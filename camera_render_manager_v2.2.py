bl_info = {
    "name": "Manga Render Manager",
    "author": "101",
    "version": (2, 2),
    "blender": (3, 6, 0),
    "location": "View3D > Sidebar > Manga Manager, or the Manga Render Manager editor",
    "description": "Manga panel camera markers, Grease Pencil details, and batch renders.",
    "category": "Render",
}

import bpy
import addon_utils
import json
import os
import re
import subprocess
import sys
import math
import tempfile
import time
import zipfile
from bpy.app.handlers import persistent
from bpy.types import Operator, Panel, UIList, PropertyGroup
from bpy.props import (
    BoolProperty,
    StringProperty,
    IntProperty,
    FloatProperty,
    EnumProperty,
    CollectionProperty,
    PointerProperty,
)
from mathutils import Matrix, Vector

# Blender frames the 3D view with a 36mm sensor fitted to the region's longer
# axis, then applies a fixed 2x zoom-out on top of it. So the view is twice as
# wide as a camera of the same focal length: a 50mm viewport sees what a 25mm
# camera sees. Both numbers are needed to convert a viewport lens to a camera.
VIEW3D_SENSOR_MM = 36.0
VIEW3D_ZOOM = 2.0

# Resolution settings copied between Camera props and Scene.render
_RES_PROPS = (
    "resolution_x",
    "resolution_y",
    "resolution_percentage",
    "pixel_aspect_x",
    "pixel_aspect_y",
)


# ---------------------------------------------------------------------------
# Module state (timers / caches — not stored on ID data)
# ---------------------------------------------------------------------------

_preview_pending = None  # (scene_name, index) or None
_preview_timer_on = False

_refresh_pending = set()  # scene as_pointer() ints
_refresh_timer_on = False

_marker_sigs = {}  # scene.as_pointer() -> signature tuple
_suppress_sync = 0  # >0 while preview mutates frame/camera

# List multi-select
_select_from_operator = False  # skip exclusive-select in index update
_selection_anchor = 0  # shift-range anchor index
_preview_done_for_index = None  # (scene_name, index) — skip duplicate timer preview
_prop_sync_depth = 0  # >0 while copying props across a multi-selection

# Active batch job runner (None when idle)
_batch = None
_batch_handlers_installed = False

# True from the moment any render starts until it finishes — ours or a plain F12.
# Blender reads scene data on another thread while this is set, so nothing here
# may touch frame, camera, resolution or selection until it clears.
_render_active = False


def render_in_progress():
    """True while a render is running, whoever started it."""
    if _render_active or _batch is not None:
        return True
    wm = getattr(bpy.context, "window_manager", None)
    return bool(wm is not None and getattr(wm, "rmcf_rendering", False))

# Objects temporarily hidden while Draw locks strokes to the camera plane
_draw_session_hidden = []


def sanitize_name(name):
    return re.sub(r'[^A-Za-z0-9_.-]+', '_', (name or "")).strip('_') or "unnamed"


def camera_object_poll(_self, obj):
    return obj is not None and obj.type == 'CAMERA'


def get_item_camera(item, scene=None):
    cam = getattr(item, "camera", None)
    if cam is not None and getattr(cam, "type", None) == 'CAMERA':
        return cam
    scene = scene or bpy.context.scene
    if scene is None:
        return None
    cam = scene.objects.get(item.camera_name)
    if cam is not None and cam.type == 'CAMERA':
        return cam
    return None


def natural_sort_key(text):
    """Alphabetical key that compares embedded numbers numerically (Cam2 < Cam10)."""
    parts = re.split(r'(\d+)', text or "")
    key = []
    for part in parts:
        if part.isdigit():
            key.append((0, int(part)))
        elif part:
            key.append((1, part.casefold()))
    return key


def iter_camera_markers(scene):
    """Return (frame, marker_name, camera_object) sorted by frame, then camera name."""
    items = []
    for marker in scene.timeline_markers:
        cam = getattr(marker, "camera", None)
        if cam is not None and cam.type == 'CAMERA':
            items.append((marker.frame, marker.name, cam))
    items.sort(key=lambda x: (x[0], natural_sort_key(x[2].name), natural_sort_key(x[1])))
    return items


def marker_signature(scene):
    return tuple(
        (frame, marker_name, cam.name_full if hasattr(cam, "name_full") else cam.name)
        for frame, marker_name, cam in iter_camera_markers(scene)
    )


def scene_by_pointer(ptr):
    for scene in bpy.data.scenes:
        if scene.as_pointer() == ptr:
            return scene
    return None


def resolve_camera(scene, camera_ptr, camera_name=""):
    """Resolve a camera by pointer, with name as a fast path."""
    if camera_name:
        cam = scene.objects.get(camera_name)
        if cam is not None and cam.type == 'CAMERA' and cam.as_pointer() == camera_ptr:
            return cam

    for obj in scene.objects:
        if obj.as_pointer() == camera_ptr and obj.type == 'CAMERA':
            return obj

    for obj in bpy.data.objects:
        if obj.as_pointer() == camera_ptr and obj.type == 'CAMERA':
            return obj

    if camera_name:
        cam = scene.objects.get(camera_name)
        if cam is not None and cam.type == 'CAMERA':
            return cam

    return None


def format_output_name(frame, camera, scene=None):
    """Build still filename. camera may be an Object or a name string."""
    if hasattr(camera, "name"):
        camera_name = camera.name
    else:
        camera_name = camera
    return f"{sanitize_name(camera_name)}_Frame_{frame:04d}"


# ---------------------------------------------------------------------------
# Manga panel helpers (naming, print size, Grease Pencil, outlines)
# ---------------------------------------------------------------------------

_GP_TYPES = {'GPENCIL', 'GREASEPENCIL'}

MANGA_RATIO_PRESETS = {
    'SQUARE': (2048, 2048),
    'PORTRAIT_3_4': (1536, 2048),
    'PORTRAIT_2_3': (1600, 2400),
    'LANDSCAPE_3_2': (2400, 1600),
    'WEBTOON': (1080, 1920),
    # 9:16 at Instagram's delivery size — also TikTok and YouTube Shorts.
    'VERTICAL_VIDEO': (1080, 1920),
}

MANGA_STATUS_ICONS = {
    'WIP': 'TIME',
    'REVIEW': 'VIEWZOOM',
    'DONE': 'CHECKMARK',
    'APPROVED': 'FUND',
}


def mm_to_px(mm, dpi):
    return max(1, int(round(float(mm) / 25.4 * float(dpi))))


def get_manga(cam_obj):
    if cam_obj is None or cam_obj.type != 'CAMERA':
        return None
    return cam_obj.data.rmcf_manga


def manga_panel_label(manga):
    page = max(0, int(manga.page_number))
    panel = (manga.panel_id or "A").strip() or "A"
    return f"P{page:02d}_{panel}"


def is_gp_object(obj):
    return obj is not None and obj.type in _GP_TYPES


def find_view3d_space(context=None):
    context = context or bpy.context
    area = find_view3d_area(context)
    if area is None:
        return None, None
    for space in area.spaces:
        if space.type == 'VIEW_3D':
            return area, space
    return area, None


def _gp_layers(gp_data):
    return getattr(gp_data, "layers", None)


def restore_draw_session_hidden():
    """Unhide meshes that were hidden for camera-plane drawing."""
    global _draw_session_hidden
    for name in _draw_session_hidden:
        obj = bpy.data.objects.get(name)
        if obj is not None:
            try:
                obj.hide_viewport = False
            except Exception:
                pass
    _draw_session_hidden.clear()


def hide_scene_geometry_for_plane_draw(context, keep_objects):
    """Hide other geometry so Surface projection can only hit the camera plane."""
    global _draw_session_hidden
    restore_draw_session_hidden()
    keep = {obj for obj in keep_objects if obj is not None}
    # Always keep grease pencil + cameras visible
    for obj in context.view_layer.objects:
        if is_gp_object(obj) or obj.type == 'CAMERA':
            keep.add(obj)

    for obj in context.view_layer.objects:
        if obj in keep:
            continue
        if obj.type not in {'MESH', 'CURVE', 'SURFACE', 'META', 'FONT'}:
            continue
        if obj.hide_viewport:
            continue
        _draw_session_hidden.append(obj.name)
        try:
            obj.hide_viewport = True
        except Exception:
            if _draw_session_hidden and _draw_session_hidden[-1] == obj.name:
                _draw_session_hidden.pop()


def apply_print_size_to_camera(cam_obj, width_mm=None, height_mm=None, dpi=None):
    manga = get_manga(cam_obj)
    res = cam_obj.data.rmcf_resolution
    if manga is None:
        return
    w = width_mm if width_mm is not None else manga.print_width_mm
    h = height_mm if height_mm is not None else manga.print_height_mm
    d = dpi if dpi is not None else manga.print_dpi
    res.use_custom_resolution = True
    res.resolution_x = mm_to_px(w, d)
    res.resolution_y = mm_to_px(h, d)
    res.resolution_percentage = 100
    manga.print_width_mm = w
    manga.print_height_mm = h
    manga.print_dpi = d


def apply_ratio_preset_to_camera(cam_obj, preset):
    size = MANGA_RATIO_PRESETS.get(preset)
    if not size:
        return False
    res = cam_obj.data.rmcf_resolution
    res.use_custom_resolution = True
    res.resolution_x, res.resolution_y = size
    res.resolution_percentage = 100
    return True


def _is_lineart_modifier(mod):
    mtype = getattr(mod, "type", "") or ""
    return mtype in {
        'GREASE_PENCIL_LINEART',
        'GP_LINEART',
        'LINEART',
    } or ('LINE' in mtype and 'ART' in mtype)


def apply_panel_outline_layers(scene, cam_obj):
    """Grease Pencil layer visibility for this panel — safe to apply any time."""
    manga = get_manga(cam_obj)
    if manga is None:
        return

    gp_obj = manga.gp_object
    if is_gp_object(gp_obj):
        layers = _gp_layers(gp_obj.data)
        if layers is not None:
            for layer in layers:
                if layer.name == "Details":
                    show = bool(manga.outline_gp_details)
                    for attr, value in (
                        ('hide', not show),
                        ('hide_viewport', not show),
                        ('hide_render', not show),
                    ):
                        if hasattr(layer, attr):
                            try:
                                setattr(layer, attr, value)
                            except Exception:
                                pass
                elif layer.name == "Erase":
                    show = bool(manga.outline_gp_erase)
                    if hasattr(layer, 'hide_render'):
                        try:
                            layer.hide_render = not show
                        except Exception:
                            pass
                    if hasattr(layer, 'hide_viewport'):
                        try:
                            layer.hide_viewport = False
                        except Exception:
                            pass

    show_lineart = bool(manga.outline_lineart)
    for obj in scene.objects:
        if not is_gp_object(obj):
            continue
        for mod in obj.modifiers:
            if _is_lineart_modifier(mod):
                mod.show_viewport = show_lineart
                mod.show_render = show_lineart


def apply_safe_area(cam_obj, enabled=True):
    data = cam_obj.data
    data.show_passepartout = True
    data.passepartout_alpha = 0.7 if enabled else 0.5
    try:
        data.show_composition_center = enabled
        data.show_composition_thirds = enabled
        data.show_composition_center_outline = enabled
    except Exception:
        pass
    try:
        data.show_safe_areas = enabled
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Per-camera resolution (same idea as Per-Camera Resolution add-on)
# ---------------------------------------------------------------------------

def copy_resolution_settings(src, dst):
    # Read every value before writing any: a write can fire an update that
    # mutates src, which would otherwise mix two sources into one copy.
    values = [(prop, getattr(src, prop)) for prop in _RES_PROPS]
    for prop, value in values:
        if getattr(dst, prop) != value:
            setattr(dst, prop, value)


def resolution_settings_match(a, b):
    return all(getattr(a, prop) == getattr(b, prop) for prop in _RES_PROPS)


def snapshot_render_resolution(scene):
    """Return a dict of the scene's current render resolution settings."""
    render = scene.render
    return {prop: getattr(render, prop) for prop in _RES_PROPS}


def restore_render_resolution(scene, snapshot):
    if not snapshot:
        return
    render = scene.render
    for prop, value in snapshot.items():
        if getattr(render, prop) != value:
            setattr(render, prop, value)


def get_use_camera_resolution(self):
    return self.get("use_custom_resolution", False)


def set_use_camera_resolution(self, value):
    """Enable/disable per-camera resolution; store or restore scene settings."""
    self["use_custom_resolution"] = value

    context = bpy.context
    scene = context.scene if context else None
    if scene is not None and scene.camera is not None and self.id_data is scene.camera.data:
        render = scene.render
        stored = scene.rmcf_resolution.stored

        settings = scene.rmcf_resolution
        if value:
            if not settings.override_applied:
                copy_resolution_settings(render, stored)
                settings.override_applied = True
            copy_resolution_settings(self, render)
        elif settings.override_applied:
            copy_resolution_settings(stored, render)
            settings.override_applied = False

        # This camera's state is now what scene.render reflects. Without this the
        # handler still thinks the last applied camera was the previous one, and
        # the next edit banks the override itself as the scene baseline.
        settings.previous_camera = scene.camera

    # Multi-select: mirror the toggle onto every selected marker camera
    propagate_group_prop(context, self, "rmcf_resolution", "use_custom_resolution", value)


def iter_selected_marker_cameras(scene):
    """Unique camera objects from selected list items (active order preserved)."""
    seen = set()
    cams = []
    for item in scene.rmcf_items:
        if not item.selected:
            continue
        cam = get_item_camera(item, scene)
        if cam is None or cam in seen:
            continue
        seen.add(cam)
        cams.append(cam)
    return cams


def count_selected_markers(scene):
    return sum(1 for item in scene.rmcf_items if item.selected)


def propagate_group_prop(context, source_pg, group_attr, prop_name, value=None):
    """Copy one property from the edited camera group to all selected marker cameras."""
    global _prop_sync_depth
    if _prop_sync_depth:
        return
    if source_pg is None:
        return

    context = context or bpy.context
    scene = getattr(context, "scene", None) if context else bpy.context.scene
    if scene is None or not hasattr(scene, "rmcf_items"):
        return

    cams = iter_selected_marker_cameras(scene)
    if len(cams) <= 1:
        return

    if value is None:
        if prop_name == "use_custom_resolution":
            value = source_pg.get("use_custom_resolution", False)
        else:
            value = getattr(source_pg, prop_name)

    _prop_sync_depth += 1
    try:
        for cam in cams:
            dst = getattr(cam.data, group_attr, None)
            if dst is None or dst == source_pg:
                continue
            if prop_name == "use_custom_resolution":
                dst["use_custom_resolution"] = bool(value)
            elif getattr(dst, prop_name) != value:
                setattr(dst, prop_name, value)
    finally:
        _prop_sync_depth -= 1

    # A propagated toggle writes the raw flag on other cameras, bypassing the
    # setter. If the active camera was one of them, scene.render is now stale.
    if group_attr == "rmcf_resolution" and prop_name == "use_custom_resolution":
        update_camera_resolution_handler(scene)


def _make_res_update(prop_name):
    def _update(self, context):
        # scene.rmcf_resolution.stored reuses this group type. Writes into it are
        # bookkeeping of the scene's own baseline, not a camera edit — reacting to
        # them re-enters the handler mid-copy and shreds the values being saved.
        if not isinstance(self.id_data, bpy.types.Camera):
            return
        propagate_group_prop(context, self, "rmcf_resolution", prop_name)
        # Keep viewport resolution matching the active camera after batch edits
        if context and context.scene:
            update_camera_resolution_handler(context.scene)
    return _update


def _make_manga_update(prop_name):
    def _update(self, context):
        propagate_group_prop(context, self, "rmcf_manga", prop_name)
    return _update


@persistent
def update_camera_resolution_handler(scene, from_render=False):
    """Apply the active camera's custom resolution (frame change / depsgraph)."""
    if scene is None:
        return

    scene_settings = getattr(scene, "rmcf_resolution", None)
    if scene_settings is None:
        return

    # During our batch stills we apply resolution explicitly per job.
    if scene_settings.is_rendering and not from_render:
        return
    if _batch is not None and not from_render:
        return
    # Any other render (F12, animation): frame_change_pre fires per frame and
    # writing render settings from it resizes the image mid-render.
    if _render_active and not from_render:
        return

    render = scene.render
    stored = scene_settings.stored

    if scene.camera is None or scene.camera.type != 'CAMERA':
        if scene_settings.override_applied:
            copy_resolution_settings(stored, render)
            scene_settings.override_applied = False
            scene_settings.previous_camera = None
        return

    cam_props = scene.camera.data.rmcf_resolution

    # Whether an override is currently applied is tracked on the scene, not
    # inferred from the previous camera's flags: those can be flipped underneath
    # us by multi-select propagation, which would strand scene.render on a stale
    # override or bank that override as the scene's baseline.
    if cam_props.use_custom_resolution:
        if not scene_settings.override_applied:
            copy_resolution_settings(render, stored)
            scene_settings.override_applied = True
        copy_resolution_settings(cam_props, render)
    elif scene_settings.override_applied:
        copy_resolution_settings(stored, render)
        scene_settings.override_applied = False

    scene_settings.previous_camera = scene.camera


def baseline_render_resolution(scene):
    """The scene's own resolution, ignoring any active camera's override.

    While an override is applied, scene.render holds that camera's values and the
    real scene resolution lives in rmcf_resolution.stored.
    """
    settings = getattr(scene, "rmcf_resolution", None)
    if settings is not None and settings.override_applied:
        return {prop: getattr(settings.stored, prop) for prop in _RES_PROPS}
    return snapshot_render_resolution(scene)


def apply_camera_resolution_for_render(scene, cam_obj, *, baseline=None):
    """Set scene.render resolution for a still from the camera (or baseline)."""
    if baseline is not None:
        restore_render_resolution(scene, baseline)

    if cam_obj is None or cam_obj.type != 'CAMERA':
        return

    props = cam_obj.data.rmcf_resolution
    if props.use_custom_resolution:
        copy_resolution_settings(props, scene.render)


# ---------------------------------------------------------------------------
# Shot serialization
# ---------------------------------------------------------------------------

SHOT_FORMAT = "manga_render_manager_shots"
SHOT_FORMAT_VERSION = 1

# Everything that decides what a shot's camera sees
_SHOT_CAMERA_PROPS = (
    "type", "lens_unit", "lens", "ortho_scale", "sensor_fit",
    "sensor_width", "sensor_height", "shift_x", "shift_y",
    "clip_start", "clip_end",
)


def serialize_property_group(group):
    """Plain-JSON dict of a PropertyGroup's own scalar values."""
    data = {}
    if group is None:
        return data
    for prop in group.bl_rna.properties:
        if prop.identifier == "rna_type" or prop.is_readonly:
            continue
        value = getattr(group, prop.identifier, None)
        if isinstance(value, (bool, int, float, str)):
            data[prop.identifier] = value
    return data


def apply_property_group(group, data, last=()):
    """Write a serialized dict back, applying `last` names after the rest.

    use_custom_resolution has a setter that pushes values onto the scene, so the
    values it pushes must already be in place when it is applied.
    """
    if group is None or not data:
        return
    deferred = [(k, v) for k, v in data.items() if k in last]
    for key, value in data.items():
        if key in last or not hasattr(group, key):
            continue
        try:
            setattr(group, key, value)
        except Exception:  # noqa: BLE001 — skip props this build doesn't accept
            pass
    for key, value in deferred:
        try:
            setattr(group, key, value)
        except Exception:  # noqa: BLE001
            pass


def shot_to_dict(scene, item):
    """One shot: where the camera is, what it sees, and how it renders."""
    cam = get_item_camera(item, scene)
    if cam is None or cam.type != 'CAMERA':
        return None
    cam_data = cam.data
    return {
        "name": cam.name,
        "marker_name": item.marker_name or cam.name,
        "frame": item.frame,
        "enabled": bool(item.enabled),
        "matrix_world": [list(row) for row in cam.matrix_world],
        "camera": {prop: getattr(cam_data, prop) for prop in _SHOT_CAMERA_PROPS},
        "resolution": serialize_property_group(getattr(cam_data, "rmcf_resolution", None)),
        "manga": serialize_property_group(getattr(cam_data, "rmcf_manga", None)),
    }


def collect_shots(scene):
    shots = []
    for item in scene.rmcf_items:
        shot = shot_to_dict(scene, item)
        if shot is not None:
            shots.append(shot)
    return shots


def refresh_evaluated_transforms():
    """matrix_world is evaluated data: without this, cameras moved since the last
    depsgraph update serialize at their old (often identity) placement."""
    try:
        bpy.context.view_layer.update()
    except (AttributeError, RuntimeError):  # no view layer (background helpers)
        pass


def apply_shot(scene, shot, collection, reuse_existing=True):
    """Create or update one camera + marker from a shot dict."""
    name = shot.get("name") or "Camera"
    frame = int(shot.get("frame", scene.frame_current))

    cam = None
    if reuse_existing:
        existing = bpy.data.objects.get(name)
        if existing is not None and existing.type == 'CAMERA':
            cam = existing
    if cam is None:
        cam = bpy.data.objects.new(name, bpy.data.cameras.new(name))
    if cam.name not in scene.objects:
        collection.objects.link(cam)

    matrix = shot.get("matrix_world")
    if matrix:
        cam.matrix_world = Matrix([list(row) for row in matrix])

    cam_data = cam.data
    for prop, value in (shot.get("camera") or {}).items():
        if prop in _SHOT_CAMERA_PROPS:
            try:
                setattr(cam_data, prop, value)
            except Exception:  # noqa: BLE001 — skip values this build rejects
                pass

    apply_property_group(getattr(cam_data, "rmcf_resolution", None),
                         shot.get("resolution"), last=("use_custom_resolution",))
    apply_property_group(getattr(cam_data, "rmcf_manga", None), shot.get("manga"))

    marker = next((m for m in scene.timeline_markers if m.camera == cam), None)
    if marker is None:
        # Name the marker after the camera actually created — restoring beside an
        # existing shot renames the camera, and the marker must not disagree.
        marker = scene.timeline_markers.new(name=cam.name, frame=frame)
        marker.camera = cam
    else:
        marker.frame = frame
    return cam, frame


# ---------------------------------------------------------------------------
# Shot list stored inside the .blend
#
# The cameras, markers and per-camera settings already live in the .blend, so a
# file opened elsewhere normally rebuilds its own shot list. The embedded copy
# is the safety net for everything that can go missing on the way — a camera
# unlinked from the scene, a marker that lost its binding, settings written by
# a different add-on version. It is refreshed on every save and replayed on
# every load, so handing someone the .blend is all it takes.
# ---------------------------------------------------------------------------

SHOT_TEXT_NAME = ".rmcf_shots"


def embedded_shot_text(create=False):
    """The internal text datablock holding the shot snapshot."""
    text = bpy.data.texts.get(SHOT_TEXT_NAME)
    if text is None and create:
        text = bpy.data.texts.new(SHOT_TEXT_NAME)
    if text is not None:
        # Nothing in the file points at this text, so without a fake user it is
        # dropped the next time the file is saved.
        text.use_fake_user = True
    return text


def write_embedded_shots(scenes=None):
    """Write every scene's shot list into the .blend. Returns the shot count."""
    scenes = list(bpy.data.scenes) if scenes is None else list(scenes)
    refresh_evaluated_transforms()

    entries = []
    total = 0
    for scene in scenes:
        shots = collect_shots(scene)
        total += len(shots)
        entries.append({"scene": scene.name, "shots": shots})

    payload = {
        "format": SHOT_FORMAT,
        "format_version": SHOT_FORMAT_VERSION,
        "addon_version": list(bl_info["version"]),
        "scenes": entries,
    }
    text = embedded_shot_text(create=True)
    text.clear()
    text.write(json.dumps(payload, indent=2))
    return total


def read_embedded_shots():
    """{scene_name: [shot, ...]} from the .blend, or {} if there is nothing usable."""
    text = bpy.data.texts.get(SHOT_TEXT_NAME)
    if text is None:
        return {}
    try:
        payload = json.loads(text.as_string())
    except (ValueError, AttributeError):
        return {}
    if not isinstance(payload, dict) or payload.get("format") != SHOT_FORMAT:
        return {}
    if payload.get("format_version", 0) > SHOT_FORMAT_VERSION:
        return {}
    result = {}
    for entry in payload.get("scenes") or ():
        if isinstance(entry, dict) and isinstance(entry.get("shots"), list):
            result[entry.get("scene") or ""] = entry["shots"]
    return result


def shot_is_live(scene, shot):
    """True if this shot's camera is already bound to a marker in the scene."""
    name = shot.get("name")
    cam = bpy.data.objects.get(name) if name else None
    if cam is None or cam.type != 'CAMERA' or cam.name not in scene.objects:
        return False
    return any(m.camera == cam for m in scene.timeline_markers)


def restore_embedded_shots(scene, shots=None, context=None):
    """Rebuild shots the scene is missing from the embedded snapshot.

    Purely additive: shots whose camera is already bound to a marker are left
    exactly as the file has them, so this never undoes local edits.
    """
    if shots is None:
        shots = read_embedded_shots().get(scene.name)
        if shots is None:
            # Scene renamed (or renamed on the way over): fall back to the only
            # entry when the file has just one, which is the common case.
            entries = read_embedded_shots()
            shots = next(iter(entries.values())) if len(entries) == 1 else None
    if not shots:
        return 0

    context = context or bpy.context
    collection = getattr(context, "collection", None) or scene.collection

    restored = []
    for shot in shots:
        if not isinstance(shot, dict) or shot_is_live(scene, shot):
            continue
        cam, frame = apply_shot(scene, shot, collection, reuse_existing=True)
        restored.append((cam, frame, bool(shot.get("enabled", True))))

    if not restored:
        return 0

    sync_marker_list(scene, force=True)
    wanted = {(cam.name, frame): enabled for cam, frame, enabled in restored}
    for item in scene.rmcf_items:
        cam = get_item_camera(item, scene)
        if cam is None:
            continue
        enabled = wanted.get((cam.name, item.frame))
        if enabled is not None:
            item.enabled = enabled
    return len(restored)



def blend_directory():
    blend = bpy.data.filepath
    if not blend:
        return ""
    return os.path.dirname(bpy.path.abspath(blend))


def resolve_output_dir(filepath):
    path = (filepath or "").strip()
    if not path:
        blend_dir = blend_directory()
        return blend_dir or os.path.expanduser("~/Renders")

    if path.startswith("//"):
        abs_path = bpy.path.abspath(path)
    elif os.path.isabs(path):
        abs_path = os.path.normpath(path)
    else:
        blend_dir = blend_directory()
        if blend_dir:
            abs_path = os.path.normpath(os.path.join(blend_dir, path))
        else:
            raise ValueError(
                "Render output is a relative path, but this .blend is unsaved. "
                "Save the file, or set an absolute output folder."
            )

    if path.endswith(("/", "\\")) or abs_path.endswith(("/", "\\")):
        return abs_path.rstrip("/\\") or abs_path

    if os.path.isdir(abs_path):
        return abs_path

    parent = os.path.dirname(abs_path)
    return parent if parent else abs_path


def get_blender_output_dir(scene):
    return resolve_output_dir(scene.render.filepath)


_CUSTOM_OUTPUT_KEY = "rmcf_output_dir_value"


def has_custom_output(scene):
    return bool(scene.get(_CUSTOM_OUTPUT_KEY, ""))


def get_rmcf_output_dir(self):
    """Show custom folder, or Blender Output when none is set."""
    custom = self.get(_CUSTOM_OUTPUT_KEY, "")
    if custom:
        return custom
    try:
        return get_blender_output_dir(self)
    except ValueError:
        return ""


def set_rmcf_output_dir(self, value):
    value = (value or "").strip()
    if not value:
        if _CUSTOM_OUTPUT_KEY in self:
            del self[_CUSTOM_OUTPUT_KEY]
        return
    self[_CUSTOM_OUTPUT_KEY] = value


def get_render_base_dir(scene):
    custom = scene.get(_CUSTOM_OUTPUT_KEY, "")
    if custom:
        return resolve_output_dir(custom)
    return get_blender_output_dir(scene)


def open_folder(path):
    path = os.path.normpath(path)
    if not os.path.isdir(path):
        os.makedirs(path, exist_ok=True)
    if sys.platform == "darwin":
        subprocess.Popen(["open", path])
    elif sys.platform == "win32":
        os.startfile(path)  # noqa: B606 — intentional folder open
    else:
        subprocess.Popen(["xdg-open", path])


def find_view3d_area(context):
    """Pick a View3D area for camera-view preview."""
    area = context.area if context.area and context.area.type == 'VIEW_3D' else None

    if area is None and context.screen is not None:
        for candidate in context.screen.areas:
            if candidate.type == 'VIEW_3D':
                return candidate

    if area is None:
        for win in context.window_manager.windows:
            for candidate in win.screen.areas:
                if candidate.type == 'VIEW_3D':
                    return candidate

    return area


def find_view3d_space(context):
    """Return (space, window_region) for the View3D used for previews."""
    area = find_view3d_area(context)
    if area is None:
        return None, None
    for space in area.spaces:
        if space.type == 'VIEW_3D' and space.region_3d is not None:
            region = next((r for r in area.regions if r.type == 'WINDOW'), None)
            return space, region
    return None, None


def view3d_is_camera_view(context):
    """True if the 3D view is currently looking through a camera."""
    space, _region = find_view3d_space(context)
    return space is not None and space.region_3d.view_perspective == 'CAMERA'


def view3d_view_matrix(context):
    """Return the active View3D view matrix, or None."""
    space, _region = find_view3d_space(context)
    if space is None:
        return None
    return space.region_3d.view_matrix.copy()


def region_aspect(region):
    """Width / height of the 3D view region."""
    if region is None or not region.width or not region.height:
        return 16.0 / 9.0
    return region.width / region.height


def camera_frame_aspect(cam_data, scene):
    """Pixel aspect of the frame this camera renders (custom resolution or scene)."""
    props = getattr(cam_data, "rmcf_resolution", None)
    source = props if props is not None and props.use_custom_resolution else scene.render
    width = source.resolution_x * source.pixel_aspect_x
    height = source.resolution_y * source.pixel_aspect_y
    if width <= 0 or height <= 0:
        return 16.0 / 9.0
    return width / height


def apply_view_optics_to_camera(cam_obj, context):
    """Match a new camera's lens to the 3D view, so its framing matches the view.

    Blender fits the camera frame inside the region on whichever axis is the
    tighter one, so the field of view is matched on that same axis — that is the
    axis whose scale must not change when the view becomes the camera.
    Returns the distance the camera must be pulled back along its local +Z.
    """
    space, region = find_view3d_space(context)
    if space is None:
        return 0.0

    cam_data = cam_obj.data
    rv3d = space.region_3d
    scene = context.scene

    # Looking through a camera already — copy that camera's optics verbatim.
    if rv3d.view_perspective == 'CAMERA':
        src = scene.camera
        if src is not None and src.type == 'CAMERA':
            src_data = src.data
            for prop in ("type", "lens_unit", "lens", "ortho_scale", "sensor_fit",
                         "sensor_width", "sensor_height", "shift_x", "shift_y",
                         "clip_start", "clip_end"):
                setattr(cam_data, prop, getattr(src_data, prop))
            return 0.0

    apply_view_lens_to_camera(cam_data, space, region, scene)

    # Never clip closer/nearer than the view the user is looking at.
    cam_data.clip_start = min(cam_data.clip_start, max(space.clip_start, 1e-5))
    cam_data.clip_end = max(cam_data.clip_end, space.clip_end)

    if rv3d.view_perspective == 'ORTHO':
        dist = max(rv3d.view_distance, 1e-4)
        cam_data.type = 'ORTHO'
        cam_data.ortho_scale = dist * VIEW3D_SENSOR_MM / cam_data.lens
        # An ortho viewport also draws what sits behind the eye; a camera cannot,
        # so pull it back and open the far clip to keep that geometry visible.
        cam_data.clip_end = max(cam_data.clip_end, dist * 2.0 + space.clip_end * 0.5)
        return dist

    cam_data.type = 'PERSP'
    return 0.0


def apply_view_lens_to_camera(cam_data, space, region, scene):
    """Give the camera the focal length that frames what the 3D view frames.

    Blender fits the camera frame inside the region on whichever axis is the
    tighter one, so the field of view is matched on that axis. Returns the lens.
    """
    aspect = region_aspect(region)
    if camera_frame_aspect(cam_data, scene) >= aspect:
        # Frame is wider than the region, so it fills the region's width.
        fit, axis_fraction = 'HORIZONTAL', min(1.0, aspect)
    else:
        fit, axis_fraction = 'VERTICAL', min(1.0, 1.0 / aspect)

    # Keep the standard 36mm sensor and express the viewport's field of view as
    # a real focal length, rather than inventing an odd sensor size.
    cam_data.sensor_fit = fit
    cam_data.sensor_width = VIEW3D_SENSOR_MM
    cam_data.sensor_height = VIEW3D_SENSOR_MM
    cam_data.lens_unit = 'MILLIMETERS'
    cam_data.lens = max(space.lens / (VIEW3D_ZOOM * axis_fraction), 1.0)
    cam_data.shift_x = 0.0
    cam_data.shift_y = 0.0
    return cam_data.lens


def next_camera_base_name(scene):
    """Prefer Camera, Camera.001, … matching existing scene cameras."""
    existing = {obj.name for obj in scene.objects if obj.type == 'CAMERA'}
    if "Camera" not in existing:
        return "Camera"
    i = 1
    while True:
        name = f"Camera.{i:03d}"
        if name not in existing:
            return name
        i += 1


def next_free_marker_frame(scene, frame):
    """First frame at or after `frame` that has no timeline marker on it."""
    used = {m.frame for m in scene.timeline_markers}
    while frame in used:
        frame += 1
    return frame


def create_marker_camera(context):
    """Create a camera at the current view (or scene camera) and bind a marker.

    The marker lands on the current frame when that frame is free, otherwise on
    the first later frame without a marker, so shots never stack on top of each
    other. The scene is left on whichever frame was used.

    Returns (camera_object, marker).
    """
    scene = context.scene
    frame = next_free_marker_frame(scene, scene.frame_current)
    cam_name = next_camera_base_name(scene)

    cam_data = bpy.data.cameras.new(cam_name)
    cam_obj = bpy.data.objects.new(cam_data.name, cam_data)

    collection = context.collection if context.collection else scene.collection
    collection.objects.link(cam_obj)

    view_matrix = view3d_view_matrix(context)
    if view_matrix is not None:
        cam_obj.matrix_world = view_matrix.inverted()
    elif scene.camera is not None:
        cam_obj.matrix_world = scene.camera.matrix_world.copy()

    pull_back = apply_view_optics_to_camera(cam_obj, context)
    if pull_back:
        cam_obj.matrix_world = cam_obj.matrix_world @ Matrix.Translation((0.0, 0.0, pull_back))

    marker = scene.timeline_markers.new(name=cam_obj.name, frame=frame)
    marker.camera = cam_obj

    scene.camera = cam_obj
    scene.frame_set(frame)
    return cam_obj, marker


def tag_view3d_redraw():
    wm = bpy.context.window_manager
    if wm is None:
        return
    for window in wm.windows:
        for area in window.screen.areas:
            if area.type == 'VIEW_3D':
                area.tag_redraw()


# ---------------------------------------------------------------------------
# List sync (Refresh / deferred panel / pre-render — never write from draw())
# ---------------------------------------------------------------------------

def marker_list_outdated(scene):
    """Read-only check: True if rmcf_items may need a rebuild."""
    if scene is None:
        return False
    try:
        sig = marker_signature(scene)
        ptr = scene.as_pointer()
        return _marker_sigs.get(ptr) != sig or len(scene.rmcf_items) != len(sig)
    except Exception:  # noqa: BLE001 — draw-safe; treat as no update needed
        return False


def sync_marker_list(scene, force=False):
    """Update rmcf_items from timeline markers; preserve enabled flags.

    Must not be called from Panel.draw / UIList.draw_item — Blender forbids
    writing ID data in those contexts.
    """
    global _preview_done_for_index
    if scene is None or _suppress_sync:
        return False

    markers = iter_camera_markers(scene)
    sig = tuple(
        (frame, marker_name, cam.name_full if hasattr(cam, "name_full") else cam.name)
        for frame, marker_name, cam in markers
    )
    ptr = scene.as_pointer()

    if not force and _marker_sigs.get(ptr) == sig and len(scene.rmcf_items) == len(sig):
        return False

    enabled_map = {}
    selected_map = {}
    for item in scene.rmcf_items:
        cam = get_item_camera(item, scene)
        key = (item.frame, cam.name if cam else item.camera_name)
        enabled_map[key] = item.enabled
        selected_map[key] = item.selected

    if len(scene.rmcf_items) == len(markers):
        for i, (frame, marker_name, cam) in enumerate(markers):
            item = scene.rmcf_items[i]
            item.frame = frame
            item.marker_name = marker_name
            item.camera = cam
            item.camera_name = cam.name
            key = (frame, cam.name)
            item.enabled = enabled_map.get(key, item.enabled)
            item.selected = selected_map.get(key, item.selected)
    else:
        scene.rmcf_items.clear()
        for frame, marker_name, cam in markers:
            item = scene.rmcf_items.add()
            item.frame = frame
            item.marker_name = marker_name
            item.camera = cam
            item.camera_name = cam.name
            key = (frame, cam.name)
            item.enabled = enabled_map.get(key, True)
            item.selected = selected_map.get(key, False)

    # Clamp the row selection to the rebuilt list. Assign only when the value
    # really changes: RNA runs the update callback on same-value writes too,
    # which would enqueue a preview and yank the frame on every save/load.
    clamped = min(scene.rmcf_index, max(len(scene.rmcf_items) - 1, 0))
    if clamped != scene.rmcf_index:
        # A sync must not count as clicking the row — mark it as already
        # previewed so the pending timer skips it (same trick
        # sync_list_to_camera_view uses).
        _preview_done_for_index = (scene.name, clamped)
        scene.rmcf_index = clamped
    _marker_sigs[ptr] = sig
    return True


def index_of_camera_item(scene, cam):
    """List row bound to this camera object, or -1."""
    if cam is None:
        return -1
    for i, item in enumerate(scene.rmcf_items):
        if get_item_camera(item, scene) == cam:
            return i
    return -1


def camera_view_selection_outdated(scene, context=None):
    """Read-only check: is the list pointing somewhere other than the camera
    the viewport is looking through? Safe to call from draw()."""
    if scene is None or _suppress_sync:
        return False
    context = context or bpy.context
    wm = getattr(context, "window_manager", None)
    if wm is not None and getattr(wm, "rmcf_rendering", False):
        return False
    if render_in_progress():
        return False
    try:
        if not view3d_is_camera_view(context):
            return False
        idx = index_of_camera_item(scene, scene.camera)
    except Exception:  # noqa: BLE001 — draw-safe; treat as up to date
        return False
    if idx < 0:
        return False
    return scene.rmcf_index != idx or not scene.rmcf_items[idx].selected


def sync_list_to_camera_view(scene, context=None):
    """Point the list at the camera the viewport is looking through.

    Stops resolution and manga edits from landing on whatever row happened to
    be active while you are framed up in a different camera.
    """
    global _select_from_operator, _preview_done_for_index

    context = context or bpy.context
    if not camera_view_selection_outdated(scene, context):
        return False

    idx = index_of_camera_item(scene, scene.camera)
    if idx < 0:
        return False

    _select_from_operator = True
    try:
        # A deliberate multi-selection that already covers this camera is left
        # alone — only the active row moves. Otherwise the viewed camera
        # becomes the selection, so bulk edits cannot reach anything else.
        if not scene.rmcf_items[idx].selected:
            exclusive_select_list_item(scene, idx)
        scene.rmcf_index = idx
    finally:
        _select_from_operator = False

    # The viewport is already looking through this camera; a preview would only
    # yank the frame to the marker, so mark it as handled.
    _preview_done_for_index = (scene.name, idx)
    apply_list_selection_to_objects(scene, context)
    return True


def _run_refresh_timer():
    global _refresh_timer_on, _refresh_pending
    _refresh_timer_on = False
    pending = set(_refresh_pending)
    _refresh_pending.clear()
    for ptr in pending:
        scene = scene_by_pointer(ptr)
        if scene is not None:
            sync_marker_list(scene)
            sync_list_to_camera_view(scene)
    tag_view3d_redraw()
    return None


def schedule_marker_refresh(scene):
    """Queue a sync on a timer (safe to call from Panel.draw)."""
    global _refresh_timer_on
    if scene is None or _suppress_sync:
        return
    wm = bpy.context.window_manager
    if wm is not None and getattr(wm, "rmcf_rendering", False):
        return
    if not marker_list_outdated(scene) and not camera_view_selection_outdated(scene):
        return
    _refresh_pending.add(scene.as_pointer())
    if not _refresh_timer_on:
        _refresh_timer_on = True
        bpy.app.timers.register(_run_refresh_timer, first_interval=0.05)


# ---------------------------------------------------------------------------
# Preview / list selection
# ---------------------------------------------------------------------------

def fit_camera_frame_to_region(context, area, space):
    """Zoom/pan the camera view so the frame fills the region.

    Entering camera view otherwise keeps whatever zoom and offset the viewport
    was left with by an earlier preview, which reads as a jump.
    """
    region = next((r for r in area.regions if r.type == 'WINDOW'), None)
    if region is None:
        return
    try:
        with context.temp_override(area=area, region=region, space_data=space):
            bpy.ops.view3d.view_center_camera()
    except Exception:  # noqa: BLE001 — framing is cosmetic; never block the add
        pass


def ensure_camera_view(context=None, fit_frame=False):
    """Switch the active (or first) View3D to camera perspective if needed."""
    context = context or bpy.context
    area = find_view3d_area(context)
    if area is None:
        return

    for space in area.spaces:
        if space.type != 'VIEW_3D':
            continue
        rv3d = space.region_3d
        if rv3d is not None and rv3d.view_perspective != 'CAMERA':
            rv3d.view_perspective = 'CAMERA'
        if fit_frame:
            fit_camera_frame_to_region(context, area, space)
        break


_EDIT_PLATE_TAG = "rmcf_edit_plate"


def get_edit_plate_dir(scene):
    """Folder for edit-plate stills (beside the .blend, or temp)."""
    if bpy.data.filepath:
        path = bpy.path.abspath("//rmcf_edit_plates/")
        try:
            os.makedirs(path, exist_ok=True)
            return path
        except OSError:
            pass
    path = os.path.join(tempfile.gettempdir(), "rmcf_edit_plates")
    os.makedirs(path, exist_ok=True)
    return path


def find_camera_edit_plate_slot(cam_data):
    for bg in cam_data.background_images:
        img = bg.image
        if img is not None and img.get(_EDIT_PLATE_TAG):
            return bg
    return None


def set_camera_edit_plate(cam_obj, image, *, alpha=1.0):
    """Show image as a camera background matched to the view frame."""
    if cam_obj is None or cam_obj.type != 'CAMERA' or image is None:
        return None

    cam_data = cam_obj.data
    cam_data.show_background_images = True

    bg = find_camera_edit_plate_slot(cam_data)
    if bg is None:
        bg = cam_data.background_images.new()

    bg.image = image
    try:
        bg.image_user.use_auto_refresh = True
    except Exception:
        pass
    bg.alpha = float(alpha)
    bg.show_background_image = True
    try:
        bg.display_depth = 'BACK'
    except Exception:
        pass
    try:
        # Rendered at this camera's resolution — fill the frame exactly
        bg.frame_method = 'STRETCH'
    except Exception:
        pass
    try:
        bg.source = 'IMAGE'
    except Exception:
        pass

    image[_EDIT_PLATE_TAG] = True
    return bg


def clear_camera_edit_plate(cam_obj):
    """Remove the Render Manager edit-plate background from a camera."""
    if cam_obj is None or cam_obj.type != 'CAMERA':
        return False
    cam_data = cam_obj.data
    removed = False
    # Collect then remove — background_images.remove needs the element
    to_remove = []
    for bg in cam_data.background_images:
        img = bg.image
        if img is not None and img.get(_EDIT_PLATE_TAG):
            to_remove.append(bg)
    for bg in to_remove:
        img = bg.image
        try:
            cam_data.background_images.remove(bg)
            removed = True
        except Exception:
            try:
                bg.image = None
                bg.show_background_image = False
                removed = True
            except Exception:
                pass
        if img is not None and img.users == 0:
            try:
                bpy.data.images.remove(img)
            except Exception:
                pass
    if removed and len(cam_data.background_images) == 0:
        cam_data.show_background_images = False
    return removed


def render_edit_plate(context, cam_obj):
    """Render a plate for this camera and return the loaded Image."""
    scene = context.scene
    manga = get_manga(cam_obj)
    if manga is None:
        return None, "No manga props on camera"

    if getattr(context.window_manager, "rmcf_rendering", False):
        return None, "A batch render is already running"

    # Jump to this camera / frame via list item if possible
    items = scene.rmcf_items
    idx = scene.rmcf_index
    if 0 <= idx < len(items):
        item_cam = get_item_camera(items[idx], scene)
        if item_cam == cam_obj:
            preview_marker_item(scene, items[idx], context)

    scene.camera = cam_obj
    ensure_camera_view(context)

    apply_panel_outline_layers(scene, cam_obj)

    # Don't bake live GP details into the plate — draw those on top afterward
    gp_obj = manga.gp_object if is_gp_object(manga.gp_object) else None
    gp_hide = None
    if gp_obj is not None:
        gp_hide = gp_obj.hide_render
        gp_obj.hide_render = True

    plane = manga.draw_plane
    plane_hide = None
    if plane is not None:
        plane_hide = plane.hide_render
        plane.hide_render = True

    orig_filepath = scene.render.filepath
    orig_overwrite = scene.render.use_overwrite
    orig_res = snapshot_render_resolution(scene)
    was_rendering_flag = False
    if hasattr(scene, "rmcf_resolution"):
        was_rendering_flag = scene.rmcf_resolution.is_rendering
        scene.rmcf_resolution.is_rendering = True

    plate_dir = get_edit_plate_dir(scene)
    plate_path = os.path.join(
        plate_dir,
        f"{sanitize_name(cam_obj.name)}_edit_plate.png",
    )
    # Blender filepath without extension — it adds the file format suffix
    plate_base, _ = os.path.splitext(plate_path)
    scene.render.filepath = plate_base
    scene.render.use_overwrite = True
    apply_camera_resolution_for_render(scene, cam_obj)

    # Prefer PNG for the plate
    orig_format = scene.render.image_settings.file_format
    try:
        scene.render.image_settings.file_format = 'PNG'
    except Exception:
        pass

    try:
        result = bpy.ops.render.render(write_still=True, use_viewport=False)
        if 'CANCELLED' in result:
            return None, "Render was cancelled"
    except Exception as exc:
        return None, str(exc)
    finally:
        scene.render.filepath = orig_filepath
        scene.render.use_overwrite = orig_overwrite
        restore_render_resolution(scene, orig_res)
        try:
            scene.render.image_settings.file_format = orig_format
        except Exception:
            pass
        if hasattr(scene, "rmcf_resolution"):
            scene.rmcf_resolution.is_rendering = was_rendering_flag
            update_camera_resolution_handler(scene, from_render=True)
        if gp_obj is not None and gp_hide is not None:
            gp_obj.hide_render = gp_hide
        if plane is not None and plane_hide is not None:
            plane.hide_render = plane_hide

    # Resolve actual written file (format may append .png)
    written = plate_path
    if not os.path.isfile(written):
        for ext in (".png", ".jpg", ".jpeg", ".tif", ".tiff", ".exr"):
            candidate = plate_base + ext
            if os.path.isfile(candidate):
                written = candidate
                break
    if not os.path.isfile(written):
        return None, f"Render finished but file not found ({plate_path})"

    # Reload so a re-render refreshes the same image block
    image = None
    for img in bpy.data.images:
        if img.get(_EDIT_PLATE_TAG) and bpy.path.abspath(img.filepath) == bpy.path.abspath(written):
            image = img
            break
    if image is None:
        image = bpy.data.images.load(written, check_existing=True)
    else:
        try:
            image.reload()
        except Exception:
            pass
    image[_EDIT_PLATE_TAG] = True
    try:
        image.name = f"{sanitize_name(cam_obj.name)}_EditPlate"
    except Exception:
        pass

    set_camera_edit_plate(cam_obj, image, alpha=1.0)
    return image, None


def exclusive_select_list_item(scene, index):
    """Select only the item at index in the marker list (minimal RNA writes)."""
    global _selection_anchor
    for i, item in enumerate(scene.rmcf_items):
        want = (i == index)
        if item.selected != want:
            item.selected = want
    _selection_anchor = index


def in_object_mode(context):
    """False while the user is posing, sculpting, editing or painting."""
    mode = getattr(context, "mode", 'OBJECT')
    if mode and mode != 'OBJECT':
        return False
    obj = getattr(context, "object", None)
    return obj is None or obj.mode == 'OBJECT'


def apply_list_selection_to_objects(scene, context, active_index=None):
    """Select camera objects for selected list items; active = active_index camera."""
    view_layer = context.view_layer
    if view_layer is None:
        return

    # Making a camera the active object drops the user out of Pose Mode (or Edit,
    # Sculpt, Paint) and loses what they had selected there. Previewing a panel is
    # not worth that, so outside Object Mode the selection is left alone.
    if not in_object_mode(context):
        return

    if active_index is None:
        active_index = scene.rmcf_index

    wanted = []
    active_cam = None
    for i, item in enumerate(scene.rmcf_items):
        if not item.selected:
            continue
        cam = get_item_camera(item, scene)
        if cam is None:
            continue
        wanted.append(cam)
        if i == active_index:
            active_cam = cam

    if active_cam is None and wanted:
        active_cam = wanted[0]

    wanted_set = set(wanted)

    # Fast path: single camera exclusive select — only touch prev active + new
    if len(wanted) <= 1 and active_cam is not None:
        prev = view_layer.objects.active
        if prev is not None and prev != active_cam and prev.select_get():
            prev.select_set(False)
        for obj in context.selected_objects:
            if obj != active_cam:
                obj.select_set(False)
        if not active_cam.select_get():
            active_cam.select_set(True)
        if view_layer.objects.active != active_cam:
            view_layer.objects.active = active_cam
        return

    for obj in list(context.selected_objects):
        if obj not in wanted_set:
            obj.select_set(False)

    for cam in wanted:
        if not cam.select_get():
            cam.select_set(True)

    if active_cam is not None and view_layer.objects.active != active_cam:
        view_layer.objects.active = active_cam


def preview_marker_item(scene, item, context=None, *, sync_objects=True):
    """Jump to the marker frame and set scene camera; optionally sync object selection."""
    global _suppress_sync

    if item is None:
        return

    # Jumping the frame or swapping the camera mid-render corrupts the depsgraph
    # the render is reading — the classic "crashed while rendering" report.
    if render_in_progress():
        return

    context = context or bpy.context
    cam = get_item_camera(item, scene)
    if cam is None:
        return

    _suppress_sync += 1
    try:
        # Skip depsgraph-heavy writes when already on the target
        if scene.frame_current != item.frame:
            scene.frame_set(item.frame)
        if scene.camera != cam:
            scene.camera = cam
        if sync_objects:
            apply_list_selection_to_objects(scene, context)
        ensure_camera_view(context)
        # Keep scene render resolution in sync with the previewed camera
        update_camera_resolution_handler(scene)
    finally:
        _suppress_sync -= 1


def _run_preview_timer():
    global _preview_timer_on, _preview_pending, _preview_done_for_index
    _preview_timer_on = False
    pending = _preview_pending
    _preview_pending = None
    if pending is None:
        return None

    # Hold the preview until the render finishes rather than dropping it.
    if render_in_progress():
        _preview_pending = pending
        _preview_timer_on = True
        return 0.5

    scene_name, index, _manage_selection = pending
    # Operator path already previewed this index — skip the duplicate
    if _preview_done_for_index == (scene_name, index):
        _preview_done_for_index = None
        return None
    _preview_done_for_index = None

    scene = bpy.data.scenes.get(scene_name)
    if scene is None:
        return None
    if 0 <= index < len(scene.rmcf_items):
        # Index-only clicks (checkbox / list chrome) must NOT wipe multi-select.
        # Selection is owned by rmcf.select_list_item / list_navigate.
        preview_marker_item(scene, scene.rmcf_items[index], bpy.context)
    return None


def on_rmcf_index_update(self, context):
    """Debounced preview: coalesce rapid list clicks into one update."""
    global _preview_pending, _preview_timer_on
    # Never exclusive-select from index updates — preserves Shift/Ctrl multi-select
    _preview_pending = (self.name, self.rmcf_index, False)
    if not _preview_timer_on:
        _preview_timer_on = True
        bpy.app.timers.register(_run_preview_timer, first_interval=0.02)


# ---------------------------------------------------------------------------
# Batch render job runner (native INVOKE_DEFAULT + handlers)
# ---------------------------------------------------------------------------

def collect_render_queue(scene):
    queue = []
    for item in scene.rmcf_items:
        if not item.enabled:
            continue
        cam = get_item_camera(item, scene)
        if cam is None:
            continue
        queue.append({
            "frame": item.frame,
            "camera_ptr": cam.as_pointer(),
            "camera_name": cam.name,
        })
    return queue


def count_render_markers(scene):
    """How many enabled list items would be rendered."""
    return len(collect_render_queue(scene))


def _install_batch_handlers():
    global _batch_handlers_installed
    if _batch_handlers_installed:
        return
    if _on_render_complete not in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.append(_on_render_complete)
    if _on_render_cancel not in bpy.app.handlers.render_cancel:
        bpy.app.handlers.render_cancel.append(_on_render_cancel)
    _batch_handlers_installed = True


def _remove_batch_handlers():
    global _batch_handlers_installed
    if _on_render_complete in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.remove(_on_render_complete)
    if _on_render_cancel in bpy.app.handlers.render_cancel:
        bpy.app.handlers.render_cancel.remove(_on_render_cancel)
    _batch_handlers_installed = False


def _set_wm_rendering(active, progress=""):
    wm = bpy.context.window_manager
    if wm is None:
        return
    try:
        wm.rmcf_rendering = active
        wm.rmcf_progress = progress
    except Exception:  # noqa: BLE001 — props may be gone during unregister
        pass
    tag_view3d_redraw()


def _batch_scene(batch):
    return scene_by_pointer(batch["scene_ptr"])


def _snapshot_user_view(batch, scene):
    """Remember the user's current frame/camera so we can restore between jobs."""
    cam = scene.camera
    batch["user_frame"] = scene.frame_current
    batch["user_camera_ptr"] = cam.as_pointer() if cam else 0
    batch["user_camera_name"] = cam.name if cam else ""


def _restore_user_view(batch):
    """Put the viewport back so the user can keep editing during the batch."""
    scene = _batch_scene(batch)
    if scene is None:
        return

    scene.frame_set(batch.get("user_frame", batch["orig_frame"]))
    cam_ptr = batch.get("user_camera_ptr", 0)
    cam_name = batch.get("user_camera_name", "")
    if cam_ptr:
        scene.camera = resolve_camera(scene, cam_ptr, cam_name)
    else:
        scene.camera = None


def _restore_batch_scene_state(batch):
    scene = _batch_scene(batch)
    if scene is None:
        return

    scene.frame_set(batch["orig_frame"])

    cam_ptr = batch.get("orig_camera_ptr", 0)
    cam_name = batch.get("orig_camera_name", "")
    if cam_ptr:
        scene.camera = resolve_camera(scene, cam_ptr, cam_name)
    else:
        scene.camera = None

    scene.render.filepath = batch["orig_filepath"]
    scene.render.use_overwrite = batch["orig_overwrite"]
    scene.render.use_placeholder = batch["orig_placeholders"]
    if "orig_lock_interface" in batch:
        scene.render.use_lock_interface = batch["orig_lock_interface"]
    restore_render_resolution(scene, batch.get("orig_resolution"))
    if hasattr(scene, "rmcf_resolution"):
        scene.rmcf_resolution.is_rendering = False
        update_camera_resolution_handler(scene, from_render=True)


def _finish_batch(*, cancelled=False, error=None):
    """Restore scene state, clear flags, and drop handlers."""
    global _batch

    batch = _batch
    _batch = None

    if bpy.app.timers.is_registered(_kick_next_render):
        bpy.app.timers.unregister(_kick_next_render)

    _remove_batch_handlers()

    if batch is not None:
        _restore_batch_scene_state(batch)
        base_dir = batch["base_dir"]
        rendered = batch["rendered"]
        total = batch["total"]
        if error:
            print(f"RMCF: Render failed after {rendered} / {total}: {error}")
        elif cancelled:
            print(f"RMCF: Cancelled after {rendered} / {total} → {base_dir}")
        else:
            print(f"RMCF: Rendered {rendered} frame(s) → {base_dir}")

    _set_wm_rendering(False, "")


def _kick_next_render():
    """Start the next still via INVOKE_DEFAULT (must not nest inside a handler)."""
    global _batch

    batch = _batch
    if batch is None:
        return None

    scene = _batch_scene(batch)
    if scene is None:
        _finish_batch(cancelled=True, error="Scene was removed during batch render")
        return None

    if batch["index"] >= batch["total"]:
        _finish_batch(cancelled=False)
        return None

    job = batch["queue"][batch["index"]]
    cam = resolve_camera(scene, job["camera_ptr"], job.get("camera_name", ""))
    if cam is None:
        batch["index"] += 1
        if not bpy.app.timers.is_registered(_kick_next_render):
            bpy.app.timers.register(_kick_next_render, first_interval=0.01)
        return None

    frame = job["frame"]
    filename = format_output_name(frame, cam, scene=scene)

    # Keep UI unlocked — snapshot what the user was looking at, then set the job
    _snapshot_user_view(batch, scene)
    scene.camera = cam
    scene.frame_set(frame)
    apply_camera_resolution_for_render(
        scene, cam, baseline=batch.get("orig_resolution"),
    )
    apply_panel_outline_layers(scene, cam)
    scene.render.filepath = os.path.join(batch["base_dir"], filename)

    _set_wm_rendering(True, f"{batch['index'] + 1} / {batch['total']}")
    batch["awaiting"] = True

    try:
        result = bpy.ops.render.render('INVOKE_DEFAULT', write_still=True)
    except Exception as exc:  # noqa: BLE001
        batch["awaiting"] = False
        _finish_batch(cancelled=True, error=str(exc))
        return None

    # INVOKE_DEFAULT returns RUNNING_MODAL / FINISHED; CANCELLED means it did not start
    if 'CANCELLED' in result:
        batch["awaiting"] = False
        _finish_batch(cancelled=True, error="Render operator was cancelled")
        return None

    return None


def start_batch_render(scene, queue, base_dir):
    """Begin a chained still-render batch. Returns (ok, message)."""
    global _batch

    if _batch is not None:
        return False, "A marker-frame batch render is already running"

    wm = bpy.context.window_manager
    if wm is not None and getattr(wm, "rmcf_rendering", False):
        return False, "A marker-frame batch render is already running"

    orig_cam = scene.camera
    baseline = baseline_render_resolution(scene)
    if hasattr(scene, "rmcf_resolution"):
        if not scene.rmcf_resolution.override_applied:
            copy_resolution_settings(scene.render, scene.rmcf_resolution.stored)
        scene.rmcf_resolution.is_rendering = True

    _batch = {
        "queue": queue,
        "index": 0,
        "total": len(queue),
        "rendered": 0,
        "base_dir": base_dir,
        "scene_ptr": scene.as_pointer(),
        "orig_frame": scene.frame_current,
        "orig_camera_ptr": orig_cam.as_pointer() if orig_cam else 0,
        "orig_camera_name": orig_cam.name if orig_cam else "",
        "orig_filepath": scene.render.filepath,
        "orig_overwrite": scene.render.use_overwrite,
        "orig_placeholders": scene.render.use_placeholder,
        "orig_resolution": baseline,
        # Per-shot recipes flip lock_interface; the file's own value must come back.
        "orig_lock_interface": scene.render.use_lock_interface,
        "user_frame": scene.frame_current,
        "user_camera_ptr": orig_cam.as_pointer() if orig_cam else 0,
        "user_camera_name": orig_cam.name if orig_cam else "",
        "awaiting": False,
    }

    scene.render.use_placeholder = False
    scene.render.use_overwrite = True
    # Blender reads the scene on another thread while rendering, so edits made
    # during a job can crash it. Locking is the supported way to prevent that.
    scene.render.use_lock_interface = bool(
        get_addon_preference("lock_interface_while_rendering", True))

    _install_batch_handlers()
    _set_wm_rendering(True, f"0 / {len(queue)}")

    if not bpy.app.timers.is_registered(_kick_next_render):
        bpy.app.timers.register(_kick_next_render, first_interval=0.01)

    return True, f"Rendering {len(queue)} frame(s) → {base_dir}"


def abort_batch_render(*, silent=False):
    """Abort any in-progress batch (file load / unregister)."""
    global _batch
    if _batch is None:
        _remove_batch_handlers()
        _set_wm_rendering(False, "")
        return
    if silent:
        batch = _batch
        _batch = None
        if bpy.app.timers.is_registered(_kick_next_render):
            bpy.app.timers.unregister(_kick_next_render)
        _remove_batch_handlers()
        if batch is not None:
            _restore_batch_scene_state(batch)
        _set_wm_rendering(False, "")
    else:
        _finish_batch(cancelled=True)


@persistent
def _on_render_complete(scene):
    batch = _batch
    if batch is None or scene is None:
        return
    if scene.as_pointer() != batch["scene_ptr"]:
        return
    # Ignore unrelated renders (e.g. user F12) while a batch exists but is between jobs
    if not batch.get("awaiting"):
        return

    batch["awaiting"] = False
    batch["rendered"] += 1
    batch["index"] += 1

    # Give the viewport back so the user can edit while the next job starts
    _restore_user_view(batch)

    if not bpy.app.timers.is_registered(_kick_next_render):
        bpy.app.timers.register(_kick_next_render, first_interval=0.05)


@persistent
def _on_render_cancel(scene):
    batch = _batch
    if batch is None or scene is None:
        return
    if scene.as_pointer() != batch["scene_ptr"]:
        return
    if not batch.get("awaiting"):
        return
    batch["awaiting"] = False
    _finish_batch(cancelled=True)


# ---------------------------------------------------------------------------
# In-place addon updates from manga_render_manager_vX.Y.Z.zip
# ---------------------------------------------------------------------------

_UPDATE_ZIP_RE = re.compile(
    r'^manga_render_manager_v\.?(\d+)(?:\.(\d+))?(?:\.(\d+))?\.zip$',
    re.IGNORECASE,
)


def _version_tuple_padded(version):
    """Zip names may carry 1-3 numbers (v2, v2.2, v2.2.1); pad to 3 so
    v2 == v2.0 == v2.0.0 when compared against bl_info."""
    version = tuple(version)
    return version + (0,) * (3 - len(version))


def _version_display(version):
    """Human form without padding zeros: (2, 2, 0) -> "2.2", (2, 0, 0) -> "2"."""
    parts = list(version)
    while len(parts) > 1 and parts[-1] == 0:
        parts.pop()
    return ".".join(str(part) for part in parts)
_UPDATE_CHECK_CACHE = {
    'timestamp': 0.0,
    'scan_dir': None,
    'result': None,  # Optional[Tuple[Tuple[int, int, int], str]]
}
UPDATE_CHECK_TTL_SECONDS = 5.0
PREFS_BACKUP_FILENAME = "manga_render_manager_prefs_backup.json"


def _addon_directory():
    return os.path.dirname(os.path.realpath(__file__))


def _invalidate_update_check_cache(*_args, **_kwargs):
    _UPDATE_CHECK_CACHE['timestamp'] = 0.0
    _UPDATE_CHECK_CACHE['scan_dir'] = None
    _UPDATE_CHECK_CACHE['result'] = None


def get_update_source_directory(context=None):
    """Folder to scan for update zips. Pref path if set, otherwise the addon folder."""
    try:
        if context is None:
            context = bpy.context
        prefs = context.preferences.addons[__name__].preferences
        custom = (getattr(prefs, 'update_source_directory', '') or '').strip().strip('"').strip("'")
        if custom:
            # DIR_PATH may be relative (//) or include a trailing slash
            try:
                norm = bpy.path.abspath(custom)
            except Exception:  # noqa: BLE001
                norm = custom
            norm = os.path.expanduser(os.path.normpath(norm))
            if os.path.isdir(norm):
                return norm
    except Exception:  # noqa: BLE001
        pass
    return _addon_directory()


def prefs_backup_path():
    return os.path.join(bpy.utils.user_resource('CONFIG'), PREFS_BACKUP_FILENAME)


def _parse_update_zip_version(filename):
    match = _UPDATE_ZIP_RE.match(filename)
    if not match:
        return None
    ver = tuple(int(part) for part in match.groups() if part is not None)
    return _version_tuple_padded(ver)


def _installed_addon_mtime():
    try:
        return os.path.getmtime(os.path.realpath(__file__))
    except OSError:
        return 0.0


def find_latest_update_zip(context=None):
    """Return (version_tuple, zip_path, zip_mtime) for the newest matching zip, or None."""
    scan_dir = get_update_source_directory(context)
    best = None  # (version, mtime, path)
    try:
        with os.scandir(scan_dir) as entries:
            for entry in entries:
                if not entry.is_file():
                    continue
                ver = _parse_update_zip_version(entry.name)
                if ver is None:
                    continue
                try:
                    mtime = entry.stat().st_mtime
                except OSError:
                    mtime = 0.0
                if best is None or ver > best[0] or (ver == best[0] and mtime > best[1]):
                    best = (ver, mtime, entry.path)
    except OSError:
        return None
    if best is None:
        return None
    return best[0], best[2], best[1]


def find_newer_addon_zip(force=False, context=None):
    """Return (version_tuple, zip_path) if an update zip should be offered, else None.

    Offers an update when:
    - zip version is higher than the running addon, or
    - zip version matches but the zip file is newer than the installed addon file
      (so rebuilding the same version after edits still shows Update)
    """
    scan_dir = get_update_source_directory(context)
    now = time.monotonic()
    if (
        not force
        and _UPDATE_CHECK_CACHE['timestamp']
        and _UPDATE_CHECK_CACHE['scan_dir'] == scan_dir
        and (now - _UPDATE_CHECK_CACHE['timestamp']) < UPDATE_CHECK_TTL_SECONDS
    ):
        return _UPDATE_CHECK_CACHE['result']

    current = _version_tuple_padded(bl_info.get('version', (0, 0, 0)))
    installed_mtime = _installed_addon_mtime()
    # Allow small clock/fs skew so a just-written install does not keep offering itself
    mtime_slack = 2.0

    best = None
    best_key = None  # (version, mtime)
    try:
        with os.scandir(scan_dir) as entries:
            for entry in entries:
                if not entry.is_file():
                    continue
                ver = _parse_update_zip_version(entry.name)
                if ver is None:
                    continue
                try:
                    mtime = entry.stat().st_mtime
                except OSError:
                    mtime = 0.0

                newer_version = ver > current
                same_version_newer_file = (
                    ver == current and mtime > (installed_mtime + mtime_slack)
                )
                if not (newer_version or same_version_newer_file):
                    continue

                key = (ver, mtime)
                if best_key is None or key > best_key:
                    best_key = key
                    best = (ver, entry.path)
    except OSError:
        best = None

    _UPDATE_CHECK_CACHE['timestamp'] = now
    _UPDATE_CHECK_CACHE['scan_dir'] = scan_dir
    _UPDATE_CHECK_CACHE['result'] = best
    return best


_PREFS_SKIP_PROPS = {'rna_type', 'bl_idname'}
_PREFS_SIMPLE_TYPES = {'STRING', 'BOOLEAN', 'INT', 'FLOAT', 'ENUM'}


def _serialize_prop(owner, prop):
    """JSON-safe value for one RNA property."""
    value = getattr(owner, prop.identifier)
    if prop.type == 'ENUM' and getattr(prop, 'is_enum_flag', False):
        return sorted(value)
    if getattr(prop, 'is_array', False):
        return list(value)
    if prop.type == 'INT':
        return int(value)
    if prop.type == 'FLOAT':
        return float(value)
    if prop.type == 'BOOLEAN':
        return bool(value)
    return value


def serialize_preferences(prefs):
    """Snapshot every writable property on an AddonPreferences, including collections.

    Generic on purpose: adding a new preference later needs no matching change
    here, so an update can never silently drop a setting.
    """
    data = {}
    for prop in prefs.bl_rna.properties:
        name = prop.identifier
        if name in _PREFS_SKIP_PROPS:
            continue
        try:
            if prop.type == 'COLLECTION':
                items = []
                for element in getattr(prefs, name):
                    entry = {}
                    for sub in element.bl_rna.properties:
                        if sub.identifier in _PREFS_SKIP_PROPS or sub.is_readonly:
                            continue
                        if sub.type not in _PREFS_SIMPLE_TYPES:
                            continue
                        entry[sub.identifier] = _serialize_prop(element, sub)
                    items.append(entry)
                data[name] = items
            elif prop.type in _PREFS_SIMPLE_TYPES and not prop.is_readonly:
                data[name] = _serialize_prop(prefs, prop)
        except Exception:  # noqa: BLE001
            continue
    return data


def apply_preferences(prefs, data):
    """Write a serialize_preferences() snapshot back onto an AddonPreferences."""
    for name, value in data.items():
        prop = prefs.bl_rna.properties.get(name)
        if prop is None:
            continue
        try:
            if prop.type == 'COLLECTION':
                if not isinstance(value, list) or not value:
                    # register() may seed a collection; an empty snapshot should
                    # not wipe those seeds back out.
                    continue
                collection = getattr(prefs, name)
                collection.clear()
                for entry in value:
                    element = collection.add()
                    if not isinstance(entry, dict):
                        continue
                    for sub_name, sub_value in entry.items():
                        if element.bl_rna.properties.get(sub_name) is None:
                            continue
                        try:
                            setattr(element, sub_name, sub_value)
                        except Exception:  # noqa: BLE001
                            continue
            elif prop.type == 'ENUM' and getattr(prop, 'is_enum_flag', False):
                setattr(prefs, name, set(value))
            elif getattr(prop, 'is_array', False):
                setattr(prefs, name, tuple(value))
            else:
                setattr(prefs, name, value)
        except Exception:  # noqa: BLE001
            continue


def get_addon_preference(name, default=None):
    """One addon preference, safe to call before/while preferences exist."""
    try:
        prefs = bpy.context.preferences.addons[__name__].preferences
    except (KeyError, AttributeError):
        return default
    return getattr(prefs, name, default)


def backup_addon_preferences(context):
    """Snapshot addon prefs so an update cannot wipe them."""
    prefs = context.preferences.addons[__name__].preferences
    data = {
        'module': __name__,
        'format': 2,
        'prefs': serialize_preferences(prefs),
    }
    path = prefs_backup_path()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as handle:
        json.dump(data, handle, indent=2)
    return path


def restore_addon_preferences(context, module_name=None):
    """Restore prefs from the JSON backup written before an update."""
    path = prefs_backup_path()
    if not os.path.isfile(path):
        return False
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            data = json.load(handle)
    except Exception:  # noqa: BLE001
        return False

    mod = module_name or data.get('module') or __name__
    try:
        prefs = context.preferences.addons[mod].preferences
    except (KeyError, AttributeError):
        return False

    if data.get('format', 1) >= 2:
        apply_preferences(prefs, data.get('prefs') or {})
        return True

    # Legacy flat backup written by 1.17.13 and earlier
    if 'update_source_directory' in data:
        prefs.update_source_directory = data['update_source_directory'] or ''
    return True


def find_duplicate_addon_copies():
    """Other .py files in the addons folder that are also Manga Render Manager.

    Each one shows up as its own entry in Blender's add-on list, so surface them
    instead of silently updating only the copy that happens to be running.
    """
    target = os.path.realpath(__file__)
    folder = os.path.dirname(target)
    duplicates = []
    try:
        with os.scandir(folder) as entries:
            for entry in entries:
                if not entry.is_file() or not entry.name.lower().endswith('.py'):
                    continue
                if os.path.realpath(entry.path) == target:
                    continue
                try:
                    with open(entry.path, 'r', encoding='utf-8', errors='replace') as handle:
                        head = handle.read(2048)
                except OSError:
                    continue
                if '"name": "Manga Render Manager"' in head or "'name': 'Manga Render Manager'" in head:
                    duplicates.append(entry.name)
    except OSError:
        pass
    return sorted(duplicates)


def _purge_module_bytecode(target):
    """Drop the cached .pyc so the re-import cannot pick up the previous build."""
    cache_dir = os.path.join(os.path.dirname(target), '__pycache__')
    stem = os.path.splitext(os.path.basename(target))[0] + '.'
    try:
        with os.scandir(cache_dir) as entries:
            for entry in entries:
                if entry.is_file() and entry.name.startswith(stem) and entry.name.endswith('.pyc'):
                    try:
                        os.remove(entry.path)
                    except OSError:
                        pass
    except OSError:
        pass


def _extract_update_zip_over_addon(zip_path):
    """Overwrite this addon's .py with the .py inside the update zip. Keeps module name stable."""
    with zipfile.ZipFile(zip_path, 'r') as archive:
        py_names = [
            name for name in archive.namelist()
            if name.lower().endswith('.py')
            and not name.endswith('/')
            and not os.path.basename(name).startswith('.')
            and '__macosx' not in name.lower()
        ]
        if not py_names:
            raise RuntimeError("Update zip contains no .py file")
        py_names.sort(
            key=lambda name: (
                0 if 'render_manager' in os.path.basename(name).lower() else 1,
                name,
            )
        )
        payload = archive.read(py_names[0])

    # Refuse to overwrite a working addon with something that cannot load
    if b'bl_info' not in payload:
        raise RuntimeError(f"{os.path.basename(py_names[0])} has no bl_info; not an addon")
    try:
        compile(payload, os.path.basename(py_names[0]), 'exec')
    except SyntaxError as exc:
        raise RuntimeError(f"Update contains invalid Python: {exc}") from exc

    # Write beside the target and rename, so a failure mid-write cannot leave a
    # half-written addon on disk (Dropbox sync in particular likes to interrupt)
    target = os.path.realpath(__file__)
    staging = target + '.incoming'
    try:
        with open(staging, 'wb') as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(staging, target)
    except BaseException:
        try:
            os.remove(staging)
        except OSError:
            pass
        raise

    _purge_module_bytecode(target)
    return target


class RMCF_AddonPreferences(bpy.types.AddonPreferences):
    bl_idname = __name__

    update_source_directory: StringProperty(
        name="Update Folder",
        description=(
            "Folder to scan for manga_render_manager_vX.Y.Z.zip updates. "
            "Leave empty to use the folder containing this addon"
        ),
        subtype='DIR_PATH',
        default="",
        update=lambda self, context: _invalidate_update_check_cache(),
    )

    lock_interface_while_rendering: BoolProperty(
        name="Lock Interface While Rendering",
        description=(
            "Freeze the interface during batch renders. Blender reads the scene on "
            "another thread while rendering, so editing during a render can crash it. "
            "Turn this off only if you accept that risk"
        ),
        default=True,
    )

    embed_shots_in_blend: BoolProperty(
        name="Store Shots In The .blend",
        description=(
            "Keep a copy of the shot list inside the .blend on every save, and rebuild "
            "any missing shot from it on load. Lets a .blend travel on its own — whoever "
            "opens it gets the cameras with nothing else to import. Leave this on"
        ),
        default=True,
    )

    restore_shots_on_load: BoolProperty(
        name="Rebuild Missing Shots On Load",
        description=(
            "When a file opens, recreate any shot the embedded copy has but the scene "
            "is missing. Never touches shots that are already there"
        ),
        default=True,
    )

    def draw(self, context):
        layout = self.layout

        newer = find_newer_addon_zip(context=context)
        if newer:
            ver, _zip_path = newer
            row = layout.row()
            row.alert = True
            row.operator(
                "rmcf.update_addon",
                text=f"Update Available: {'.'.join(str(v) for v in ver)}",
                icon='FILE_REFRESH',
            )
            layout.separator()

        layout.label(text="Rendering:")
        layout.prop(self, "lock_interface_while_rendering")
        layout.separator()

        layout.label(text="Shot List:")
        col = layout.column(align=True)
        col.prop(self, "embed_shots_in_blend")
        sub = col.column(align=True)
        sub.enabled = self.embed_shots_in_blend
        sub.prop(self, "restore_shots_on_load")
        layout.separator()

        layout.label(text="Addon Updates:")
        layout.prop(self, "update_source_directory")
        scan_dir = get_update_source_directory(context)
        layout.label(text=f"Looking in: {scan_dir}", icon='INFO')
        current = _version_tuple_padded(bl_info.get('version', (0, 0, 0)))
        layout.label(text=f"Installed: {_version_display(current)}")
        latest = find_latest_update_zip(context=context)
        if latest:
            ver, zip_path, _mtime = latest
            layout.label(
                text=f"Latest zip: {_version_display(ver)} ({os.path.basename(zip_path)})"
            )
        else:
            layout.label(text="Latest zip: none found (need manga_render_manager_vX.Y[.Z].zip)")
        layout.label(text=f"Installed file: {os.path.basename(os.path.realpath(__file__))}")

        duplicates = find_duplicate_addon_copies()
        if duplicates:
            box = layout.box()
            box.alert = True
            box.label(text="Other copies installed (each is a separate add-on entry):", icon='ERROR')
            for name in duplicates:
                box.label(text=name)
            box.label(text="Updating only touches the file above. Remove the others manually.")


class RMCF_OT_update_addon(Operator):
    bl_idname = "rmcf.update_addon"
    bl_label = "Update Manga Render Manager"
    bl_description = (
        "Install the newer manga_render_manager_vX.Y[.Z].zip from the Update Folder. "
        "Addon preferences are backed up and restored"
    )

    def execute(self, context):
        newer = find_newer_addon_zip(force=True, context=context)
        if not newer:
            scan_dir = get_update_source_directory(context)
            self.report(
                {'WARNING'},
                f"No newer manga_render_manager_vX.Y[.Z].zip in {scan_dir}",
            )
            return {'CANCELLED'}

        version, zip_path = newer
        module_name = __name__

        try:
            backup_addon_preferences(context)
        except Exception as exc:  # noqa: BLE001
            self.report({'WARNING'}, f"Preference backup failed: {exc}")

        try:
            _extract_update_zip_over_addon(zip_path)
        except Exception as exc:  # noqa: BLE001
            self.report({'ERROR'}, f"Failed to install update: {exc}")
            return {'CANCELLED'}

        def _reload_updated_addon():
            # Unregister first. addon_utils.disable() looks the module up in
            # sys.modules, so clearing sys.modules beforehand makes it skip
            # unregister() entirely and leak the old render handlers.
            try:
                addon_utils.disable(module_name, default_set=False)
            except Exception:  # noqa: BLE001
                pass
            # Now drop the cached module so enable() loads the new file from disk
            for key in list(sys.modules):
                if key == module_name or key.startswith(module_name + "."):
                    del sys.modules[key]
            try:
                addon_utils.modules(refresh=True)
            except Exception:  # noqa: BLE001
                pass
            try:
                addon_utils.enable(module_name, default_set=True, persistent=True)
            except Exception:  # noqa: BLE001
                return None
            try:
                restore_addon_preferences(bpy.context, module_name)
                bpy.ops.wm.save_userpref()
            except Exception:  # noqa: BLE001
                pass
            _invalidate_update_check_cache()
            return None

        bpy.app.timers.register(_reload_updated_addon, first_interval=0.1)

        ver_str = '.'.join(str(part) for part in version)
        self.report(
            {'INFO'},
            f"Updating {os.path.basename(os.path.realpath(__file__))} in place to {ver_str}…",
        )
        return {'FINISHED'}


# ---------------------------------------------------------------------------
# Property group / UIList
# ---------------------------------------------------------------------------

class RMCF_MarkerItem(PropertyGroup):
    frame: IntProperty(name="Frame")
    marker_name: StringProperty(name="Marker Name")
    camera_name: StringProperty(name="Camera Name")
    camera: PointerProperty(
        name="Camera",
        type=bpy.types.Object,
        poll=camera_object_poll,
    )
    enabled: BoolProperty(name="Render", default=True)
    selected: BoolProperty(name="Selected", default=False)


class RMCF_CameraResolutionProps(PropertyGroup):
    use_custom_resolution: BoolProperty(
        name="Use Custom Resolution",
        description="Use this camera's resolution instead of the scene default",
        default=False,
        get=get_use_camera_resolution,
        set=set_use_camera_resolution,
    )
    resolution_x: IntProperty(
        name="Resolution X",
        description="Number of horizontal pixels in the rendered image",
        default=1920,
        min=1,
        subtype='PIXEL',
        update=_make_res_update("resolution_x"),
    )
    resolution_y: IntProperty(
        name="Resolution Y",
        description="Number of vertical pixels in the rendered image",
        default=1080,
        min=1,
        subtype='PIXEL',
        update=_make_res_update("resolution_y"),
    )
    resolution_percentage: IntProperty(
        name="Resolution Scale",
        description="Percentage scale for render resolution",
        default=100,
        min=1,
        soft_max=100,
        subtype='PERCENTAGE',
        update=_make_res_update("resolution_percentage"),
    )
    pixel_aspect_x: FloatProperty(
        name="Pixel Aspect X",
        description="Horizontal aspect ratio — for anamorphic or non-square pixels",
        default=1.0,
        min=1.0,
        max=200.0,
        precision=3,
        update=_make_res_update("pixel_aspect_x"),
    )
    pixel_aspect_y: FloatProperty(
        name="Pixel Aspect Y",
        description="Vertical aspect ratio — for anamorphic or non-square pixels",
        default=1.0,
        min=1.0,
        max=200.0,
        precision=3,
        update=_make_res_update("pixel_aspect_y"),
    )


class RMCF_SceneResolutionProps(PropertyGroup):
    stored: PointerProperty(type=RMCF_CameraResolutionProps)
    previous_camera: PointerProperty(type=bpy.types.Object)
    is_rendering: BoolProperty(default=False)
    # True while scene.render holds a camera's override instead of the scene's
    # own resolution — the only reliable signal that .stored is the real baseline.
    override_applied: BoolProperty(default=False)


class RMCF_MangaCameraProps(PropertyGroup):
    page_number: IntProperty(
        name="Page",
        description="Manga page number for this panel camera",
        default=1,
        min=0,
    )
    panel_id: StringProperty(
        name="Panel",
        description="Panel id on the page (A, B, C…)",
        default="A",
    )
    status: EnumProperty(
        name="Status",
        description="Panel production status",
        items=(
            ('WIP', "WIP", "Work in progress"),
            ('REVIEW', "Review", "Needs review"),
            ('DONE', "Done", "Cleanup finished"),
            ('APPROVED', "Approved", "Approved for delivery"),
        ),
        default='WIP',
        update=_make_manga_update("status"),
    )
    notes: StringProperty(
        name="Notes",
        description="Short panel notes",
        default="",
    )
    print_width_mm: FloatProperty(
        name="Width mm",
        description="Print width in millimeters",
        default=127.0,
        min=1.0,
        soft_max=500.0,
        update=_make_manga_update("print_width_mm"),
    )
    print_height_mm: FloatProperty(
        name="Height mm",
        description="Print height in millimeters",
        default=180.0,
        min=1.0,
        soft_max=500.0,
        update=_make_manga_update("print_height_mm"),
    )
    print_dpi: IntProperty(
        name="DPI",
        description="Print dots per inch used to compute pixel resolution",
        default=600,
        min=72,
        soft_max=1200,
        update=_make_manga_update("print_dpi"),
    )
    # Pre-1.17.30 files carried Freestyle-specific props; the addon no longer
    # uses Freestyle at all, so they are only kept as hidden fields so that
    # existing files still load without warnings.
    freestyle_mode: StringProperty(default='FILE', options={'HIDDEN'})
    outline_freestyle: BoolProperty(default=False, options={'HIDDEN'})
    outline_lineart: BoolProperty(
        name="Line Art",
        description="Show Grease Pencil Line Art modifiers for this panel",
        default=True,
        update=_make_manga_update("outline_lineart"),
    )
    outline_gp_details: BoolProperty(
        name="GP Details",
        description="Show the Details Grease Pencil layer",
        default=True,
        update=_make_manga_update("outline_gp_details"),
    )
    outline_gp_erase: BoolProperty(
        name="GP Erase (render)",
        description="Include the Erase layer in renders (usually off — guide only)",
        default=False,
        update=_make_manga_update("outline_gp_erase"),
    )
    # Kept as a hidden field so pre-1.17.30 files still load; no longer used.
    line_weight_scale: FloatProperty(default=1.0, options={'HIDDEN'})
    show_safe_area: BoolProperty(
        name="Safe Area Guides",
        description="Show composition / safe area guides on this camera",
        default=True,
        update=_make_manga_update("show_safe_area"),
    )
    draw_plane_mode: EnumProperty(
        name="Draw Plane Placement",
        description="Where to put the transparent Grease Pencil draw plane",
        items=(
            (
                'NEAR',
                "In Front (Near Clip)",
                "Place just past the camera clip start so drawings stay in front of scene objects",
            ),
            (
                'CUSTOM',
                "Custom Distance",
                "Place at a fixed distance from the camera (can sit behind nearby objects)",
            ),
        ),
        default='NEAR',
    )
    draw_plane_distance: FloatProperty(
        name="Draw Plane Distance",
        description="Distance in front of the camera when placement is Custom",
        default=2.0,
        min=0.0001,
        soft_max=50.0,
        unit='LENGTH',
    )
    draw_plane: PointerProperty(
        name="Draw Plane",
        description="Transparent plane aligned to this camera for Grease Pencil surface drawing",
        type=bpy.types.Object,
    )
    gp_object: PointerProperty(
        name="Grease Pencil",
        description="Grease Pencil object used for panel details and erase guides",
        type=bpy.types.Object,
    )


def cameras_for_size_preset(scene):
    """Selected marker cameras, falling back to the active row's camera."""
    cams = iter_selected_marker_cameras(scene)
    if cams:
        return cams
    items = scene.rmcf_items
    idx = scene.rmcf_index
    if 0 <= idx < len(items):
        cam = get_item_camera(items[idx], scene)
        if cam is not None:
            return [cam]
    return []


def apply_size_preset(scene, preset):
    """Push a size preset onto every camera the size dropdown targets."""
    n = 0
    for cam in cameras_for_size_preset(scene):
        if apply_ratio_preset_to_camera(cam, preset):
            n += 1
    if n:
        update_camera_resolution_handler(scene, from_render=True)
    return n


def _quick_ratio_update(self, context):
    # Picking a size is the action -- there is no separate Apply button.
    scene = getattr(context, "scene", None)
    if scene is not None and not getattr(context.window_manager, "rmcf_rendering", False):
        apply_size_preset(scene, self.quick_ratio)


class RMCF_MangaSceneProps(PropertyGroup):
    use_manga_export_names: BoolProperty(
        name="Manga Export Names",
        description="Name renders Page##_PanelX_Camera_Frame_####",
        default=True,
    )
    auto_apply_outline: BoolProperty(
        name="Auto Apply Outline",
        description="Apply the panel outline recipe when previewing a marker",
        default=True,
    )
    profile: EnumProperty(
        name="Profile",
        description="Quick resolution profile for selected cameras",
        items=(
            ('WEB', "Web", "Lower % for previews / web"),
            ('PRINT', "Print", "Full resolution for print"),
        ),
        default='PRINT',
    )
    web_percent: IntProperty(
        name="Web %",
        description="Resolution percentage used by the Web profile",
        default=50,
        min=1,
        soft_max=100,
        subtype='PERCENTAGE',
    )
    quick_ratio: EnumProperty(
        name="Size",
        description="Panel size preset — applied to the selected cameras as soon as you pick it",
        items=(
            ('PORTRAIT_3_4', "3:4 Portrait", "1536 x 2048"),
            ('PORTRAIT_2_3', "2:3 Portrait", "1600 x 2400"),
            ('SQUARE', "1:1 Square", "2048 x 2048"),
            ('WEBTOON', "Webtoon", "1080 x 1920"),
            ('VERTICAL_VIDEO', "Vertical Video",
             "1080 x 1920 — Instagram Reels, TikTok, YouTube Shorts"),
            ('LANDSCAPE_3_2', "3:2 Landscape", "2400 x 1600"),
        ),
        default='PORTRAIT_3_4',
        update=_quick_ratio_update,
    )


class RMCF_UL_markers(UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index=0):
        # NOT aligned: an aligned neighbour makes the highlighted button square
        # off its left edge and outline it, which reads as a stray line right
        # before the camera icon. Unaligned, the fill is a clean rounded shape
        # that simply starts after the checkbox.
        row = layout.row(align=False)
        row.prop(item, "enabled", text="")

        selected = bool(item.selected)
        scene = context.scene
        cam = get_item_camera(item, scene)
        label = cam.name if cam is not None else (item.camera_name or "Missing")
        # One widget for the whole name, in every state: it is the Shift/Ctrl/Cmd
        # multi-select hit target AND cannot shift, because nothing about it
        # changes on selection but the button's fill.
        # Do not swap widget type per state -- Blender pads text differently
        # inside a text field (+2px) and inside a button with no icon (+14px,
        # it centers), so any swap makes the name visibly jump. Emboss/depress
        # only repaints the same widget, so the text stays put.
        # Renaming lives on rmcf.rename_camera instead of an inline field.
        #
        # depress paints the button in the theme's selection colour -- the same
        # highlight Blender gives the active row -- so a multi-selection reads
        # as highlighted rows rather than a column of checkmarks.
        # Frame and name share ONE button: two buttons would draw an edge where
        # they meet, and a line through the middle of a highlighted row reads
        # as a glitch. The frame leads and is zero-padded, so the digits are a
        # fixed-width column and the names line up underneath each other.
        op = row.operator(
            "rmcf.select_list_item",
            text=f"{item.frame:04d}   {label}",
            icon='CAMERA_DATA',
            emboss=selected,
            depress=selected,
        )
        op.index = index


# ---------------------------------------------------------------------------
# Operators
# ---------------------------------------------------------------------------

class RMCF_OT_select_list_item(Operator):
    bl_idname = "rmcf.select_list_item"
    bl_label = "Select Marker Camera"
    bl_description = (
        "Select marker — Shift: range, Cmd/Ctrl: add/remove "
        "(resolution edits apply to all selected)"
    )
    bl_options = {'INTERNAL'}

    index: IntProperty()

    @classmethod
    def poll(cls, context):
        # Never move the frame or camera while a render is reading the scene.
        return not render_in_progress()

    def invoke(self, context, event):
        global _select_from_operator, _selection_anchor, _preview_done_for_index

        scene = context.scene
        items = scene.rmcf_items
        idx = self.index
        if idx < 0 or idx >= len(items):
            return {'CANCELLED'}

        _select_from_operator = True
        try:
            if event.shift:
                # Outliner semantics: the range runs from the active row to the
                # clicked one and is added to what is already selected.
                anchor = _selection_anchor
                if not (0 <= anchor < len(items)) or not any(it.selected for it in items):
                    anchor = scene.rmcf_index
                anchor = max(0, min(anchor, len(items) - 1))
                lo, hi = sorted((anchor, idx))
                for i in range(lo, hi + 1):
                    if not items[i].selected:
                        items[i].selected = True
                # The anchor stays put so dragging the shift-click up and down
                # keeps sweeping from the same row.
            elif event.ctrl or event.oskey:
                items[idx].selected = not items[idx].selected
                _selection_anchor = idx
            else:
                exclusive_select_list_item(scene, idx)
                _selection_anchor = idx

            scene.rmcf_index = idx
        finally:
            _select_from_operator = False

        # Apply once here; mark so the index-update timer does not preview again
        if 0 <= idx < len(items):
            preview_marker_item(scene, items[idx], context)
            _preview_done_for_index = (scene.name, idx)

        return {'FINISHED'}


class RMCF_OT_list_navigate(Operator):
    bl_idname = "rmcf.list_navigate"
    bl_label = "Navigate Marker List"
    bl_description = "Move the active marker list item (WASD / arrows, Shift to extend)"
    bl_options = {'INTERNAL'}

    direction: EnumProperty(
        items=(
            ('UP', "Up", "Previous marker"),
            ('DOWN', "Down", "Next marker"),
            ('LEFT', "Left", "Previous marker"),
            ('RIGHT', "Right", "Next marker"),
        ),
        default='DOWN',
    )
    extend: BoolProperty(
        name="Extend",
        description="Grow the selection from the anchor instead of replacing it",
        default=False,
    )

    def invoke(self, context, event):
        # Keymap entries set `extend`; holding Shift on any of them also does.
        if event.shift:
            self.extend = True
        return self.execute(context)

    @classmethod
    def poll(cls, context):
        # Never move the frame or camera while a render is reading the scene.
        if render_in_progress():
            return False
        scene = context.scene
        return scene is not None and len(getattr(scene, "rmcf_items", [])) > 0

    def execute(self, context):
        global _select_from_operator, _preview_done_for_index, _selection_anchor

        scene = context.scene
        items = scene.rmcf_items
        n = len(items)
        if n == 0:
            return {'CANCELLED'}

        delta = -1 if self.direction in {'UP', 'LEFT'} else 1
        idx = max(0, min(n - 1, scene.rmcf_index + delta))
        if idx == scene.rmcf_index and 0 <= idx < n:
            # Already at end — still refresh preview/selection
            pass

        _select_from_operator = True
        try:
            if self.extend:
                anchor = _selection_anchor
                if not (0 <= anchor < n) or not any(it.selected for it in items):
                    anchor = scene.rmcf_index
                lo, hi = sorted((anchor, idx))
                for i in range(lo, hi + 1):
                    if not items[i].selected:
                        items[i].selected = True
            else:
                exclusive_select_list_item(scene, idx)
            scene.rmcf_index = idx
        finally:
            _select_from_operator = False

        preview_marker_item(scene, items[idx], context)
        _preview_done_for_index = (scene.name, idx)
        return {'FINISHED'}


class RMCF_OT_rename_camera(Operator):
    bl_idname = "rmcf.rename_camera"
    bl_label = "Rename Camera"
    bl_description = "Rename the active marker camera"
    bl_options = {'REGISTER', 'UNDO'}

    new_name: StringProperty(name="Name")

    @classmethod
    def poll(cls, context):
        scene = context.scene
        if scene is None:
            return False
        items = getattr(scene, "rmcf_items", None)
        if not items:
            return False
        idx = scene.rmcf_index
        return 0 <= idx < len(items) and get_item_camera(items[idx], scene) is not None

    def _active_camera(self, context):
        scene = context.scene
        items = scene.rmcf_items
        idx = scene.rmcf_index
        if not (0 <= idx < len(items)):
            return None
        return get_item_camera(items[idx], scene)

    def invoke(self, context, event):
        cam = self._active_camera(context)
        if cam is None:
            return {'CANCELLED'}
        self.new_name = cam.name
        return context.window_manager.invoke_props_dialog(self)

    def execute(self, context):
        cam = self._active_camera(context)
        if cam is None:
            return {'CANCELLED'}
        name = (self.new_name or "").strip()
        if not name:
            self.report({'WARNING'}, "Name cannot be empty")
            return {'CANCELLED'}
        cam.name = name
        return {'FINISHED'}


class RMCF_OT_refresh(Operator):
    bl_idname = "rmcf.refresh"
    bl_label = "Refresh Marker List"
    bl_description = "Rebuild the list from timeline markers with bound cameras"

    def execute(self, context):
        sync_marker_list(context.scene, force=True)
        self.report({'INFO'}, f"{len(context.scene.rmcf_items)} marker camera(s)")
        return {'FINISHED'}


class RMCF_OT_add_camera_marker(Operator):
    bl_idname = "rmcf.add_camera_marker"
    bl_label = "Add Camera Marker"
    bl_description = ("Create a new camera matching the current view — position and viewport focal "
                      "length — and add a timeline marker on the first free frame from here")
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        if getattr(context.window_manager, "rmcf_rendering", False):
            self.report({'WARNING'}, "Cannot add cameras while a batch render is running")
            return {'CANCELLED'}

        # Inside a camera view the new camera inherits the old one's optics and
        # transform, so the existing zoom/pan already shows the same picture.
        keep_framing = view3d_is_camera_view(context)

        cam_obj, marker = create_marker_camera(context)
        sync_marker_list(scene, force=True)

        # Select the new list row and preview it
        for i, item in enumerate(scene.rmcf_items):
            if item.frame == marker.frame and item.camera == cam_obj:
                exclusive_select_list_item(scene, i)
                scene.rmcf_index = i
                break

        ensure_camera_view(context, fit_frame=not keep_framing)
        apply_list_selection_to_objects(scene, context)
        self.report({'INFO'}, f"Added {cam_obj.name} at frame {marker.frame}")
        return {'FINISHED'}


class RMCF_OT_select_all(Operator):
    bl_idname = "rmcf.select_all"
    bl_label = "Enable All for Render"
    bl_description = "Enable every marker in the list for render"

    def execute(self, context):
        for item in context.scene.rmcf_items:
            item.enabled = True
        return {'FINISHED'}


class RMCF_OT_select_none(Operator):
    bl_idname = "rmcf.select_none"
    bl_label = "Disable All for Render"
    bl_description = "Disable every marker in the list for render"

    def execute(self, context):
        for item in context.scene.rmcf_items:
            item.enabled = False
        return {'FINISHED'}


class RMCF_OT_enable_selected(Operator):
    bl_idname = "rmcf.enable_selected"
    bl_label = "Enable Selected for Render"
    bl_description = "Enable the currently selected markers for render"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        scene = context.scene
        return scene is not None and any(item.selected for item in getattr(scene, "rmcf_items", []))

    def execute(self, context):
        n = 0
        for item in context.scene.rmcf_items:
            if item.selected:
                item.enabled = True
                n += 1
        self.report({'INFO'}, f"Enabled {n} marker(s) for render")
        return {'FINISHED'}


class RMCF_OT_disable_selected(Operator):
    bl_idname = "rmcf.disable_selected"
    bl_label = "Disable Selected for Render"
    bl_description = "Disable the currently selected markers for render"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        scene = context.scene
        return scene is not None and any(item.selected for item in getattr(scene, "rmcf_items", []))

    def execute(self, context):
        n = 0
        for item in context.scene.rmcf_items:
            if item.selected:
                item.enabled = False
                n += 1
        self.report({'INFO'}, f"Disabled {n} marker(s) for render")
        return {'FINISHED'}


class RMCF_OT_apply_resolution_to_selected(Operator):
    bl_idname = "rmcf.apply_resolution_to_selected"
    bl_label = "Apply Resolution to Selected"
    bl_description = "Copy the active camera's custom resolution settings to all selected marker cameras"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        scene = context.scene
        if scene is None or not getattr(scene, "rmcf_items", None):
            return False
        cams = iter_selected_marker_cameras(scene)
        return len(cams) >= 2

    def execute(self, context):
        scene = context.scene
        items = scene.rmcf_items
        idx = scene.rmcf_index
        if not (0 <= idx < len(items)):
            self.report({'WARNING'}, "No active marker")
            return {'CANCELLED'}

        src_cam = get_item_camera(items[idx], scene)
        if src_cam is None:
            self.report({'WARNING'}, "Active marker has no camera")
            return {'CANCELLED'}

        src = src_cam.data.rmcf_resolution
        n = 0
        for cam in iter_selected_marker_cameras(scene):
            if cam == src_cam:
                continue
            dst = cam.data.rmcf_resolution
            dst["use_custom_resolution"] = src.use_custom_resolution
            copy_resolution_settings(src, dst)
            n += 1

        update_camera_resolution_handler(scene, from_render=True)
        self.report({'INFO'}, f"Applied resolution to {n} camera(s)")
        return {'FINISHED'}



class RMCF_OT_manga_ratio_preset(Operator):
    bl_idname = "rmcf.manga_ratio_preset"
    bl_label = "Apply Panel Ratio"
    bl_description = "Apply a manga panel ratio preset to selected cameras"
    bl_options = {'REGISTER', 'UNDO'}

    preset: EnumProperty(
        name="Preset",
        items=(
            ('SQUARE', "1:1 Square", ""),
            ('PORTRAIT_3_4', "3:4 Portrait", ""),
            ('PORTRAIT_2_3', "2:3 Portrait", ""),
            ('LANDSCAPE_3_2', "3:2 Landscape", ""),
            ('WEBTOON', "Webtoon", ""),
            ('VERTICAL_VIDEO', "Vertical Video",
             "1080 x 1920 — Instagram Reels, TikTok, YouTube Shorts"),
        ),
        default='PORTRAIT_3_4',
    )

    def execute(self, context):
        n = apply_size_preset(context.scene, self.preset)
        self.report({'INFO'}, f"Applied {self.preset} to {n} camera(s)")
        return {'FINISHED'}


class RMCF_OT_manga_apply_print_size(Operator):
    bl_idname = "rmcf.manga_apply_print_size"
    bl_label = "Apply Print Size"
    bl_description = "Set custom resolution from width/height mm and DPI"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        cams = iter_selected_marker_cameras(scene)
        if not cams:
            items = scene.rmcf_items
            idx = scene.rmcf_index
            if 0 <= idx < len(items):
                cam = get_item_camera(items[idx], scene)
                if cam is not None:
                    cams = [cam]
        if not cams:
            self.report({'WARNING'}, "No camera selected")
            return {'CANCELLED'}

        items = scene.rmcf_items
        idx = scene.rmcf_index
        src = get_item_camera(items[idx], scene) if 0 <= idx < len(items) else cams[0]
        manga = src.data.rmcf_manga
        for cam in cams:
            apply_print_size_to_camera(
                cam,
                width_mm=manga.print_width_mm,
                height_mm=manga.print_height_mm,
                dpi=manga.print_dpi,
            )
        update_camera_resolution_handler(scene, from_render=True)
        self.report({'INFO'}, f"Applied print size to {len(cams)} camera(s)")
        return {'FINISHED'}


class RMCF_OT_manga_apply_profile(Operator):
    bl_idname = "rmcf.manga_apply_profile"
    bl_label = "Apply Web/Print Profile"
    bl_description = "Set resolution % on selected cameras for web preview or print"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        cams = iter_selected_marker_cameras(scene)
        if not cams:
            items = scene.rmcf_items
            idx = scene.rmcf_index
            if 0 <= idx < len(items):
                cam = get_item_camera(items[idx], scene)
                if cam is not None:
                    cams = [cam]
        percent = 100 if scene.rmcf_manga.profile == 'PRINT' else scene.rmcf_manga.web_percent
        n = 0
        for cam in cams:
            res = cam.data.rmcf_resolution
            res.use_custom_resolution = True
            res.resolution_percentage = percent
            n += 1
        update_camera_resolution_handler(scene, from_render=True)
        self.report({'INFO'}, f"Set {percent}% on {n} camera(s)")
        return {'FINISHED'}


class RMCF_OT_manga_apply_outline(Operator):
    bl_idname = "rmcf.manga_apply_outline"
    bl_label = "Apply Outline Recipe"
    bl_description = "Apply the GP outline / lineart layer recipe for the active panel"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        items = scene.rmcf_items
        idx = scene.rmcf_index
        cam = get_item_camera(items[idx], scene) if 0 <= idx < len(items) else scene.camera
        if cam is None or cam.type != 'CAMERA':
            self.report({'WARNING'}, "No active panel camera")
            return {'CANCELLED'}
        apply_panel_outline_layers(scene, cam)
        manga = cam.data.rmcf_manga
        if manga.show_safe_area:
            apply_safe_area(cam, True)
        self.report({'INFO'}, f"Applied outline recipe for {cam.name}")
        return {'FINISHED'}


class RMCF_OT_manga_safe_area(Operator):
    bl_idname = "rmcf.manga_safe_area"
    bl_label = "Toggle Safe Area"
    bl_description = "Toggle composition / safe area guides on the active panel camera"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        items = scene.rmcf_items
        idx = scene.rmcf_index
        cam = get_item_camera(items[idx], scene) if 0 <= idx < len(items) else None
        if cam is None:
            self.report({'WARNING'}, "No active panel camera")
            return {'CANCELLED'}
        manga = cam.data.rmcf_manga
        manga.show_safe_area = not manga.show_safe_area
        apply_safe_area(cam, manga.show_safe_area)
        self.report({'INFO'}, "Safe area " + ("on" if manga.show_safe_area else "off"))
        return {'FINISHED'}


class RMCF_OT_clear_output_dir(Operator):
    bl_idname = "rmcf.clear_output_dir"
    bl_label = "Use Blender Output Folder"
    bl_description = "Clear custom folder and use the blend file Output folder"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        if _CUSTOM_OUTPUT_KEY in scene:
            del scene[_CUSTOM_OUTPUT_KEY]
        return {'FINISHED'}


class RMCF_OT_open_output_dir(Operator):
    bl_idname = "rmcf.open_output_dir"
    bl_label = "Open Render Folder"
    bl_description = "Open the current render folder in the system file browser"

    def execute(self, context):
        try:
            path = get_render_base_dir(context.scene)
        except ValueError as exc:
            self.report({'ERROR'}, str(exc))
            return {'CANCELLED'}
        try:
            open_folder(path)
        except OSError as exc:
            self.report({'ERROR'}, f"Could not open folder: {exc}")
            return {'CANCELLED'}
        self.report({'INFO'}, path)
        return {'FINISHED'}


class RMCF_OT_browse_output_dir(Operator):
    bl_idname = "rmcf.browse_output_dir"
    bl_label = "Choose Render Folder"
    bl_description = "Pick the render folder with the file browser"

    # Filled in by the file browser; named "directory" so it picks folders.
    directory: StringProperty(subtype='DIR_PATH')

    def invoke(self, context, event):
        try:
            self.directory = get_render_base_dir(context.scene)
        except ValueError:
            self.directory = ""
        context.window_manager.fileselect_add(self)
        return {'RUNNING_MODAL'}

    def execute(self, context):
        context.scene.rmcf_output_dir = self.directory
        return {'FINISHED'}


class RMCF_OT_render(Operator):
    bl_idname = "rmcf.render"
    bl_label = "Render Selected Marker Frames"
    bl_description = "Render enabled marker cameras via Blender's render UI (Esc to cancel)"
    bl_options = {'REGISTER'}

    def _start(self, context):
        scene = context.scene
        sync_marker_list(scene)

        if _batch is not None or getattr(context.window_manager, "rmcf_rendering", False):
            self.report({'WARNING'}, "A marker-frame batch render is already running")
            return {'CANCELLED'}

        queue = collect_render_queue(scene)
        if not queue:
            self.report({'WARNING'}, "No frames selected for render.")
            return {'CANCELLED'}

        try:
            base_dir = get_render_base_dir(scene)
        except ValueError as exc:
            self.report({'ERROR'}, str(exc))
            return {'CANCELLED'}

        try:
            os.makedirs(base_dir, exist_ok=True)
        except OSError as exc:
            self.report({'ERROR'}, f"Cannot write to '{base_dir}': {exc}")
            return {'CANCELLED'}

        if not os.access(base_dir, os.W_OK):
            self.report({'ERROR'}, f"Output folder is not writable: {base_dir}")
            return {'CANCELLED'}

        ok, message = start_batch_render(scene, queue, base_dir)
        if not ok:
            self.report({'WARNING'}, message)
            return {'CANCELLED'}

        self.report({'INFO'}, message)
        return {'FINISHED'}

    def invoke(self, context, event):
        return self._start(context)

    def execute(self, context):
        return self._start(context)


# ---------------------------------------------------------------------------
# Panel
# ---------------------------------------------------------------------------

def draw_lens_control(layout, cam_data):
    """Focal length for one marker camera — whichever value actually frames it."""
    if cam_data.type == 'ORTHO':
        layout.prop(cam_data, "ortho_scale", text="Ortho Scale")
    elif cam_data.lens_unit == 'FOV':
        layout.prop(cam_data, "angle", text="FOV")
    else:
        layout.prop(cam_data, "lens", text="Focal Length")


class RMCF_NodeTree(bpy.types.NodeTree):
    """Registering a NodeTree is the only way an add-on can add an entry to the
    editor-type dropdown. The tree itself holds nothing — it exists so the
    Manga Render Manager can be opened as its own editor, the same trick
    Pencil+ 4 Line uses for its editor."""
    bl_idname = "MangaRenderManagerTreeType"
    bl_label = "Manga Render Manager"
    bl_icon = 'EVENT_M'


def draw_render_manager_panel(panel, context):
    """One draw implementation shared by RMCF_PT_panel and RMCF_PT_editor."""
    layout = panel.layout
    scene = context.scene
    wm = context.window_manager

    # Draw cannot write ID data — only schedule a deferred sync if needed.
    if not wm.rmcf_rendering:
        schedule_marker_refresh(scene)

    newer = find_newer_addon_zip(context=context)
    if newer:
        ver, _zip_path = newer
        update_row = layout.row()
        update_row.alert = True
        update_row.operator(
            "rmcf.update_addon",
                text=f"Update to {_version_display(ver)}",
            icon='FILE_REFRESH',
        )
        layout.separator()

    items = scene.rmcf_items
    idx = scene.rmcf_index
    active_cam = get_item_camera(items[idx], scene) if 0 <= idx < len(items) else None
    n_sel = count_selected_markers(scene)
    busy = bool(wm.rmcf_rendering)

    # Enable / disable above the list
    row = layout.row(align=True)
    row.enabled = not busy
    row.operator("rmcf.select_all", text="Enable All")
    row.operator("rmcf.select_none", text="Disable All")
    row = layout.row(align=True)
    row.enabled = not busy and n_sel > 0
    row.operator("rmcf.enable_selected", text="Enable Selected")
    row.operator("rmcf.disable_selected", text="Disable Selected")

    # Locked while rendering: selecting a row jumps the frame and swaps the
    # scene camera, which is not safe while a render is reading the scene.
    list_col = layout.column()
    list_col.enabled = not busy
    list_col.template_list(
        "RMCF_UL_markers", "",
        scene, "rmcf_items",
        scene, "rmcf_index",
        rows=10,
    )

    # Add camera under the list
    row = layout.row(align=True)
    row.enabled = not busy
    row.operator("rmcf.add_camera_marker", icon='ADD', text="Add Camera")
    row.operator("rmcf.rename_camera", icon='FONT_DATA', text="")
    row.operator("rmcf.refresh", icon='FILE_REFRESH', text="")

    # Path row: reveal the folder in the system file browser, the path
    # field, pick a new folder with Blender's file browser, clear.
    row = layout.row(align=True)
    row.operator(
        "rmcf.open_output_dir",
        text="",
        icon='FILE_FOLDER',
    )
    row.prop(scene, "rmcf_output_dir", text="")
    row.operator(
        "rmcf.browse_output_dir",
        text="",
        icon='FILEBROWSER',
    )
    if has_custom_output(scene):
        row.operator("rmcf.clear_output_dir", text="", icon='X')

    if busy:
        col = layout.column(align=True)
        col.label(text=f"Rendering {wm.rmcf_progress}", icon='RENDER_STILL')
        col.label(text="Esc cancels")
    else:
        n = count_render_markers(scene)
        layout.operator(
            "rmcf.render",
            icon='RENDER_STILL',
            text="Render" if n == 0 else f"Render {n}",
        )

    # Focal length of the active panel camera (its own, per camera),
    # placed directly above the resolution box.
    if active_cam is not None:
        row = layout.row(align=True)
        row.enabled = not busy
        draw_lens_control(row, active_cam.data)

    # Custom resolution is always open — the box heads itself with its own
    # "Use Custom Resolution" toggle, so a separate collapsible header only
    # added a click.
    _draw_custom_resolution_box(layout, scene, active_cam)


def _draw_custom_resolution_box(layout, scene, active_cam):
    box = layout.box()
    if active_cam is not None:
        props = active_cam.data.rmcf_resolution
        n_edit = len(iter_selected_marker_cameras(scene)) or 1

        if n_edit > 1:
            box.label(text=f"{n_edit} cameras selected")
        row = box.row(align=True)
        row.prop(props, "use_custom_resolution", text="Use Custom Resolution")
        col = box.column(align=True)
        col.enabled = props.use_custom_resolution
        col.prop(props, "resolution_x", text="X")
        col.prop(props, "resolution_y", text="Y")
        col.prop(props, "resolution_percentage", text="%")
        col.separator()
        col.label(text="Size Preset")
        col.prop(scene.rmcf_manga, "quick_ratio", text="")

    else:
        box.label(text="Select a camera in the list", icon='INFO')


class RMCF_PT_panel(Panel):
    bl_label = "Manga Render Manager  v" + ".".join(str(v) for v in bl_info["version"])
    bl_idname = "RMCF_PT_panel"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Manga Manager"

    draw = draw_render_manager_panel


class RMCF_PT_camera_resolution(Panel):
    """Also expose per-camera resolution on the Camera data properties tab."""
    bl_label = "Custom Resolution"
    bl_idname = "RMCF_PT_camera_resolution"
    bl_space_type = 'PROPERTIES'
    bl_region_type = 'WINDOW'
    bl_context = "data"
    bl_parent_id = "DATA_PT_camera"
    bl_options = {'DEFAULT_CLOSED'}

    @classmethod
    def poll(cls, context):
        return context.camera is not None

    def draw_header(self, context):
        props = context.camera.rmcf_resolution
        self.layout.prop(props, "use_custom_resolution", text="")

    def draw(self, context):
        props = context.camera.rmcf_resolution
        layout = self.layout
        layout.use_property_split = True
        col = layout.column()
        col.active = props.use_custom_resolution

        sub = col.column(align=True)
        sub.prop(props, "resolution_x", text="Resolution X")
        sub.prop(props, "resolution_y", text="Y")
        sub.prop(props, "resolution_percentage", text="%")

        sub = col.column(align=True)
        sub.prop(props, "pixel_aspect_x", text="Aspect X")
        sub.prop(props, "pixel_aspect_y", text="Y")

        layout.use_property_split = False
        box = layout.box()
        box.enabled = props.use_custom_resolution
        box.label(text="Size Preset")
        box.prop(context.scene.rmcf_manga, "quick_ratio", text="")


# ---------------------------------------------------------------------------
# Lifecycle
# ---------------------------------------------------------------------------

class RMCF_PT_editor(Panel):
    """The same UI as the 3D View sidebar, in the Manga Render Manager editor."""
    bl_label = RMCF_PT_panel.bl_label
    bl_idname = "RMCF_PT_editor"
    bl_space_type = 'NODE_EDITOR'
    bl_region_type = 'UI'
    bl_category = "Manga Manager"

    @classmethod
    def poll(cls, context):
        return getattr(context.space_data, "tree_type", None) == RMCF_NodeTree.bl_idname

    draw = draw_render_manager_panel


classes = (
    RMCF_AddonPreferences,
    RMCF_OT_update_addon,
    RMCF_MarkerItem,
    RMCF_CameraResolutionProps,
    RMCF_SceneResolutionProps,
    RMCF_MangaCameraProps,
    RMCF_MangaSceneProps,
    RMCF_UL_markers,
    RMCF_OT_select_list_item,
    RMCF_OT_list_navigate,
    RMCF_OT_rename_camera,
    RMCF_OT_refresh,
    RMCF_OT_add_camera_marker,
    RMCF_OT_select_all,
    RMCF_OT_select_none,
    RMCF_OT_enable_selected,
    RMCF_OT_disable_selected,
    RMCF_OT_apply_resolution_to_selected,
    RMCF_OT_manga_ratio_preset,
    RMCF_OT_manga_apply_print_size,
    RMCF_OT_manga_apply_profile,
    RMCF_OT_manga_apply_outline,
    RMCF_OT_manga_safe_area,
    RMCF_OT_clear_output_dir,
    RMCF_OT_open_output_dir,
    RMCF_OT_browse_output_dir,
    RMCF_OT_render,
    RMCF_NodeTree,
    RMCF_PT_panel,
    RMCF_PT_editor,
    RMCF_PT_camera_resolution,
)

# (keymap, keymap_item) pairs registered by this add-on
_addon_keymaps = []


def register_keymaps():
    """WASD / arrows navigate the marker list while the mouse is over the N-panel."""
    global _addon_keymaps
    _addon_keymaps.clear()

    wm = bpy.context.window_manager
    kc = wm.keyconfigs.addon
    if kc is None:
        return

    # region_type='UI' → only while the sidebar (N-panel) has focus, not the viewport
    km = kc.keymaps.new(name='3D View', space_type='VIEW_3D', region_type='UI')
    for key, direction in (
        ('W', 'UP'),
        ('S', 'DOWN'),
        ('A', 'LEFT'),
        ('D', 'RIGHT'),
        ('UP_ARROW', 'UP'),
        ('DOWN_ARROW', 'DOWN'),
        ('LEFT_ARROW', 'LEFT'),
        ('RIGHT_ARROW', 'RIGHT'),
    ):
        kmi = km.keymap_items.new('rmcf.list_navigate', key, 'PRESS')
        kmi.properties.direction = direction
        kmi.properties.extend = False
        _addon_keymaps.append((km, kmi))

        # Shift+key grows the selection from the anchor, like Shift+arrow does
        # in the Outliner.
        kmi = km.keymap_items.new('rmcf.list_navigate', key, 'PRESS', shift=True)
        kmi.properties.direction = direction
        kmi.properties.extend = True
        _addon_keymaps.append((km, kmi))


def unregister_keymaps():
    global _addon_keymaps
    for km, kmi in _addon_keymaps:
        try:
            km.keymap_items.remove(kmi)
        except Exception:  # noqa: BLE001
            pass
    _addon_keymaps.clear()


def _unregister_module_timers():
    global _preview_timer_on, _preview_pending, _refresh_timer_on

    _preview_pending = None
    _preview_timer_on = False
    _refresh_pending.clear()
    _refresh_timer_on = False

    for fn in (_run_preview_timer, _run_refresh_timer, _kick_next_render,
               _initial_sync):
        if bpy.app.timers.is_registered(fn):
            bpy.app.timers.unregister(fn)


def _clear_module_caches():
    global _preview_pending, _suppress_sync, _select_from_operator, _selection_anchor
    global _preview_done_for_index, _prop_sync_depth
    restore_draw_session_hidden()
    _preview_pending = None
    _refresh_pending.clear()
    _suppress_sync = 0
    _select_from_operator = False
    _selection_anchor = 0
    _preview_done_for_index = None
    _prop_sync_depth = 0
    _marker_sigs.clear()


def _initial_sync():
    # Deferred out of register(): bpy.data is restricted while add-ons load.
    restore = get_addon_preference("restore_shots_on_load", True) and get_addon_preference(
        "embed_shots_in_blend", True)
    embedded = read_embedded_shots() if restore else {}
    single = next(iter(embedded.values())) if len(embedded) == 1 else None

    for scene in bpy.data.scenes:
        sync_marker_list(scene, force=True)
        if not embedded:
            continue
        shots = embedded.get(scene.name, single)
        if not shots:
            continue
        try:
            count = restore_embedded_shots(scene, shots)
        except Exception as exc:  # noqa: BLE001 — never block a file from opening
            print(f"[Manga Render Manager] Could not restore stored shots: {exc}")
            continue
        if count:
            print(f"[Manga Render Manager] Restored {count} stored shot(s) in '{scene.name}'")
    return None


@persistent
def rmcf_save_pre(_dummy):
    """Keep the .blend's own copy of the shot list current on every save."""
    if not get_addon_preference("embed_shots_in_blend", True):
        return
    if getattr(bpy.context.window_manager, "rmcf_rendering", False):
        return  # the list is mid-batch; snapshot it once the render is done
    try:
        for scene in bpy.data.scenes:
            sync_marker_list(scene, force=True)
        write_embedded_shots()
    except Exception as exc:  # noqa: BLE001 — a snapshot must never break saving
        print(f"[Manga Render Manager] Could not store shots in the .blend: {exc}")


@persistent
def rmcf_render_started(_scene, _depsgraph=None):
    global _render_active
    _render_active = True


@persistent
def rmcf_render_ended(_scene, _depsgraph=None):
    global _render_active
    _render_active = False


def resync_override_state(scene):
    """Rebuild override_applied after a load — files saved before it existed
    (or saved while a camera override was live) have no trustworthy value."""
    settings = getattr(scene, "rmcf_resolution", None)
    if settings is None:
        return
    cam = scene.camera
    props = cam.data.rmcf_resolution if cam is not None and cam.type == 'CAMERA' else None
    settings.override_applied = bool(
        props is not None
        and props.use_custom_resolution
        and resolution_settings_match(scene.render, props)
    )


@persistent
def rmcf_load_post(_dummy):
    """Reset module state after file load / reload."""
    abort_batch_render(silent=True)
    for scene in bpy.data.scenes:
        resync_override_state(scene)
    _unregister_module_timers()
    _clear_module_caches()
    bpy.app.timers.register(_initial_sync, first_interval=0.1)


def register():
    for cls in classes:
        bpy.utils.register_class(cls)

    bpy.types.Scene.rmcf_items = CollectionProperty(type=RMCF_MarkerItem)
    bpy.types.Scene.rmcf_index = IntProperty(default=0, update=on_rmcf_index_update)
    # Plain string field on purpose: subtype='DIR_PATH' would embed Blender's
    # own folder button, which duplicates the browse operator and hovers as
    # "Accept". PATH_SUPPORTS_BLEND_RELATIVE keeps "//" blend-relative paths
    # accepted; resolution is handled by resolve_output_dir().
    bpy.types.Scene.rmcf_output_dir = StringProperty(
        name="Render Folder",
        description="Render folder. Clear the field (or press X) to use the blend file Output folder",
        get=get_rmcf_output_dir,
        set=set_rmcf_output_dir,
        options={'PATH_SUPPORTS_BLEND_RELATIVE'},
    )
    bpy.types.Scene.rmcf_resolution = PointerProperty(type=RMCF_SceneResolutionProps)
    bpy.types.Scene.rmcf_manga = PointerProperty(type=RMCF_MangaSceneProps)
    bpy.types.Camera.rmcf_resolution = PointerProperty(type=RMCF_CameraResolutionProps)
    bpy.types.Camera.rmcf_manga = PointerProperty(type=RMCF_MangaCameraProps)
    bpy.types.WindowManager.rmcf_rendering = BoolProperty(default=False)
    bpy.types.WindowManager.rmcf_progress = StringProperty(default="")

    if rmcf_load_post not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(rmcf_load_post)
    if rmcf_save_pre not in bpy.app.handlers.save_pre:
        bpy.app.handlers.save_pre.append(rmcf_save_pre)

    if update_camera_resolution_handler not in bpy.app.handlers.depsgraph_update_pre:
        bpy.app.handlers.depsgraph_update_pre.append(update_camera_resolution_handler)
    if update_camera_resolution_handler not in bpy.app.handlers.frame_change_pre:
        bpy.app.handlers.frame_change_pre.append(update_camera_resolution_handler)

    # Track any render, not just our batches — a plain F12 animation fires
    # frame_change_pre for every frame, and writing render settings there
    # changes the image size out from under the renderer.
    for handler, callback in (
        (bpy.app.handlers.render_init, rmcf_render_started),
        (bpy.app.handlers.render_complete, rmcf_render_ended),
        (bpy.app.handlers.render_cancel, rmcf_render_ended),
    ):
        if callback not in handler:
            handler.append(callback)

    register_keymaps()
    bpy.app.timers.register(_initial_sync, first_interval=0.1)


def unregister():
    abort_batch_render(silent=True)
    unregister_keymaps()
    _unregister_module_timers()
    _clear_module_caches()
    _remove_batch_handlers()

    if rmcf_load_post in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.remove(rmcf_load_post)
    if rmcf_save_pre in bpy.app.handlers.save_pre:
        bpy.app.handlers.save_pre.remove(rmcf_save_pre)

    if update_camera_resolution_handler in bpy.app.handlers.depsgraph_update_pre:
        bpy.app.handlers.depsgraph_update_pre.remove(update_camera_resolution_handler)
    if update_camera_resolution_handler in bpy.app.handlers.frame_change_pre:
        bpy.app.handlers.frame_change_pre.remove(update_camera_resolution_handler)

    for handler, callback in (
        (bpy.app.handlers.render_init, rmcf_render_started),
        (bpy.app.handlers.render_complete, rmcf_render_ended),
        (bpy.app.handlers.render_cancel, rmcf_render_ended),
    ):
        if callback in handler:
            handler.remove(callback)

    del bpy.types.Scene.rmcf_items
    del bpy.types.Scene.rmcf_index
    del bpy.types.Scene.rmcf_output_dir
    del bpy.types.Scene.rmcf_resolution
    del bpy.types.Scene.rmcf_manga
    del bpy.types.Camera.rmcf_resolution
    del bpy.types.Camera.rmcf_manga
    del bpy.types.WindowManager.rmcf_rendering
    del bpy.types.WindowManager.rmcf_progress

    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
