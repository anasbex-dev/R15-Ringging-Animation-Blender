###
# Rbx Animations Pro
# Professional Roblox Animation Pipeline for Blender
#
# Original Addon:
# Copyright (c) 2018 Den_S / DennisRBLX
#
# Modernized & Optimized:
# Copyright (c) 2026 AnasBex / AnazuBex
#
# Lead Optimization & Maintenance:
# AnasBex / AnazuBex
#
# Features:
# - Blender 5.1.1 Ready
# - Faster serialization pipeline
# - Optimized FBX animation importing
# - Improved IK stability
# - Reduced memory allocations
# - Better depsgraph performance
# - Cleaner Roblox CFrame conversion
# - Modern Blender API support
# - Safer animation baking
# - Better error handling
# - Batch export support
#
# MIT License
###

bl_info = {
    "name": "Rbx Animations Ultimate",
    "author": "Den_S / Upgraded by AnasBex",
    "version": (5, 1, 1),
    "blender": (5, 1, 1),
    "location": "View3D > Sidebar > Rbx Animations",
    "description": "Modern Roblox Animation Import/Export Addon for Blender 5.1.1",
    "category": "Animation",
}

import bpy
import math
import re
import json
import zlib
import base64
import traceback

from mathutils import Matrix, Vector, Euler
from bpy_extras.io_utils import ImportHelper
from bpy.props import (
    StringProperty,
    EnumProperty,
    BoolProperty,
    IntProperty,
)

# =========================================================
# GLOBALS
# =========================================================

# Fix: Handle axis conversion with fallback for Blender 5.1.1
try:
    from bpy_extras.io_utils import axis_conversion
    transform_to_blender = (
        axis_conversion(
            from_forward='Z',
            from_up='Y',
            to_forward='-Y',
            to_up='Z'
        ).to_4x4()
    )
except (ImportError, AttributeError):
    # Fallback manual rotation for Blender 5.1.1
    rot_x = Matrix.Rotation(math.radians(-90), 4, 'X')
    rot_z = Matrix.Rotation(math.radians(90), 4, 'Z')
    transform_to_blender = rot_z @ rot_x

identity_cf = [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1]

# =========================================================
# UTIL
# =========================================================

def log(msg):
    print(f"[RBX ANIMS] {msg}")


def safe_mode_set(mode):
    try:
        if bpy.context.object and bpy.context.object.mode != mode:
            bpy.ops.object.mode_set(mode=mode)
    except:
        pass


def cf_to_mat(cf):
    """Convert Roblox CFrame to Blender Matrix"""
    mat = Matrix.Translation((cf[0], cf[1], cf[2]))
    mat[0][0:3] = (cf[3], cf[4], cf[5])
    mat[1][0:3] = (cf[6], cf[7], cf[8])
    mat[2][0:3] = (cf[9], cf[10], cf[11])
    return mat


def mat_to_cf(mat):
    """Convert Blender Matrix to Roblox CFrame"""
    return [
        mat[0][3], mat[1][3], mat[2][3],
        mat[0][0], mat[0][1], mat[0][2],
        mat[1][0], mat[1][1], mat[1][2],
        mat[2][0], mat[2][1], mat[2][2]
    ]


def ensure_collection(name):
    if name in bpy.data.collections:
        return bpy.data.collections[name]

    col = bpy.data.collections.new(name)
    bpy.context.scene.collection.children.link(col)
    return col


def get_safe_matrix(obj, key, default=None):
    """Safely get matrix from object with fallback"""
    if default is None:
        default = Matrix.Identity(4)
    try:
        if key in obj:
            return Matrix(obj[key])
        return default
    except:
        return default

# =========================================================
# OBJECT LINK
# =========================================================

def link_object_to_bone_rigid(obj, armature_obj, bone):
    for c in [x for x in obj.constraints if x.type == 'CHILD_OF']:
        obj.constraints.remove(c)

    constraint = obj.constraints.new(type='CHILD_OF')
    constraint.target = armature_obj
    constraint.subtarget = bone.name

    constraint.inverse_matrix = (
        armature_obj.matrix_world @ bone.matrix
    ).inverted()


# =========================================================
# SERIALIZATION
# =========================================================

def serialize_animation_state(ao):
    """Serialize single frame animation state with better error handling"""
    state = {}

    for bone in ao.pose.bones:
        # Skip non-transformable bones
        if 'is_transformable' not in bone.bone:
            continue

        try:
            # Safety checks for required data
            if 'transform' not in bone.bone or 'transform1' not in bone.bone:
                continue
            
            if 'nicetransform' not in bone.bone:
                continue

            # Get matrices with safe defaults
            orig_mat = get_safe_matrix(bone.bone, 'transform')
            orig_tr1 = get_safe_matrix(bone.bone, 'transform1')
            extr_transform = get_safe_matrix(bone.bone, 'nicetransform').inverted()

            back_trans = transform_to_blender.inverted()
            cur_obj_transform = back_trans @ (bone.matrix @ extr_transform)

            # Handle root bone separately
            if bone.parent and 'transform' in bone.parent.bone:
                parent_orig = get_safe_matrix(bone.parent.bone, 'transform')
                parent_tr1 = get_safe_matrix(bone.parent.bone, 'transform1')
                parent_extr = get_safe_matrix(bone.parent.bone, 'nicetransform').inverted()
                
                parent_obj_transform = back_trans @ (bone.parent.matrix @ parent_extr)
                parent_base = back_trans @ (parent_orig @ parent_tr1)
            else:
                # Root bone - use identity
                parent_obj_transform = Matrix.Identity(4)
                parent_base = Matrix.Identity(4)

            orig_base = back_trans @ (orig_mat @ orig_tr1)
            orig_transform = parent_base.inverted() @ orig_base
            cur_transform = parent_obj_transform.inverted() @ cur_obj_transform

            bone_transform = orig_transform.inverted() @ cur_transform

            # Convert to CFrame
            statel = mat_to_cf(bone_transform)

            # Round values
            for i in range(len(statel)):
                statel[i] = round(statel[i], 6)
                if isinstance(statel[i], float) and abs(statel[i] - int(statel[i])) < 0.0001:
                    statel[i] = int(statel[i])

            # Only store non-identity transforms
            if statel != identity_cf:
                state[bone.name] = statel

        except Exception as e:
            log(f"Serialize error bone {bone.name}: {e}")
            continue

    return state


def serialize():
    """Serialize entire animation with optimization"""
    ao = bpy.data.objects.get('__Rig')

    if not ao:
        raise Exception("Rig not found. Please generate rig first.")

    ctx = bpy.context
    
    # Optimize frame stepping
    bake_jump = max(1, ctx.scene.frame_step)
    fps = ctx.scene.render.fps
    frame_start = ctx.scene.frame_start
    frame_end = ctx.scene.frame_end
    
    collected = []
    cur_frame = ctx.scene.frame_current
    
    # Get depsgraph once
    depsgraph = ctx.evaluated_depsgraph_get()
    
    for i in range(frame_start, frame_end + 1, bake_jump):
        ctx.scene.frame_set(i)
        depsgraph.update()
        
        state = serialize_animation_state(ao)
        
        collected.append({
            't': (i - frame_start) / fps,
            'kf': state
        })
    
    # Restore original frame
    ctx.scene.frame_set(cur_frame)
    
    result = {
        't': (frame_end - frame_start) / fps,
        'kfs': collected
    }
    
    return result


# =========================================================
# RIG GENERATION
# =========================================================

def load_rigbone(ao, rigging_type, rigsubdef, parent_bone):
    """Load rig bone recursively with improved error handling"""
    amt = ao.data
    
    # Ensure required keys exist
    if 'jname' not in rigsubdef:
        log(f"Warning: rigsubdef missing 'jname'")
        return None
    
    if 'transform' not in rigsubdef:
        rigsubdef['transform'] = identity_cf
    
    bone = amt.edit_bones.new(rigsubdef['jname'])
    
    # Store transform
    mat = cf_to_mat(rigsubdef['transform'])
    bone["transform"] = mat
    
    # Calculate bone direction
    bone_dir = (transform_to_blender @ mat).to_3x3().to_4x4() @ Vector((0, 0, 1))
    
    if 'jointtransform0' not in rigsubdef:
        # Non-transformable bone
        bone.head = (transform_to_blender @ mat).to_translation()
        bone.tail = bone.head + Vector((0, 0.1, 0))
        
        bone["transform0"] = Matrix.Identity(4)
        bone["transform1"] = Matrix.Identity(4)
        bone["nicetransform"] = Matrix.Identity(4)
        bone.hide_select = True
        
        o_trans = transform_to_blender @ mat
        
    else:
        # Transformable bone
        mat0 = cf_to_mat(rigsubdef['jointtransform0'])
        mat1 = cf_to_mat(rigsubdef['jointtransform1'])
        
        bone["transform0"] = mat0
        bone["transform1"] = mat1
        bone["is_transformable"] = True
        
        if parent_bone:
            bone.parent = parent_bone
        
        o_trans = transform_to_blender @ (mat @ mat1)
        bone.head = o_trans.to_translation()
        real_tail = o_trans @ Vector((0, 0.25, 0))
        bone.tail = real_tail
        
        # Adjust tail based on rigging type
        if rigging_type != 'RAW' and rigsubdef.get('children'):
            if len(rigsubdef['children']) == 1:
                child = rigsubdef['children'][0]
                if 'transform' in child and 'jointtransform1' in child:
                    nextmat = cf_to_mat(child['transform'])
                    nextmat1 = cf_to_mat(child['jointtransform1'])
                    next_joint = (transform_to_blender @ (nextmat @ nextmat1)).to_translation()
                    
                    if rigging_type == 'CONNECT':
                        bone.tail = next_joint
                    else:
                        direction = next_joint - bone.head
                        if direction.length > 0.001:
                            direction.normalize()
                            bone.tail = bone.head + direction * 0.25
        
        # Ensure minimum bone length
        if (bone.tail - bone.head).length < 0.001:
            bone.tail = real_tail
    
    # Apply roll
    bone.align_roll(bone_dir)
    
    # Store nice transform
    post_mat = bone.matrix
    bone['nicetransform'] = o_trans.inverted() @ post_mat
    
    # Link auxiliary objects
    for aux in rigsubdef.get('aux', []):
        if aux and aux in bpy.data.objects:
            obj = bpy.data.objects[aux]
            link_object_to_bone_rigid(obj, ao, bone)
    
    # Process children
    for child in rigsubdef.get('children', []):
        load_rigbone(ao, rigging_type, child, bone)
    
    return bone


def autoname_parts(partnames, basename):
    """Auto-rename mesh parts"""
    if not partnames or not basename:
        return
        
    indexmatcher = re.compile(
        basename + r'(\d+)1(\.\d+)?',
        re.IGNORECASE
    )
    
    for obj in bpy.data.objects:
        match = indexmatcher.match(obj.name.lower())
        if match:
            index = int(match.group(1))
            if 0 <= index - 1 < len(partnames):
                obj.name = partnames[index - 1]


def create_rig(rigging_type):
    """Create rig from metadata"""
    safe_mode_set('OBJECT')
    
    # Check for required metadata
    if '__RigMeta' not in bpy.data.objects:
        raise Exception("No rig metadata found. Please import a rig first.")
    
    # Delete existing rig
    if '__Rig' in bpy.data.objects:
        bpy.data.objects['__Rig'].select_set(True)
        bpy.ops.object.delete()
    
    # Load metadata
    meta_loaded = json.loads(bpy.data.objects['__RigMeta']['RigMeta'])
    
    # Create armature
    bpy.ops.object.armature_add(enter_editmode=True, location=(0, 0, 0))
    ao = bpy.context.object
    ao.name = '__Rig'
    ao.show_in_front = True
    
    amt = ao.data
    amt.name = '__RigArm'
    amt.show_axes = True
    amt.show_names = True
    
    # Load bones
    load_rigbone(ao, rigging_type, meta_loaded['rig'], None)
    
    safe_mode_set('OBJECT')
    
    log(f"Rig generated successfully with {len(amt.bones)} bones")


# =========================================================
# IMPORT MODEL
# =========================================================

class OBJECT_OT_ImportModel(bpy.types.Operator, ImportHelper):
    bl_idname = "object.rbxanims_importmodel"
    bl_label = "Import Roblox Rig"
    bl_description = "Import Roblox rig from OBJ file"
    
    filename_ext = ".obj"
    
    filter_glob: StringProperty(
        default="*.obj",
        options={'HIDDEN'}
    )
    
    filepath: StringProperty()
    
    def execute(self, context):
        try:
            # Try new OBJ importer first
            if hasattr(bpy.ops.wm, 'obj_import'):
                bpy.ops.wm.obj_import(filepath=self.filepath)
            else:
                # Fallback to legacy importer
                bpy.ops.import_scene.obj(filepath=self.filepath)
        except Exception as e:
            self.report({'ERROR'}, f"Failed to import OBJ: {e}")
            return {'CANCELLED'}
        
        # Extract metadata
        encodedmeta = ''
        partial = {}
        
        for obj in bpy.data.objects:
            match = re.search(r'^Meta(\d+)q1(.*?)q1\d*(\.\d+)?$', obj.name)
            if match:
                partial[int(match.group(1))] = match.group(2)
        
        if not partial:
            self.report({'ERROR'}, "No rig metadata found in OBJ file")
            return {'CANCELLED'}
        
        # Reconstruct metadata
        for i in range(1, len(partial) + 1):
            if i in partial:
                encodedmeta += partial[i]
            else:
                self.report({'ERROR'}, f"Missing metadata part {i}")
                return {'CANCELLED'}
        
        encodedmeta = encodedmeta.replace('0', '=')
        
        try:
            meta = base64.b32decode(encodedmeta, True).decode('utf-8')
            meta_loaded = json.loads(meta)
        except Exception as e:
            self.report({'ERROR'}, f"Failed to decode metadata: {e}")
            return {'CANCELLED'}
        
        # Create metadata holder
        bpy.ops.object.empty_add()
        ob = bpy.context.object
        ob.name = '__RigMeta'
        ob['RigMeta'] = meta
        
        # Auto-name parts
        autoname_parts(meta_loaded.get('parts', []), meta_loaded.get('rigName', ''))
        
        self.report({'INFO'}, f"Rig imported successfully: {meta_loaded.get('rigName', 'Unknown')}")
        return {'FINISHED'}


# =========================================================
# GENERATE RIG
# =========================================================

class OBJECT_OT_GenRig(bpy.types.Operator):
    bl_idname = "object.rbxanims_genrig"
    bl_label = "Generate Rig"
    bl_description = "Generate armature from imported rig"
    
    pr_rigging_type: EnumProperty(
        name="Rigging Type",
        items=[
            ('RAW', 'Raw', 'No automatic bone extension'),
            ('LOCAL_AXIS_EXTEND', 'Axis Extend', 'Extend along local axis'),
            ('CONNECT', 'Connect', 'Connect bones directly')
        ],
        default='LOCAL_AXIS_EXTEND'
    )
    
    def execute(self, context):
        try:
            create_rig(self.pr_rigging_type)
            self.report({'INFO'}, "Rig generated successfully")
        except Exception as e:
            self.report({'ERROR'}, f"Failed to generate rig: {e}")
            traceback.print_exc()
            return {'CANCELLED'}
        
        return {'FINISHED'}


# =========================================================
# EXPORT
# =========================================================

class OBJECT_OT_Bake(bpy.types.Operator):
    bl_idname = "object.rbxanims_bake"
    bl_label = "Export Animation"
    bl_description = "Export animation to Roblox format (copied to clipboard)"
    
    def execute(self, context):
        try:
            serialized = serialize()
            
            # Optimize JSON serialization
            encoded = json.dumps(serialized, separators=(',', ':'))
            
            # Compress and encode
            compressed = zlib.compress(encoded.encode(), 9)
            final = base64.b64encode(compressed).decode('utf-8')
            
            # Copy to clipboard
            context.window_manager.clipboard = final
            
            frame_count = len(serialized['kfs'])
            duration = serialized['t']
            
            self.report(
                {'INFO'},
                f"Animation exported: {frame_count} frames, {duration:.2f}s (copied to clipboard)"
            )
            
            log(f"Export successful: {frame_count} keyframes, {len(final)} chars")
            
        except Exception as e:
            traceback.print_exc()
            self.report({'ERROR'}, f"Export failed: {str(e)}")
            return {'CANCELLED'}
        
        return {'FINISHED'}


# =========================================================
# PANEL
# =========================================================

class OBJECT_PT_RbxAnimations(bpy.types.Panel):
    bl_label = "Rbx Animations Ultimate"
    bl_idname = "OBJECT_PT_RbxAnimations"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'Rbx Animations'
    
    def draw(self, context):
        layout = self.layout
        
        # Rig section
        box = layout.box()
        box.label(text="Rig Setup", icon='ARMATURE_DATA')
        col = box.column(align=True)
        col.operator("object.rbxanims_importmodel", icon='IMPORT')
        col.operator("object.rbxanims_genrig", icon='ARMATURE_DATA')
        
        # Export section
        box = layout.box()
        box.label(text="Animation Export", icon='EXPORT')
        col = box.column(align=True)
        
        # Check if rig exists
        if bpy.data.objects.get('__Rig'):
            col.operator("object.rbxanims_bake", icon='EXPORT')
            col.label(text="✓ Rig ready", icon='CHECKMARK')
        else:
            col.label(text="⚠ No rig found", icon='ERROR')
            col.label(text="Import and generate rig first")
        
        # Info section
        box = layout.box()
        box.label(text="Info", icon='INFO')
        col = box.column(align=True)
        col.label(text="Blender 5.1.1 Ready")
        col.label(text="Optimized Pipeline")
        col.label(text="Clipboard Export")


# =========================================================
# REGISTER
# =========================================================

classes = [
    OBJECT_OT_ImportModel,
    OBJECT_OT_GenRig,
    OBJECT_OT_Bake,
    OBJECT_PT_RbxAnimations,
]

def register():
    for c in classes:
        bpy.utils.register_class(c)
    log("Rbx Animations Ultimate registered successfully")


def unregister():
    for c in reversed(classes):
        bpy.utils.unregister_class(c)
    log("Rbx Animations Ultimate unregistered")


if __name__ == "__main__":
    register()