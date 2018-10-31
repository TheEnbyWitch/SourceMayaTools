# Copyright 2018, Maciej Ray Marcin

# SourceMayaTools is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# -----------------------------------------------------------------------------------------
# VERSION INFO
# VERSION 1.0
#	+ Original - Initial release
# VERSION 1.0.1
#   + Fix scaling issue between different units

# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------- Customization (You can change these values!) ----------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
MAX_WARNINGS_SHOWN = 100 # Maximum number of warnings to show per export
EXPORT_WINDOW_NUMSLOTS = 100 # Number of slots in the export windows

# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------------------------- Global ------------------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
import os
import maya.cmds as cmds
import maya.mel as mel
import math
import sys
import datetime
import os.path
import traceback
import maya.OpenMaya as OpenMaya
import maya.OpenMayaAnim as OpenMayaAnim
import urllib2
import socket
import subprocess
import webbrowser
import Queue
import _winreg as reg
import time
import struct
import shutil
import zipfile
import re
from subprocess import Popen, PIPE, STDOUT

WarningsDuringExport = 0 # Number of warnings shown during current export
CM_TO_INCH = 0.3937007874015748031496062992126 # 1cm = 50/127in
PI_CONST = 3.141592

GLOBAL_STORAGE_REG_KEY = (reg.HKEY_CURRENT_USER, "Software\\SourceMayaTools") # Registry path for global data storage
#               name     :      control code name,              control friendly name,  data storage node name, refresh function,       export function
OBJECT_NAMES =  {'menu'  :      ["SourceMayaToolsMenu",            "Source Engine Tools",   None,                   None,                   None],
                 'progress' :   ["SourceMayaToolsProgressbar",     "Progress",             None,                   None,                   None],
                 'smdmodel':      ["SMDModelExportWindow",   "Export SMD Model",        "SMDModelExporterInfo",   "RefreshSMDModelWindow",  "ExportSMDModel"],
                 'smdanim' :      ["SMDAnimExportWindow",    "Export SMD Anim",         "SMDAnimExporterInfo",    "RefreshSMDAnimWindow",   "ExportSMDAnim"],
                 }

# UTILITY FUNCTIONS FOR EXPORT

# Thanks to SETools
def __math_matrixtoquat__(maya_matrix):
    """Converts a Maya matrix array to a quaternion"""
    quat_x, quat_y, quat_z, quat_w = (0, 0, 0, 1)

    trans_remain = maya_matrix[0] + maya_matrix[5] + maya_matrix[10]
    if trans_remain > 0:
        divisor = math.sqrt(trans_remain + 1.0) * 2.0
        quat_w = 0.25 * divisor
        quat_x = (maya_matrix[6] - maya_matrix[9]) / divisor
        quat_y = (maya_matrix[8] - maya_matrix[2]) / divisor
        quat_z = (maya_matrix[1] - maya_matrix[4]) / divisor
    elif (maya_matrix[0] > maya_matrix[5]) and (maya_matrix[0] > maya_matrix[10]):
        divisor = math.sqrt(
            1.0 + maya_matrix[0] - maya_matrix[5] - maya_matrix[10]) * 2.0
        quat_w = (maya_matrix[6] - maya_matrix[9]) / divisor
        quat_x = 0.25 * divisor
        quat_y = (maya_matrix[4] + maya_matrix[1]) / divisor
        quat_z = (maya_matrix[8] + maya_matrix[2]) / divisor
    elif maya_matrix[5] > maya_matrix[10]:
        divisor = math.sqrt(
            1.0 + maya_matrix[5] - maya_matrix[0] - maya_matrix[10]) * 2.0
        quat_w = (maya_matrix[8] - maya_matrix[2]) / divisor
        quat_x = (maya_matrix[4] + maya_matrix[1]) / divisor
        quat_y = 0.25 * divisor
        quat_z = (maya_matrix[9] + maya_matrix[6]) / divisor
    else:
        divisor = math.sqrt(
            1.0 + maya_matrix[10] - maya_matrix[0] - maya_matrix[5]) * 2.0
        quat_w = (maya_matrix[1] - maya_matrix[4]) / divisor
        quat_x = (maya_matrix[8] + maya_matrix[2]) / divisor
        quat_y = (maya_matrix[9] + maya_matrix[6]) / divisor
        quat_z = 0.25 * divisor

    # Return the result
    return OpenMaya.MQuaternion(quat_x, quat_y, quat_z, quat_w)

def GetJointList():
    joints = []
    
    # Get selected objects
    selectedObjects = OpenMaya.MSelectionList()
    OpenMaya.MGlobal.getActiveSelectionList(selectedObjects)
    
    for i in range(selectedObjects.length()):
        # Get object path and node
        dagPath = OpenMaya.MDagPath()
        selectedObjects.getDagPath(i, dagPath)
        dagNode = OpenMaya.MFnDagNode(dagPath)
        
        # Ignore nodes that aren't joints or arn't top-level
        if not dagPath.hasFn(OpenMaya.MFn.kJoint) or not RecursiveCheckIsTopNode(selectedObjects, dagNode):
            continue
        
        # Breadth first search of joint tree
        searchQueue = Queue.Queue(0)
        searchQueue.put((-1, dagNode, True)) # (index = child node's parent index, child node)
        while not searchQueue.empty():
            node = searchQueue.get()
            index = len(joints)
            
            if node[2]:
                joints.append((node[0], node[1]))
            else:
                index = node[0]
            
            for i in range(node[1].childCount()):
                dagPath = OpenMaya.MDagPath()
                childNode = OpenMaya.MFnDagNode(node[1].child(i))
                childNode.getPath(dagPath)
                searchQueue.put((index, childNode, selectedObjects.hasItem(dagPath) and dagPath.hasFn(OpenMaya.MFn.kJoint)))
    
    return joints

def RecursiveCheckIsTopNode(cSelectionList, currentNode): # Checks if the given node has ANY selected parent, grandparent, etc joints
    if currentNode.parentCount() == 0:
        return True
    
    for i in range(currentNode.parentCount()):
        parentDagPath = OpenMaya.MDagPath()
        parentNode = OpenMaya.MFnDagNode(currentNode.parent(i))
        parentNode.getPath(parentDagPath)
    
        if not parentDagPath.hasFn(OpenMaya.MFn.kJoint): # Not a joint, but still check parents
            if not RecursiveCheckIsTopNode(cSelectionList, parentNode):
                return False # A parent joint is selected, we're done
            else:
                continue # No parent joints are selected, ignore this node
        
        if cSelectionList.hasItem(parentDagPath):
            return False
        else:
            if not RecursiveCheckIsTopNode(cSelectionList, parentNode):
                return False
                
    return True


def GetMaterialsFromMesh(mesh, dagPath):
    textures = {}
    
    # http://rabidsquirrelgames.googlecode.com/svn/trunk/Maya%20plugin/fileExportCmd.py
    # The code below gets a dictionary of [material name: material file name], ex: [a_material: a_material.dds]
    shaders = OpenMaya.MObjectArray()
    shaderIndices = OpenMaya.MIntArray()
    mesh.getConnectedShaders(dagPath.instanceNumber(), shaders, shaderIndices)
    
    for i in range(shaders.length()):
            shaderNode = OpenMaya.MFnDependencyNode(shaders[i])
            shaderPlug = shaderNode.findPlug("surfaceShader")
            material = OpenMaya.MPlugArray()
            shaderPlug.connectedTo(material, 1, 0)
            
            for j in range(material.length()):
                    materialNode = OpenMaya.MFnDependencyNode(material[j].node())
                    colorPlug = materialNode.findPlug("color")
                    
                    dgIt = OpenMaya.MItDependencyGraph(
                        colorPlug,
                        OpenMaya.MFn.kFileTexture,
                        OpenMaya.MItDependencyGraph.kUpstream,
                        OpenMaya.MItDependencyGraph.kBreadthFirst,
                        OpenMaya.MItDependencyGraph.kNodeLevel)
                    
                    texturePath = ""
                    
                    try: # If there is no texture, this part can throw an exception
                        dgIt.disablePruningOnFilter()
                        textureNode = OpenMaya.MFnDependencyNode(dgIt.currentItem())
                        texturePlug = textureNode.findPlug("fileTextureName")
                        texturePath = os.path.basename(texturePlug.asString())
                    except Exception:
                        pass
                    
                    textures[i] = (materialNode.name(), texturePath)
    
    texturesToFaces = []
    for i in range(shaderIndices.length()):
        if shaderIndices[i] in textures:
            texturesToFaces.append(textures[shaderIndices[i]])
        else:
            texturesToFaces.append(None)
    
    return texturesToFaces

    
def WriteJointData(f, jointC):
    jointNode = jointC[1]
    # Get the joint's transform
    path = OpenMaya.MDagPath() 
    jointNode.getPath(path)
    transform = OpenMaya.MFnTransform(path)
    
    # Get joint position
    pos = transform.getTranslation(OpenMaya.MSpace.kTransform)
    
    # Get scale (almost always 1)
    scaleUtil = OpenMaya.MScriptUtil()
    scaleUtil.createFromList([1,1,1], 3)
    scalePtr = scaleUtil.asDoublePtr()
    transform.getScale(scalePtr)
    
    # TODO: Scale support
    # scale = [OpenMaya.MScriptUtil.getDoubleArrayItem(scalePtr, 0), OpenMaya.MScriptUtil.getDoubleArrayItem(scalePtr, 1), OpenMaya.MScriptUtil.getDoubleArrayItem(scalePtr, 2)]
    
    # Get rotation matrix (mat is a 4x4, but the last row and column arn't needed)
    jointRotQuat = __math_matrixtoquat__(cmds.getAttr(path.fullPathName()+".matrix"))

    eulerRotation = jointRotQuat.asEulerRotation()

    joint_offset = (pos.x*CM_TO_INCH, pos.y*CM_TO_INCH, pos.z*CM_TO_INCH)

    joint_rotation = (eulerRotation.x,eulerRotation.y,eulerRotation.z)

    # TODO: Decide how to handle joint scaling
    # joint_scale = (scale[0], scale[1], scale[2])

    f.write("%f %f %f  %f %f %f\n" % (joint_offset[0], joint_offset[1], joint_offset[2], joint_rotation[0], joint_rotation[1], joint_rotation[2]))


# Converts a set of vertices (toConvertVertexIndices) from object-relative IDs to face-relative IDs
# vertexIndices is a list of object-relative vertex indices in face order (from polyIter.getVertices)
# toConvertVertexIndices is any set of vertices from the same faces as vertexIndices, not necessarily the same length
# Returns false if a vertex index is unable to be converted (= bad vertex values)
def VerticesObjRelToLocalRel(vertexIndices, toConvertVertexIndices):
    # http://svn.gna.org/svn/cal3d/trunk/cal3d/plugins/cal3d_maya_exporter/MayaMesh.cpp
    localVertexIndices = OpenMaya.MIntArray()
    
    for i in range(toConvertVertexIndices.length()):
        found = False
        for j in range(vertexIndices.length()):
            if toConvertVertexIndices[i] == vertexIndices[j]:
                localVertexIndices.append(j)
                found = True
                break
        if not found:
            return False
    
    return localVertexIndices


def GetShapes(joints):
    # Vars
    meshes = []
    verts = []
    tris = []
    materialDict = {}
    materials = []
    
    # Convert the joints to a dictionary, for simple searching for joint indices
    jointDict = {}
    for i, joint in enumerate(joints):
        jointDict[joint[1].partialPathName()] = i
    
    # Get all selected objects
    selectedObjects = OpenMaya.MSelectionList()
    OpenMaya.MGlobal.getActiveSelectionList(selectedObjects)
    
    # The global vert index at the start of each object
    currentStartingVertIndex = 0
    
    # Loop through all objects
    for i in range(0, selectedObjects.length()):
        # Get data on object
        object = OpenMaya.MObject()
        dagPath = OpenMaya.MDagPath()
        selectedObjects.getDependNode(i, object)
        selectedObjects.getDagPath(i, dagPath)
        
        # Ignore dag nodes that aren't shapes or shape transforms
        if not dagPath.hasFn(OpenMaya.MFn.kMesh):
            ProgressBarStep()
            continue
        
        # Lower path to shape node
        # Selecting a shape transform or shape will get the same dagPath to the shape using this
        dagPath.extendToShape()
        
        # Check for duplicates
        if dagPath.partialPathName() in meshes:
            ProgressBarStep()
            continue
        
        # Add shape to list
        meshes.append(dagPath.partialPathName())
        
        # Get mesh
        mesh = OpenMaya.MFnMesh(dagPath)
        
        # Get skin cluster
        clusterName = mel.eval("findRelatedSkinCluster " + dagPath.partialPathName()) # I couldn't figure out how to get the skin cluster via the API
        hasSkin = False
        if clusterName != None and clusterName != "" and not clusterName.isspace():
            hasSkin = True
            selList = OpenMaya.MSelectionList()
            selList.add(clusterName)
            clusterNode = OpenMaya.MObject()
            selList.getDependNode(0, clusterNode)
            skin = OpenMayaAnim.MFnSkinCluster(clusterNode)
        
        # Loop through all vertices
        vertIter = OpenMaya.MItMeshVertex(dagPath)
        while not vertIter.isDone():
            if not hasSkin:
                verts.append((vertIter.position(OpenMaya.MSpace.kWorld), []))
                vertIter.next()
                continue
            
            # Get weight values
            weightValues = OpenMaya.MDoubleArray()
            numWeights = OpenMaya.MScriptUtil() # Need this because getWeights crashes without being passed a count
            skin.getWeights(dagPath, vertIter.currentItem(), weightValues, numWeights.asUintPtr())
            
            # Get weight names
            weightJoints = OpenMaya.MDagPathArray()
            skin.influenceObjects(weightJoints)
            
            # Make sure the list of weight values and names match
            if weightValues.length() != weightJoints.length():
                PrintWarning("Failed to retrieve vertex weight list on '%s.vtx[%d]'; using default joints." % (dagPath.partialPathName(), vertIter.index()))
            
            # Remove weights of value 0 or weights from unexported joints
            finalWeights = []
            weightsSize = 0
            for i in range(0, weightJoints.length()):
                if weightValues[i] < 0.000001: # 0.000001 is the smallest decimal in xmodel exports
                    continue
                jointName = weightJoints[i].partialPathName()
                if not jointName in jointDict:
                    PrintWarning("Unexported joint %s is influencing vertex '%s.vtx[%d]' by %f%%" % (("'%s'" % jointName).ljust(15), dagPath.partialPathName(), vertIter.index(), weightValues[i]*100))
                else:
                    finalWeights.append([jointDict[jointName], weightValues[i]])
                    weightsSize += weightValues[i]
            
            # Make sure the total weight adds up to 1
            if weightsSize > 0:
                weightMultiplier = 1 / weightsSize
                for weight in finalWeights:
                    weight[1] *= weightMultiplier
            
            verts.append((
                vertIter.position(OpenMaya.MSpace.kWorld), # XYZ position
                finalWeights # List of weights
            ))
            
            # Next vert
            vertIter.next()
        
        # Get materials used by this mesh
        meshMaterials = GetMaterialsFromMesh(mesh, dagPath)
        
        # Loop through all faces
        polyIter = OpenMaya.MItMeshPolygon(dagPath)
        while not polyIter.isDone():
            # Get this poly's material
            polyMaterial = meshMaterials[polyIter.index()]
            
            # Every face must have a material
            if polyMaterial == None:
                PrintWarning("Found no material on face '%s.f[%d]'; ignoring face" % (dagPath.partialPathName(), polyIter.index()))
                polyIter.next()
                continue
            
            # Add this poly's material to the global list of used materials
            if not polyMaterial[0] in materialDict:
                materialDict[polyMaterial[0]] = len(materials)
                materials.append(polyMaterial)
            
            # Get vertex indices of this poly, and the vertex indices of this poly's triangles
            trianglePoints = OpenMaya.MPointArray()
            triangleIndices = OpenMaya.MIntArray()
            vertexIndices = OpenMaya.MIntArray()
            polyIter.getTriangles(trianglePoints, triangleIndices)
            polyIter.getVertices(vertexIndices)
            
            # localTriangleIndices is the same as triangleIndices, except each vertex is listed as the face-relative index intead of the object-realtive index
            localTriangleIndices = VerticesObjRelToLocalRel(vertexIndices, triangleIndices)
            if localTriangleIndices == False:
                return "Failed to convert object-relative vertices to face-relative on poly '%s.f[%d]'" % (dagPath.partialPathName(), polyIter.index())
            
            # Note: UVs, normals, and colors, are "per-vertex per face", because even though two faces may share
            # a vertex, they might have different UVs, colors, or normals. So, each face has to contain this info
            # for each of it's vertices instead of each vertex alone
            Us = OpenMaya.MFloatArray()
            Vs = OpenMaya.MFloatArray()
            normals = OpenMaya.MVectorArray()
            polyIter.getUVs(Us, Vs)
            polyIter.getNormals(normals, OpenMaya.MSpace.kWorld)
            
            # Add each triangle in this poly to the global face list
            for i in range(triangleIndices.length()/3): # vertexIndices.length() has 3 values per triangle
                # Put local indices into an array for easy access
                locals = [localTriangleIndices[i*3], localTriangleIndices[i*3+1], localTriangleIndices[i*3+2]]
                
                # Using polyIter.getColors() doesn't always work - sometimes values in the return array would
                # be valid Python objects, but when used they would cause Maya to completely crash. No idea
                # why that happens, but getting the colors individually fixed the problem.
                vert0Color = OpenMaya.MColor()
                vert1Color = OpenMaya.MColor()
                vert2Color = OpenMaya.MColor()
                polyIter.getColor(vert0Color, locals[0])
                polyIter.getColor(vert1Color, locals[1])
                polyIter.getColor(vert2Color, locals[2])
                    
                # Note: Vertices are in 0,2,1 order to make CoD happy
                tris.append((
                    len(meshes)-1, # Shape index
                    materialDict[polyMaterial[0]], # Matertial index 
                    (currentStartingVertIndex + triangleIndices[i*3], currentStartingVertIndex + triangleIndices[i*3+1], currentStartingVertIndex + triangleIndices[i*3+2]), # Vert indices
                    ((Us[locals[0]], 1-Vs[locals[0]]),      (Us[locals[1]], 1-Vs[locals[1]]),       (Us[locals[2]], 1-Vs[locals[2]])),    # UVs
                    (vert0Color,                            vert1Color,                             vert2Color),                          # Colors
                    (OpenMaya.MVector(normals[locals[0]]),  OpenMaya.MVector(normals[locals[1]]),   OpenMaya.MVector(normals[locals[2]])) # Normals; Must copy the normals into a new container, because the original is destructed at the end of this poltIter iteration.
                ))
            
            # Next poly
            polyIter.next()
        
        # Update starting vertex index
        currentStartingVertIndex = len(verts)
        
        ProgressBarStep()
        
    # Error messages
    if len(meshes) == 0:
        return "No meshes selected to export."
    if len(verts) == 0:
        return "No vertices found in selected meshes."
    if len(tris) == 0:
        return "No faces found in selected meshes."
    if len(materials) == 0:
        return "No materials found on the selected meshes."
        
    # Done!
    return {"meshes": meshes, "verts": verts, "faces": tris, "materials": materials}


# EXPORT

def ExportSMDModel(filePath):
    currentunit_state = cmds.currentUnit(query=True, linear=True)
    currentangle_state = cmds.currentUnit(query=True, angle=True)
    cmds.autoKeyframe(state=False)
    cmds.currentUnit(linear="cm", angle="deg")

    numSelectedObjects = len(cmds.ls(selection=True))
    if numSelectedObjects == 0:
        return "Error: No objects selected for export"

    # Get data
    joints = GetJointList()
    if len(joints) > 128:
        print "Warning: More than 128 joints have been selected. The model might not compile."

    shapes = GetShapes(joints)
    if type(shapes) == str:
        return shapes

    # Open file
    f = None
    try:
        # Create export directory if it doesn't exist
        directory = os.path.dirname(filePath)
        if not os.path.exists(directory):
            os.makedirs(directory)
        
        # Create file
        f = open(filePath, 'w')
    except (IOError, OSError) as e:
        typex, value, traceback = sys.exc_info()
        return "Unable to create file:\n\n%s" % value.strerror

    # Write header
    f.write("// Exported with Source Maya Tools\n")
    if cmds.file(query=True, exists=True):
        f.write("// Scene: '%s'\n" % os.path.normpath(os.path.abspath(cmds.file(query=True, sceneName=True))).encode('ascii', 'ignore')) # Ignore Ascii characters using .encode()
    else:
        f.write("// Scene: Unsaved\n\n")
    f.write("version 1\n")

    f.write("nodes\n")
    if len(joints) == 0:
        f.write("0 \"tag_origin\" -1\n")
    else:
        for i, joint in enumerate(joints):
            name = joint[1].partialPathName().split("|")
            name = name[len(name)-1].split(":") # Remove namespace prefixes
            name = name[len(name)-1]
            f.write("%i \"%s\" %i\n" % (i, name, joint[0]))
    f.write("end\n")

    f.write("skeleton\n")
    f.write("time 0\n")
    if len(joints) == 0:
        f.write("0 0 0 0 0 0 0\n")
    else:
        for i, joint in enumerate(joints):
            name = joint[1].partialPathName().split("|")
            name = name[len(name)-1].split(":") # Remove namespace prefixes
            name = name[len(name)-1]
            f.write("%i  " % (i))
            WriteJointData(f, joint)
    f.write("end\n")

    f.write("triangles\n")
    verts = shapes["verts"]
    materials = shapes["materials"]
    for face in shapes["faces"]:
        f.write("%s\n" % (materials[face[1]][0].split(":")[-1]))
        for i in range(0, 3):
            f.write("0 %f %f %f %f %f %f %f %f " % (
                verts[face[2][i]][0].x*CM_TO_INCH, verts[face[2][i]][0].y*CM_TO_INCH, verts[face[2][i]][0].z*CM_TO_INCH,
                face[5][i].x, face[5][i].y, face[5][i].z,
                face[3][i][0], 1-face[3][i][1]
                ))
            f.write(" %i " % max(len(verts[face[2][i]][1]), 1))
            if len(verts[face[2][i]][1]) > 0:
                for bone in verts[face[2][i]][1]:
                    f.write(" %i %f " % (bone[0], bone[1]))
            else:
                f.write(" 0 1.000000 ")
            f.write("\n")
    f.write("end\n")

    f.close()

    cmds.currentUnit(linear=currentunit_state, angle=currentangle_state)

def ExportSMDAnim(filePath):
    currentunit_state = cmds.currentUnit(query=True, linear=True)
    currentangle_state = cmds.currentUnit(query=True, angle=True)
    cmds.autoKeyframe(state=False)
    cmds.currentUnit(linear="cm", angle="deg")

    numSelectedObjects = len(cmds.ls(selection=True))
    if numSelectedObjects == 0:
        return "Error: No objects selected for export"

    # Get data
    joints = GetJointList()
    if len(joints) == 0:
        return "Error: No joints selected for export"
    if len(joints) > 128:
        print "Warning: More than 128 joints have been selected. The animation might not compile."

    frameStart = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameStartField", query=True, value=True)
    frameEnd = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameEndField", query=True, value=True)

    # Open file
    f = None
    try:
        # Create export directory if it doesn't exist
        directory = os.path.dirname(filePath)
        if not os.path.exists(directory):
            os.makedirs(directory)
        
        # Create file
        f = open(filePath, 'w')
    except (IOError, OSError) as e:
        typex, value, traceback = sys.exc_info()
        return "Unable to create file:\n\n%s" % value.strerror

    # Write header
    f.write("// Exported with Source Maya Tools\n")
    if cmds.file(query=True, exists=True):
        f.write("// Scene: '%s'\n" % os.path.normpath(os.path.abspath(cmds.file(query=True, sceneName=True))).encode('ascii', 'ignore')) # Ignore Ascii characters using .encode()
    else:
        f.write("// Scene: Unsaved\n\n")
    f.write("version 1\n")

    f.write("nodes\n")
    if len(joints) == 0:
        f.write("0 \"tag_origin\" -1\n")
    else:
        for i, joint in enumerate(joints):
            name = joint[1].partialPathName().split("|")
            name = name[len(name)-1].split(":") # Remove namespace prefixes
            name = name[len(name)-1]
            f.write("%i \"%s\" %i\n" % (i, name, joint[0]))
    f.write("end\n")

    f.write("skeleton\n")
    for i in range(int(frameStart), int(frameEnd+1)):
        f.write("time %i\n" % (i - frameStart)) 
        cmds.currentTime(i)
        if len(joints) == 0:
            f.write("0 0 0 0 0 0 0\n")
        else:
            for i, joint in enumerate(joints):
                name = joint[1].partialPathName().split("|")
                name = name[len(name)-1].split(":") # Remove namespace prefixes
                name = name[len(name)-1]
                f.write("%i  " % (i))
                WriteJointData(f, joint)
    f.write("end\n")

    f.close()

    cmds.currentUnit(linear=currentunit_state, angle=currentangle_state)

def GetRootFolder(firstTimePrompt=False, category="none"):
    SrcRootPath = ""
    
    try:
        storageKey = reg.OpenKey(GLOBAL_STORAGE_REG_KEY[0], GLOBAL_STORAGE_REG_KEY[1])
        SrcRootPath = reg.QueryValueEx(storageKey, "RootPath")[0]
        reg.CloseKey(storageKey)
    except WindowsError:
        # First time, create key
        storageKey = reg.CreateKey(GLOBAL_STORAGE_REG_KEY[0], GLOBAL_STORAGE_REG_KEY[1])
        reg.SetValueEx(storageKey, "RootPath", 0, reg.REG_SZ, "")
        reg.CloseKey(storageKey)
        
    if not os.path.isdir(SrcRootPath):
        SrcRootPath = ""
        
    return SrcRootPath  

def SetRootFolder(msg=None, game="none"):
    #if game == "none":
    #   game = currentGame
    #if game == "none":
    #   res = cmds.confirmDialog(message="Please select the game you're working with", button=['OK'], defaultButton='OK', title="WARNING")
    #   return None
    # Get current root folder (this also makes sure the reg key exists)
    srcRootPath = GetRootFolder(False, game)
    
    # Open input box
    #if cmds.promptDialog(title="Set Root Path", message=msg or "Change your root path:\t\t\t", text=srcRootPath) != "Confirm":
    #   return None
    
    srcRootPath = cmds.fileDialog2(fileMode=3, dialogStyle=2)[0] + "/"
    
    # Check to make sure the path exists
    if not os.path.isdir(srcRootPath):
        MessageBox("Given root path does not exist")
        return None
        
    # cmds.promptDialog(title="Set Root Path", message=srcRootPath)
    # Set path
    # , 0, reg.KEY_SET_VALUE)
    storageKey = reg.OpenKey(GLOBAL_STORAGE_REG_KEY[0], GLOBAL_STORAGE_REG_KEY[1], 0, reg.KEY_SET_VALUE)
    reg.SetValueEx(storageKey, "RootPath", 0, reg.REG_SZ, srcRootPath)
    reg.CloseKey(storageKey)
    
    return srcRootPath


# Windows

# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------------------- XModel Export Window ----------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------        
def CreateSMDModelWindow():
    # Create window
    if cmds.control(OBJECT_NAMES['smdmodel'][0], exists=True):
        cmds.deleteUI(OBJECT_NAMES['smdmodel'][0])
    
    cmds.window(OBJECT_NAMES['smdmodel'][0], title=OBJECT_NAMES['smdmodel'][1], width=340, height=1, retain=True, maximizeButton=False)
    form = cmds.formLayout(OBJECT_NAMES['smdmodel'][0]+"_Form")
    
    # Controls
    slotDropDown = cmds.optionMenu(OBJECT_NAMES['smdmodel'][0]+"_SlotDropDown", changeCommand=lambda x:RefreshXModelWindow(), annotation="Each slot contains different a export path, settings, and saved selection")
    for i in range(1, EXPORT_WINDOW_NUMSLOTS+1):
        cmds.menuItem(OBJECT_NAMES['smdmodel'][0]+"_SlotDropDown"+("_s%i" % i), label="Slot %i" % i)
    
    separator1 = cmds.separator(style='in', height=16)
    separator2 = cmds.separator(style='in')
    
    saveToLabel = cmds.text(label="Save to:", annotation="This is where the .xmodel_export is saved to")
    saveToField = cmds.textField(OBJECT_NAMES['smdmodel'][0]+"_SaveToField", height=21, changeCommand=lambda x:GeneralWindow_SaveToField('xmodel'), annotation="This is where the .xmodel_export is saved to")
    fileBrowserButton = cmds.button(label="...", height=21, command=lambda x:GeneralWindow_FileBrowser('smdmodel', "SMD File (*.smd)"), annotation="Open a file browser dialog")
    
    exportSelectedButton = cmds.button(label="Export Selected", command=lambda x:GeneralWindow_ExportSelected('smdmodel', False), annotation="Export all currently selected objects from the scene (current frame)\nWarning: Will automatically overwrite if the export path if it already exists")
    saveSelectionButton = cmds.button(label="Save Selection", command=lambda x:GeneralWindow_SaveSelection('smdmodel'), annotation="Save the current object selection")
    getSavedSelectionButton = cmds.button(label="Get Saved Selection", command=lambda x:GeneralWindow_GetSavedSelection('smdmodel'), annotation="Reselect the saved selection")
    
    exportMultipleSlotsButton = cmds.button(label="Export Multiple Slots", command=lambda x:GeneralWindow_ExportMultiple('smdmodel'), annotation="Automatically export multiple slots at once, using each slot's saved selection")
    exportInMultiExportCheckbox = cmds.checkBox(OBJECT_NAMES['smdmodel'][0]+"_UseInMultiExportCheckBox", label="Use current slot for Export Multiple", changeCommand=lambda x:GeneralWindow_ExportInMultiExport('smdmodel'), annotation="Check this make the 'Export Multiple Slots' button export this slot")

    # Setup form
    cmds.formLayout(form, edit=True,
        attachForm=[(slotDropDown, 'top', 6), (slotDropDown, 'left', 10), (slotDropDown, 'right', 10),
                    (separator1, 'left', 0), (separator1, 'right', 0),
                    (separator2, 'left', 0), (separator2, 'right', 0),
                    (saveToLabel, 'left', 12),
                    (fileBrowserButton, 'right', 10),
                    (exportMultipleSlotsButton, 'bottom', 6), (exportMultipleSlotsButton, 'left', 10),
                    (exportInMultiExportCheckbox, 'bottom', 9), (exportInMultiExportCheckbox, 'right', 6),
                    (exportSelectedButton, 'left', 10),
                    (saveSelectionButton, 'right', 10)],
                    #(exportSelectedButton, 'bottom', 6), (exportSelectedButton, 'left', 10),
                    #(saveSelectionButton, 'bottom', 6), (saveSelectionButton, 'right', 10),
                    #(getSavedSelectionButton, 'bottom', 6)],
        
        attachControl=[ (separator1, 'top', 0, slotDropDown),
                        (saveToLabel, 'bottom', 9, exportSelectedButton),
                        (saveToField, 'bottom', 5, exportSelectedButton), (saveToField, 'left', 5, saveToLabel), (saveToField, 'right', 5, fileBrowserButton),
                        (fileBrowserButton, 'bottom', 5, exportSelectedButton),
                        (exportSelectedButton, 'bottom', 5, separator2),
                        (saveSelectionButton, 'bottom', 5, separator2),
                        (getSavedSelectionButton, 'bottom', 5, separator2), (getSavedSelectionButton, 'right', 10, saveSelectionButton),
                        (separator2, 'bottom', 5, exportMultipleSlotsButton)])

def RefreshSMDModelWindow():
    # Refresh/create node
    if len(cmds.ls(OBJECT_NAMES['smdmodel'][2])) == 0:
        cmds.createNode("renderLayer", name=OBJECT_NAMES['smdmodel'][2], skipSelect=True)
    
    cmds.lockNode(OBJECT_NAMES['smdmodel'][2], lock=False)
    
    if not cmds.attributeQuery("slot", node=OBJECT_NAMES['smdmodel'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdmodel'][2], longName="slot", attributeType='short', defaultValue=1)
    if not cmds.attributeQuery("paths", node=OBJECT_NAMES['smdmodel'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdmodel'][2], longName="paths", multi=True, dataType='string')
        cmds.setAttr(OBJECT_NAMES['smdmodel'][2]+".paths", size=EXPORT_WINDOW_NUMSLOTS)
    if not cmds.attributeQuery("selections", node=OBJECT_NAMES['smdmodel'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdmodel'][2], longName="selections", multi=True, dataType='stringArray')
        cmds.setAttr(OBJECT_NAMES['smdmodel'][2]+".selections", size=EXPORT_WINDOW_NUMSLOTS)
    if not cmds.attributeQuery("useinmultiexport", node=OBJECT_NAMES['smdmodel'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdmodel'][2], longName="useinmultiexport", multi=True, attributeType='bool', defaultValue=False)
        cmds.setAttr(OBJECT_NAMES['smdmodel'][2]+".useinmultiexport", size=EXPORT_WINDOW_NUMSLOTS)
        
    cmds.lockNode(OBJECT_NAMES['smdmodel'][2], lock=True)
    
    # Set values
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdmodel'][0]+"_SlotDropDown", query=True, select=True)
    path = cmds.getAttr(OBJECT_NAMES['smdmodel'][2]+(".paths[%i]" % slotIndex))
    cmds.setAttr(OBJECT_NAMES['smdmodel'][2]+".slot", slotIndex)
    cmds.textField(OBJECT_NAMES['smdmodel'][0]+"_SaveToField", edit=True, fileName=path)

    useInMultiExport = cmds.getAttr(OBJECT_NAMES['smdmodel'][2]+(".useinmultiexport[%i]" % slotIndex))
    cmds.checkBox(OBJECT_NAMES['smdmodel'][0]+"_UseInMultiExportCheckBox", edit=True, value=useInMultiExport)


# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------- XAnim Export Window ----------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------    
def CreateSMDAnimWindow():
    # Create window
    if cmds.control(OBJECT_NAMES['smdanim'][0], exists=True):
        cmds.deleteUI(OBJECT_NAMES['smdanim'][0])
    
    cmds.window(OBJECT_NAMES['smdanim'][0], title=OBJECT_NAMES['smdanim'][1], width=1, height=1, retain=True, maximizeButton=False)
    form = cmds.formLayout(OBJECT_NAMES['smdanim'][0]+"_Form")
    
    # Controls
    slotDropDown = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", changeCommand=lambda x:RefreshSMDAnimWindow(), annotation="Each slot contains different a export path, frame range, notetrack, and saved selection")
    for i in range(1, EXPORT_WINDOW_NUMSLOTS+1):
        cmds.menuItem(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown"+("_s%i" % i), label="Slot %i" % i)
    
    separator1 = cmds.separator(style='in')
    separator2 = cmds.separator(style='in')
    separator3 = cmds.separator(style='in')
    
    framesLabel = cmds.text(label="Frames:", annotation="Range of frames to export")
    framesStartField = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameStartField", height=21, width=35, minValue=0, changeCommand=SMDAnimWindow_UpdateFrameRange, annotation="Starting frame to export (inclusive)")
    framesToLabel = cmds.text(label="to")
    framesEndField = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameEndField", height=21, width=35, minValue=0, changeCommand=SMDAnimWindow_UpdateFrameRange, annotation="Ending frame to export (inclusive)")

    saveToLabel = cmds.text(label="Save to:", annotation="This is where .smd is saved to")
    saveToField = cmds.textField(OBJECT_NAMES['smdanim'][0]+"_SaveToField", height=21, changeCommand=lambda x:GeneralWindow_SaveToField('smdanim'), annotation="This is where .xanim_export is saved to")
    fileBrowserButton = cmds.button(label="...", height=21, command=lambda x:GeneralWindow_FileBrowser('smdanim', "SMD File (*.smd)"), annotation="Open a file browser dialog")
    
    exportSelectedButton = cmds.button(label="Export Selected", command=lambda x:GeneralWindow_ExportSelected('smdanim', False), annotation="Export all currently selected joints from the scene (specified frames)\nWarning: Will automatically overwrite if the export path if it already exists")
    saveSelectionButton = cmds.button(label="Save Selection", command=lambda x:GeneralWindow_SaveSelection('smdanim'), annotation="Save the current object selection")
    getSavedSelectionButton = cmds.button(label="Get Saved Selection", command=lambda x:GeneralWindow_GetSavedSelection('smdanim'), annotation="Reselect the saved selection")
    
    exportMultipleSlotsButton = cmds.button(label="Export Multiple Slots", command=lambda x:GeneralWindow_ExportMultiple('smdanim'), annotation="Automatically export multiple slots at once, using each slot's saved selection")
    exportInMultiExportCheckbox = cmds.checkBox(OBJECT_NAMES['smdanim'][0]+"_UseInMultiExportCheckBox", label="Use current slot for Export Multiple", changeCommand=lambda x:GeneralWindow_ExportInMultiExport('smdanim'), annotation="Check this make the 'Export Multiple Slots' button export this slot")
    # Setup form
    cmds.formLayout(form, edit=True,
        attachForm=[(slotDropDown, 'top', 6), (slotDropDown, 'left', 10), (slotDropDown, 'right', 10),
                    (separator1, 'left', 0), (separator1, 'right', 0),
                    (framesLabel, 'left', 10),
                    (separator2, 'left', 0), (separator2, 'right', 0),
                    (saveToLabel, 'left', 12),
                    (fileBrowserButton, 'right', 10),
                    (exportMultipleSlotsButton, 'bottom', 6), (exportMultipleSlotsButton, 'left', 10),
                    (exportInMultiExportCheckbox, 'bottom', 9), (exportInMultiExportCheckbox, 'right', 6),
                    (exportSelectedButton, 'left', 10),
                    (saveSelectionButton, 'right', 10),
                    (separator3, 'left', 0), (separator3, 'right', 0)],
        
        attachControl=[ (separator1, 'top', 6, slotDropDown),
                        (framesLabel, 'top', 8, separator1),
                        (framesStartField, 'top', 5, separator1), (framesStartField, 'left', 4, framesLabel),
                        (framesToLabel, 'top', 8, separator1), (framesToLabel, 'left', 4+35+4, framesLabel),
                        (framesEndField, 'top', 5, separator1), (framesEndField, 'left', 4, framesToLabel),
                        (separator2, 'bottom', 5, fileBrowserButton),
                        (saveToLabel, 'bottom', 10, exportSelectedButton),
                        (saveToField, 'bottom', 5, exportSelectedButton), (saveToField, 'left', 5, saveToLabel), (saveToField, 'right', 5, fileBrowserButton),
                        (fileBrowserButton, 'bottom', 5, exportSelectedButton),
                        (exportSelectedButton, 'bottom', 5, separator3),
                        (saveSelectionButton, 'bottom', 5, separator3),
                        (getSavedSelectionButton, 'bottom', 5, separator3), (getSavedSelectionButton, 'right', 10, saveSelectionButton),
                        (separator3, 'bottom', 5, exportMultipleSlotsButton)
                        ])

def SMDAnimWindow_UpdateFrameRange(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    start = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameStartField", query=True, value=True)
    end = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameEndField", query=True, value=True)
    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".frameRanges[%i]" % slotIndex), start, end, type='long2')

def SMDAnimWindow_UpdateFramerate(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    fps = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FPSField", query=True, value=True)
    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".framerate[%i]" % slotIndex), fps)

def SMDAnimWindow_UpdateMultiplier(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    fps = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_qualityField", query=True, value=True)
    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".multiplier[%i]" % slotIndex), fps)

def SMDAnimWindow_AddNote(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    if cmds.promptDialog(title="Add Note to Slot %i's Notetrack" % slotIndex, message="Enter the note's name:\t\t  ") != "Confirm":
        return
    
    userInput = cmds.promptDialog(query=True, text=True)
    noteName = "".join([c for c in userInput if c.isalnum() or c=="_"]) # Remove all non-alphanumeric characters
    if noteName == "":
        MessageBox("Invalid note name")
        return
        
    existingItems = cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", query=True, allItems=True)
    
    if existingItems != None and noteName in existingItems:
        MessageBox("A note with this name already exists")
        
    noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
    noteList += "%s:%i," % (noteName, cmds.currentTime(query=True))
    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
    
    cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, append=noteName, selectIndexedItem=len((existingItems or []))+1)
    SMDAnimWindow_SelectNote()

def ReadSMDAnimNotes(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    existingItems = cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", query=True, allItems=True)
    noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""

    isWraithAnim = False
    isSEAnim = False

    isNotWraithAnimButHasNoteTrack = False
    
    if cmds.objExists('WraithNotes'):
        isWraithAnim = True
        
    if cmds.objExists('SENotes'):
        isSEAnim = True

    if cmds.objExists('NoteTrack'):
        isNotWraithAnimButHasNoteTrack = True

    if cmds.objExists('WraithNotes') and cmds.objExists('NoteTrack'):
        cmds.confirmDialog( title='ERROR', message='WraithNotes and NoteTrack both exist in this scene, please delete one and try again.' , button=['Ok'], defaultButton='Ok')
        return


    if isSEAnim:
        cmds.select( clear=True )
        cmds.select( 'SENotes', hi=True )
        cmds.select( 'SENotes', d=True ) 

        notes = cmds.ls( selection=True ) # Grab what is selected.

        for NoteTrack in notes: # Go through each one.
            if not "Shape" in NoteTrack: # Avoid ones with Shape at end.
                for note in cmds.keyframe(NoteTrack, attribute="translateX", sl=False, q=True, tc=True): # See where are the keyframes.
                    IsUneededNote = ( # If you find a Note that is not needed in WaW and you want to remove it from further anims add it here:
                                        NoteTrack == "reload_large" 
                                     or NoteTrack == "reload_small" 
                                     or NoteTrack == "reload_medium"
                                     or NoteTrack == "clip_out"
                                     or NoteTrack == "clip_in"
                                     or NoteTrack == "rechamber_release"
                                     or NoteTrack == "rechamber_pull_back"
                                     or NoteTrack == "end" # This will cause an error in converter, but might be needed for BO3, appears to be on ALL anims.

                                    )
                    if cmds.checkBox("Scoba_IgnoreUslessNotes", query=True, value=True) and IsUneededNote:
                        continue
                    noteList += "%s:%i," % (NoteTrack, note) # Add Notes to Aidan's list.
                    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
                    cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, append=NoteTrack, selectIndexedItem=len((existingItems or []))+1)
    
    elif isWraithAnim:
        cmds.select( clear=True )
        cmds.select( 'WraithNotes', hi=True )
        cmds.select( 'WraithNotes', d=True ) # Select WraithNotes and it's children and then deselect it to avoid issues.

        notes = cmds.ls( selection=True ) # Grab what is selected.

        for NoteTrack in notes: # Go through each one.
            if not "Shape" in NoteTrack: # Avoid ones with Shape at end.
                for note in cmds.keyframe(NoteTrack, attribute="translateX", sl=False, q=True, tc=True): # See where are the keyframes.
                    IsUneededNote = ( # If you find a Note that is not needed in WaW and you want to remove it from further anims add it here:
                                        NoteTrack == "reload_large" 
                                     or NoteTrack == "reload_small" 
                                     or NoteTrack == "reload_medium"
                                     or NoteTrack == "clip_out"
                                     or NoteTrack == "clip_in"
                                     or NoteTrack == "rechamber_release"
                                     or NoteTrack == "rechamber_pull_back"
                                     or NoteTrack == "end" # This will cause an error in converter, but might be needed for BO3, appears to be on ALL anims.

                                    )
                    if cmds.checkBox("Scoba_IgnoreUslessNotes", query=True, value=True) and IsUneededNote:
                        continue
                    noteList += "%s:%i," % (NoteTrack, note) # Add Notes to Aidan's list.
                    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
                    cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, append=NoteTrack, selectIndexedItem=len((existingItems or []))+1)
    elif isNotWraithAnimButHasNoteTrack:
        for note in cmds.keyframe("NoteTrack", attribute="MainNote", sl=False, q=True, tc=True): # cmds.keyframe("NoteTrack", attribute="MainNote", sl=False, q=True, tc=True) lists all the keyframes for this object's attribute, so we loop through it.
            noteName =  cmds.getAttr('NoteTrack.MainNote',x=True, asString=True, t=note) # Here is where we grab the Note from the attribute "MainNote", asString allows us to return it as string instead of intiger.
            IsUneededNote = ( # If you find a Note that is not needed in WaW and you want to remove it from further anims add it here:
                                noteName == "reload_large" 
                             or noteName == "reload_small" 
                             or noteName == "reload_medium"
                             or noteName == "clip_out"
                             or noteName == "clip_in"
                             or noteName == "rechamber_release"
                             or noteName == "rechamber_pull_back"
                             or noteName == "end" # This will cause an error in converter, but might be needed for BO3, appears to be on ALL anims.
                            )
            if cmds.checkBox("Scoba_IgnoreUslessNotes", query=True, value=True) and IsUneededNote:
                continue
            if "sndnt#" in noteName:
                noteName = noteName[6:] # This essentially, in laymans terms, strips the notetrack's name of the first 6 characters if it contains "sndnt#" in the name.
            if "rmbnt#" in noteName:
                noteName = noteName[6:]
            noteList += "%s:%i," % (noteName, note) # Add Notes to Aidan's list.
            cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
            cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, append=noteName, selectIndexedItem=len((existingItems or []))+1)
    else:
        cmds.confirmDialog( title='ERROR', message='Can\'t find Notetracks for Wriath Anim or Normal anim.' , button=['Ok'], defaultButton='Ok') 

    SMDAnimWindow_SelectNote()


def RenameSMDAnimNotes(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    currentIndex = cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", query=True, selectIndexedItem=True)
    if currentIndex != None and len(currentIndex) > 0 and currentIndex[0] >= 1:
        if cmds.promptDialog(title="Rename NoteTrack in slot", message="Enter new notetrack name:\t\t  ") != "Confirm":
            return
    
        userInput = cmds.promptDialog(query=True, text=True)
        noteName = "".join([c for c in userInput if c.isalnum() or c=="_"]) # Remove all non-alphanumeric characters
        if noteName == "":
            MessageBox("Invalid note name")
            return
        currentIndex = currentIndex[0]
        noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
        notes = noteList.split(",")
        noteInfo = notes[currentIndex-1].split(":")
        note = int(noteInfo[1])
        NoteTrack = userInput
        
        # REMOVE NOTE

        cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, removeIndexedItem=currentIndex)
        noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
        notes = noteList.split(",")
        del notes[currentIndex-1]
        noteList = ",".join(notes)
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')

        # REMOVE NOTE
        noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
        noteList += "%s:%i," % (NoteTrack, note) # Add Notes to Aidan's list.
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
        cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, append=NoteTrack, selectIndexedItem=currentIndex)
        SMDAnimWindow_SelectNote()


    
def SMDAnimWindow_RemoveNote(required_parameter):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    currentIndex = cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", query=True, selectIndexedItem=True)
    if currentIndex != None and len(currentIndex) > 0 and currentIndex[0] >= 1:
        currentIndex = currentIndex[0]
        cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", edit=True, removeIndexedItem=currentIndex)
        noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
        notes = noteList.split(",")
        del notes[currentIndex-1]
        noteList = ",".join(notes)
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
        SMDAnimWindow_SelectNote()
        
def SMDAnimWindow_UpdateNoteFrame(newFrame):
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    currentIndex = cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", query=True, selectIndexedItem=True)
    if currentIndex != None and len(currentIndex) > 0 and currentIndex[0] >= 1:
        currentIndex = currentIndex[0]
        noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
        notes = noteList.split(",")
        parts = notes[currentIndex-1].split(":")
        if len(parts) < 2:
            error("Error parsing notetrack string (A) at %i: %s" % (currentIndex, noteList))
        notes[currentIndex-1] = "%s:%i" % (parts[0], newFrame)
        noteList = ",".join(notes)
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex), noteList, type='string')
        
def SMDAnimWindow_SelectNote():
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)
    currentIndex = cmds.textScrollList(OBJECT_NAMES['smdanim'][0]+"_NoteList", query=True, selectIndexedItem=True)
    if currentIndex != None and len(currentIndex) > 0 and currentIndex[0] >= 1:
        currentIndex = currentIndex[0]
        noteList = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".notetracks[%i]" % slotIndex)) or ""
        notes = noteList.split(",")
        parts = notes[currentIndex-1].split(":")
        if len(parts) < 2:
            error("Error parsing notetrack string (B) at %i: %s" % (currentIndex, noteList))
            
        frame=0
        try: 
            frame = int(parts[1])
        except ValueError:
            pass
            
        noteFrameField = cmds.intField(OBJECT_NAMES['smdanim'][0]+"_NoteFrameField", edit=True, value=frame)
        
def RefreshSMDAnimWindow():
    # Refresh/create node
    if len(cmds.ls(OBJECT_NAMES['smdanim'][2])) == 0:
        cmds.createNode("renderLayer", name=OBJECT_NAMES['smdanim'][2], skipSelect=True)
    
    cmds.lockNode(OBJECT_NAMES['smdanim'][2], lock=False)
    
    if not cmds.attributeQuery("slot", node=OBJECT_NAMES['smdanim'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdanim'][2], longName="slot", attributeType='short', defaultValue=1)
    if not cmds.attributeQuery("paths", node=OBJECT_NAMES['smdanim'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdanim'][2], longName="paths", multi=True, dataType='string')
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+".paths", size=EXPORT_WINDOW_NUMSLOTS)
    if not cmds.attributeQuery("selections", node=OBJECT_NAMES['smdanim'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdanim'][2], longName="selections", multi=True, dataType='stringArray')
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+".selections", size=EXPORT_WINDOW_NUMSLOTS)
    if not cmds.attributeQuery("frameRanges", node=OBJECT_NAMES['smdanim'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdanim'][2], longName="frameRanges", multi=True, dataType='long2')
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+".frameRanges", size=EXPORT_WINDOW_NUMSLOTS)
    if not cmds.attributeQuery("useinmultiexport", node=OBJECT_NAMES['smdanim'][2], exists=True):
        cmds.addAttr(OBJECT_NAMES['smdanim'][2], longName="useinmultiexport", multi=True, attributeType='bool', defaultValue=False)
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+".useinmultiexport", size=EXPORT_WINDOW_NUMSLOTS)
    
    cmds.lockNode(OBJECT_NAMES['smdanim'][2], lock=True)
    
    # Set values
    slotIndex = cmds.optionMenu(OBJECT_NAMES['smdanim'][0]+"_SlotDropDown", query=True, select=True)  
    cmds.setAttr(OBJECT_NAMES['smdanim'][2]+".slot", slotIndex)
    
    path = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".paths[%i]" % slotIndex))
    cmds.textField(OBJECT_NAMES['smdanim'][0]+"_SaveToField", edit=True, fileName=path)
    
    frameRange = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".frameRanges[%i]" % slotIndex))
    if frameRange == None:
        cmds.setAttr(OBJECT_NAMES['smdanim'][2]+(".frameRanges[%i]" % slotIndex), 0, 0, type='long2')
        cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameStartField", edit=True, value=0)
        cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameEndField", edit=True, value=0)
    else:
        cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameStartField", edit=True, value=frameRange[0][0])
        cmds.intField(OBJECT_NAMES['smdanim'][0]+"_FrameEndField", edit=True, value=frameRange[0][1])
    
        
    useInMultiExport = cmds.getAttr(OBJECT_NAMES['smdanim'][2]+(".useinmultiexport[%i]" % slotIndex))
    cmds.checkBox(OBJECT_NAMES['smdanim'][0]+"_UseInMultiExportCheckBox", edit=True, value=useInMultiExport)
    

# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# --------------------------------------------------------------------------- General GUI --------------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
def SaveReminder(allowUnsaved=True):
    if cmds.file(query=True, modified=True):
        if cmds.file(query=True, exists=True):
            result = cmds.confirmDialog(message="Save changes to %s?" % cmds.file(query=True, sceneName=True), button=["Yes", "No", "Cancel"], defaultButton="Yes", title="Save Changes")
            if result == "Yes":
                cmds.file(save=True)
            elif result != "No":
                return False
        else: # The file has never been saved (has no name)
            if allowUnsaved:
                result = cmds.confirmDialog(message="The current scene is not saved. Continue?", button=["Yes", "No"], defaultButton="Yes", title="Save Changes")
                if result != "Yes":
                    return False
            else:
                MessageBox("The scene needs to be saved first")
                return False
                
    return True

def PrintWarning(message):
    global WarningsDuringExport
    if WarningsDuringExport < MAX_WARNINGS_SHOWN:
        print "WARNING: %s" % message
        WarningsDuringExport += 1
    elif WarningsDuringExport == MAX_WARNINGS_SHOWN:
        print "More warnings not shown because printing text is slow...\n"
        WarningsDuringExport = MAX_WARNINGS_SHOWN+1

def MessageBox(message):
    cmds.confirmDialog(message=message, button='OK', defaultButton='OK', title=OBJECT_NAMES['menu'][1])
        
def ShowWindow(windowID):
    exec(OBJECT_NAMES[windowID][3] + "()") # Refresh window
    cmds.showWindow(OBJECT_NAMES[windowID][0])

def ProgressBarStep():
    cmds.progressBar(OBJECT_NAMES['progress'][0], edit=True, step=1)

def AboutWindow():
    result = cmds.confirmDialog(message="Source Engine Tools for Maya, created by Maciej Ray Marcin (based on CoDMayaTools).\n\nThis script is under the GNU General Public License. You may modify or redistribute this script, however it comes with no warranty. Go to http://www.gnu.org/licenses/ for more details.", button=['OK'], defaultButton='OK', title="About Source Maya Tools")

# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# ---------------------------------------------------------------------- General Export Window ---------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# GeneralWindow_... are callback functions that are used by both export windows
def GeneralWindow_SaveToField(windowID):
    slotIndex = cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", query=True, select=True)
    filePath = cmds.textField(OBJECT_NAMES[windowID][0]+"_SaveToField", query=True, fileName=True)
    cmds.setAttr(OBJECT_NAMES[windowID][2]+(".paths[%i]" % slotIndex), filePath, type='string')
    
def GeneralWindow_FileBrowser(windowID, formatExtension):
    defaultFolder = GetRootFolder()
    saveTo = cmds.fileDialog2(fileMode=0, fileFilter=formatExtension, caption="Export To", startingDirectory=defaultFolder)
    if saveTo == None or len(saveTo) == 0 or saveTo[0].strip() == "":
        return
    saveTo = saveTo[0].strip()
    
    cmds.textField(OBJECT_NAMES[windowID][0]+"_SaveToField", edit=True, fileName=saveTo)
    GeneralWindow_SaveToField(windowID)

def GeneralWindow_SaveSelection(windowID):
    slotIndex = cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", query=True, select=True)
    selection = cmds.ls(selection=True)
    if selection == None or len(selection) == 0:
        return
    cmds.setAttr(OBJECT_NAMES[windowID][2]+(".selections[%i]" % slotIndex), len(selection), *selection, type='stringArray')
    
def GeneralWindow_GetSavedSelection(windowID):
    slotIndex = cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", query=True, select=True)
    selection = cmds.getAttr(OBJECT_NAMES[windowID][2]+(".selections[%i]" % slotIndex))
    
    validSelection = []
    for obj in selection:
        if cmds.objExists(obj):
            validSelection.append(obj)
    
    # Remove non-existing objects from the saved list
    cmds.setAttr(OBJECT_NAMES[windowID][2]+(".selections[%i]" % slotIndex), len(validSelection), *validSelection, type='stringArray')
    
    if validSelection == None or len(validSelection) == 0:
        MessageBox("No selection saved to slot %i" % slotIndex)
        return False
    
    cmds.select(validSelection)
    return True

def GeneralWindow_ExportSelected(windowID, exportingMultiple):
    global WarningsDuringExport
    
    slotIndex = cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", query=True, select=True)
    
    # Get path
    filePath = cmds.textField(OBJECT_NAMES[windowID][0]+"_SaveToField", query=True, fileName=True)
    if filePath.strip() == "":
        if exportingMultiple:
            MessageBox("Invalid path on slot %i:\n\nPath is empty." % slotIndex)
        else:
            MessageBox("Invalid path:\n\nPath is empty.")
        return
        
    if os.path.isdir(filePath):
        if exportingMultiple:
            MessageBox("Invalid path on slot %i:\n\nPath points to an existing directory." % slotIndex)
        else:
            MessageBox("Invalid path:\n\nPath points to an existing directory.")
        return
        
    # Save reminder
    if not exportingMultiple and not SaveReminder():
        return
    
    # Progress bar
    if cmds.control("w"+OBJECT_NAMES['progress'][0], exists=True):
        cmds.deleteUI("w"+OBJECT_NAMES['progress'][0])
    progressWindow = cmds.window("w"+OBJECT_NAMES['progress'][0], title=OBJECT_NAMES['progress'][1], width=302, height=22)
    cmds.columnLayout()
    progressControl = cmds.progressBar(OBJECT_NAMES['progress'][0], width=300)
    cmds.showWindow(progressWindow)
    cmds.refresh() # Force the progress bar to be drawn
    
    # Export
    if not exportingMultiple:
        WarningsDuringExport = 0
    response = None
    try:
        exec("response = %s(\"%s\")" % (OBJECT_NAMES[windowID][4], filePath))
    except Exception as e:
        response = "An unhandled error occurred during export:\n\n" + traceback.format_exc()
    
    # Delete progress bar
    cmds.deleteUI(progressWindow, window=True)
    
    # Handle response
    
    if type(response) == str or type(response) == unicode:
        if exportingMultiple:
            MessageBox("Slot %i\n\n%s" % (slotIndex, response))
        else:
            MessageBox(response)
    elif WarningsDuringExport > 0 and not exportingMultiple:
        MessageBox("Warnings occurred during export. Check the script editor output for more details.")

def GeneralWindow_ExportMultiple(windowID):
    originalSlotIndex = cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", query=True, select=True)
    any = False
    for i in range(1, EXPORT_WINDOW_NUMSLOTS+1):
        useInMultiExport = cmds.getAttr(OBJECT_NAMES[windowID][2]+(".useinmultiexport[%i]" % i))
        if useInMultiExport:
            any = True
            break
    
    if not any:
        MessageBox("No slots set to export.")
        return
    
    if not SaveReminder():
        return
        
    WarningsDuringExport = 0
    originalSelection = cmds.ls(selection=True)
    
    for i in range(1, EXPORT_WINDOW_NUMSLOTS+1):
        useInMultiExport = cmds.getAttr(OBJECT_NAMES[windowID][2]+(".useinmultiexport[%i]" % i))
        if useInMultiExport:
            print "Exporting slot %i in multiexport" % i
            cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", edit=True, select=i)
            exec(OBJECT_NAMES[windowID][3] + "()") # Refresh window
            if GeneralWindow_GetSavedSelection(windowID):
                GeneralWindow_ExportSelected(windowID, True)
    
    if originalSelection == None or len(originalSelection) == 0:
        cmds.select(clear=True)
    else:
        cmds.select(originalSelection)
    
    if WarningsDuringExport > 0:
        MessageBox("Warnings occurred during export. Check the script editor output for more details.")         
    
    # Reset slot
    cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", edit=True, select=originalSlotIndex)
    exec(OBJECT_NAMES[windowID][3] + "()") # Refresh window
    
def GeneralWindow_ExportInMultiExport(windowID):
    slotIndex = cmds.optionMenu(OBJECT_NAMES[windowID][0]+"_SlotDropDown", query=True, select=True)
    useInMultiExport = cmds.checkBox(OBJECT_NAMES[windowID][0]+"_UseInMultiExportCheckBox", query=True, value=True)
    cmds.setAttr(OBJECT_NAMES[windowID][2]+(".useinmultiexport[%i]" % slotIndex), useInMultiExport)

def ExportAll():
    GeneralWindow_ExportMultiple('smdmodel')
    GeneralWindow_ExportMultiple('smdanim')

# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
# ------------------------------------------------------------------------------ Init ------------------------------------------------------------------------------
# ------------------------------------------------------------------------------------------------------------------------------------------------------------------
def CreateMenu():
    cmds.setParent(mel.eval("$temp1=$gMainWindow"))

    if cmds.control(OBJECT_NAMES['menu'][0], exists=True):
        cmds.deleteUI(OBJECT_NAMES['menu'][0], menu=True)

    menu = cmds.menu(OBJECT_NAMES['menu'][0], label=OBJECT_NAMES['menu'][1], tearOff=True)

    # Export tools
    cmds.menuItem(label=OBJECT_NAMES['smdmodel'][1]+"...", command=lambda x:ShowWindow('smdmodel'))
    cmds.menuItem(label=OBJECT_NAMES['smdanim'][1]+"...", command=lambda x:ShowWindow('smdanim'))
    cmds.menuItem(label="Export All", command=lambda x:ExportAll())

    # Root folder
    cmds.menuItem(divider=True)
    cmds.menuItem(label="Set Model Source Folder", command=lambda x:SetRootFolder(None))

    # For easy script updating
    cmds.menuItem(label="Reload Script", command="reload(SourceMayaTools)")

    # Tools Info
    cmds.menuItem(label="About", command=lambda x:AboutWindow())

CreateMenu()
CreateSMDModelWindow()
CreateSMDAnimWindow()
