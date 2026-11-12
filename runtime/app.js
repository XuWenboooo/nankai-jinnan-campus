import * as THREE from 'three';
import {OrbitControls} from 'three/addons/controls/OrbitControls.js';
import {GLTFLoader} from 'three/addons/loaders/GLTFLoader.js';
import {Sky} from 'three/addons/objects/Sky.js';

const $=id=>document.getElementById(id);
const renderer=new THREE.WebGLRenderer({antialias:true,powerPreference:'high-performance'});
renderer.setPixelRatio(1);renderer.setSize(innerWidth,innerHeight);
renderer.shadowMap.enabled=true;renderer.shadowMap.type=THREE.PCFSoftShadowMap;
renderer.shadowMap.autoUpdate=false;
renderer.outputColorSpace=THREE.SRGBColorSpace;renderer.toneMapping=THREE.ACESFilmicToneMapping;renderer.toneMappingExposure=1.0;
$('canvas').append(renderer.domElement);
const scene=new THREE.Scene();scene.background=new THREE.Color('#c5dce9');
// Physically based daylight reflection, generated locally; no remote HDRI.
const reflectionScene=new THREE.Scene();const sky=new Sky();sky.scale.setScalar(10000);
sky.material.uniforms.turbidity.value=4;sky.material.uniforms.rayleigh.value=2;
sky.material.uniforms.mieCoefficient.value=.003;sky.material.uniforms.mieDirectionalG.value=.8;
sky.material.uniforms.sunPosition.value.set(-100,180,90).normalize();reflectionScene.add(sky);
const pmrem=new THREE.PMREMGenerator(renderer);scene.environment=pmrem.fromScene(reflectionScene,.04).texture;scene.environmentIntensity=.015;pmrem.dispose();sky.geometry.dispose();sky.material.dispose();
const camera=new THREE.PerspectiveCamera(60,innerWidth/innerHeight,.08,6000);
const controls=new OrbitControls(camera,renderer.domElement);controls.enableDamping=true;controls.maxDistance=4500;controls.minDistance=1;
const world=new THREE.Group();world.name='ENGINEERING_ROOT';scene.add(world);
scene.add(new THREE.HemisphereLight('#e5f2ff','#a2a591',1.25));
const sun=new THREE.DirectionalLight('#fff4de',2.5);sun.castShadow=true;sun.shadow.mapSize.set(2048,2048);sun.shadow.normalBias=.04;sun.shadow.bias=-.0002;
sun.shadow.camera.left=-110;sun.shadow.camera.right=110;sun.shadow.camera.top=110;sun.shadow.camera.bottom=-110;sun.shadow.camera.near=1;sun.shadow.camera.far=650;scene.add(sun,sun.target);
const loader=new GLTFLoader();const failures=[];const loadedAssets=new Set();const treeTemplates=new Map();const treeBatches=new Map();
let scale=1,walking=false,yaw=0,pitch=0,lastTime=performance.now(),lastTrees=-1,lastHud=0;
let treeInstances=[],treeForms=[],ground={},heightData,waterMask,colliders=[],views=[],frameSamples=[],walkingFrames=[];
const treeSlots=new Map();
const trunkCells=new Map();
const walkSurfaceCells=new Map();
let walkSurfaceCount=0;
let treeColorsLinear=false;
let waterNormal=null;
const surfacePbr=new Map();
let activeRoute=null;
let hudFrames=[];
let entryAdjustment=null;
let lastTreePosition=null;
let shadowCell='';
const keys=new Set();const dummy=new THREE.Object3D();const point=new THREE.Vector3();
const targetRenderFPS=45;

const compressedJSON=new Set(["world/runtime_asset_manifest.json", "world/walkable_surfaces.json", "assets/vegetation/instances.json"]);
async function bytes(path,compressed=false){const r=await fetch('../'+path+(compressed?'.gz':''));if(!r.ok)throw Error(path+' HTTP '+r.status);return await (compressed?new Response(r.body.pipeThrough(new DecompressionStream('gzip'))):r).arrayBuffer();}
async function json(path){return JSON.parse(new TextDecoder().decode(await bytes(path,compressedJSON.has(path))))}
async function asset(path){
 const response=await fetch('../'+path+'.gz');
 if(!response.ok)throw Error(path+' HTTP '+response.status);
 const decoded=new Response(response.body.pipeThrough(new DecompressionStream('gzip')));
 const buffer=await decoded.arrayBuffer();
 const gltf=await loader.parseAsync(buffer,'../'+path.slice(0,path.lastIndexOf('/')+1));
 loadedAssets.add(path);return gltf.scene;
}
function terrainY(x,z){
 if(!heightData)return 1;
 const fx=Math.max(0,Math.min(ground.width-1.001,(x-ground.origin_xz[0])/ground.resolution));
 const fz=Math.max(0,Math.min(ground.height-1.001,(z-ground.origin_xz[1])/ground.resolution));
 const ix=Math.floor(fx),iz=Math.floor(fz),tx=fx-ix,tz=fz-iz;
 const a=heightData[iz*ground.width+ix],b=heightData[iz*ground.width+ix+1],c=heightData[(iz+1)*ground.width+ix],d=heightData[(iz+1)*ground.width+ix+1];
 return (a*(1-tx)+b*tx)*(1-tz)+(c*(1-tx)+d*tx)*tz;
}
function indexWalkSurfaces(data){
 for(const surface of data.surfaces||[])for(const t of surface.triangles){
  const [a,b,c]=t,den=(b[2]-c[2])*(a[0]-c[0])+(c[0]-b[0])*(a[2]-c[2]);
  if(Math.abs(den)<1e-10)continue;
  const item={id:surface.id,mode:surface.mode||'raise',a,b,c,den};
  const loX=Math.floor(Math.min(a[0],b[0],c[0])/16),hiX=Math.floor(Math.max(a[0],b[0],c[0])/16);
  const loZ=Math.floor(Math.min(a[2],b[2],c[2])/16),hiZ=Math.floor(Math.max(a[2],b[2],c[2])/16);
  for(let x=loX;x<=hiX;x++)for(let z=loZ;z<=hiZ;z++){const key=x+'_'+z;if(!walkSurfaceCells.has(key))walkSurfaceCells.set(key,[]);walkSurfaceCells.get(key).push(item);}
  walkSurfaceCount++;
 }
}
function walkableHeights(x,z,ceiling=Infinity){
 let replacement=-Infinity,raised=-Infinity;
 for(const {a,b,c,den,mode} of walkSurfaceCells.get(Math.floor(x/16)+'_'+Math.floor(z/16))||[]){
  const aa=((b[2]-c[2])*(x-c[0])+(c[0]-b[0])*(z-c[2]))/den;
  const bb=((c[2]-a[2])*(x-c[0])+(a[0]-c[0])*(z-c[2]))/den,cc=1-aa-bb;
  if(aa<-.000001||bb<-.000001||cc<-.000001)continue;
  const h=aa*a[1]+bb*b[1]+cc*c[1];
  if(h>ceiling+.00001)continue;
  if(mode==='replace')replacement=Math.max(replacement,h);else raised=Math.max(raised,h);
 }
 return {replacement,raised,hit:replacement!==-Infinity||raised!==-Infinity};
}
function groundY(x,z,ceiling=Infinity){
 const {replacement,raised}=walkableHeights(x,z,ceiling);
 return Math.max(replacement!==-Infinity?replacement:terrainY(x,z),raised);
}
function inside(x,z,ring){let result=false;for(let i=0,j=ring.length-1;i<ring.length;j=i++){
 const a=ring[i],b=ring[j];if((a[1]>z)!==(b[1]>z)&&x<(b[0]-a[0])*(z-a[1])/(b[1]-a[1])+a[0])result=!result;
 }return result;}
function blocked(x,z,feet=groundY(x,z)){
 if(ground.width&&(x<ground.origin_xz[0]||z<ground.origin_xz[1]||x>ground.origin_xz[0]+(ground.width-1)*ground.resolution||z>ground.origin_xz[1]+(ground.height-1)*ground.resolution))return true;
 // A verified bridge/deck surface remains walkable over a water/low-ground
 // cell. Canopy roofs are deliberately absent from the walkable contract.
 if(waterMask){const ix=Math.floor((x-ground.origin_xz[0])/ground.resolution),iz=Math.floor((z-ground.origin_xz[1])/ground.resolution);if(waterMask[iz*ground.width+ix]&&!walkableHeights(x,z,feet+.05).hit)return true;}
 const head=feet+1.68/scale;
 for(const collider of colliders){
  if(x<=collider.bounds[0]-.25||x>=collider.bounds[2]+.25||z<=collider.bounds[1]-.25||z>=collider.bounds[3]+.25)continue;
  if(collider.base!==undefined&&head<=collider.base+.02)continue;
  if(collider.roof!==undefined&&feet>=collider.roof-.02)continue;
  // Native stair risers enter the body margin before the foot centre reaches the tread.
  if(collider.walkable_step&&collider.roof<=feet+.45/scale+.00001)continue;
  if(inside(x,z,collider.outer)&&!(collider.holes||[]).some(h=>inside(x,z,h)))return true;
 }
 const cx=Math.floor(x/16),cz=Math.floor(z/16);
 for(let dx=-1;dx<=1;dx++)for(let dz=-1;dz<=1;dz++)for(const t of trunkCells.get((cx+dx)+'_'+(cz+dz))||[]){
  if(head<=t.position[1]||feet>=t.position[1]+t.height)continue;
  if(Math.hypot(x-t.position[0],z-t.position[2])<(t.collision_radius||.25)+.18)return true;
 }
 return false;
}
function setView(view){
 hudFrames=[];
 activeRoute=null;
 walking=false;document.exitPointerLock?.();$('cross').style.display='none';controls.enabled=true;
 $('instructions').textContent='拖动旋转 · 右键平移 · 滚轮缩放';
 if(view.id)$('view').value=view.id;
 camera.position.fromArray(view.position).multiplyScalar(scale);controls.target.fromArray(view.target).multiplyScalar(scale);
 camera.fov=view.fov||60;camera.updateProjectionMatrix();controls.update();lastTrees=-1;
}
function enterWalk(){
 walking=true;controls.enabled=false;
 const sx=camera.position.x/scale,sz=camera.position.z/scale;entryAdjustment=null;
 const entryCeiling=camera.position.y/scale;
 if(blocked(sx,sz,groundY(sx,sz,entryCeiling))){
  let found=null;
  for(let radius=1;radius<=180&&!found;radius++)for(let i=0;i<64;i++){const x=sx+radius*Math.cos(i*Math.PI/32),z=sz+radius*Math.sin(i*Math.PI/32);if(!blocked(x,z,groundY(x,z,entryCeiling))){found=[x,z];break;}}
  if(found){camera.position.x=found[0]*scale;camera.position.z=found[1]*scale;entryAdjustment={from:[sx,sz],to:found,reason:'nearest exterior position; orbit camera was inside building projection'};}
 }
 const direction=camera.getWorldDirection(new THREE.Vector3());yaw=Math.atan2(-direction.x,-direction.z);pitch=Math.asin(direction.y);
 camera.position.y=groundY(camera.position.x/scale,camera.position.z/scale,entryCeiling)*scale+1.68;
 $('cross').style.display='block';$('instructions').textContent='WASD 行走 · 鼠标转向 · Shift 加速 · Esc 释放鼠标';
}
function walkHeight(x,z,previousFloor){
 const floor=groundY(x,z,previousFloor+.45/scale);
 if(floor-previousFloor>.45/scale||previousFloor-floor>.75/scale||blocked(x,z,floor))return null;
 return floor;
}
function moveWalk(forward,right,dt){
 const speed=(keys.has('ShiftLeft')?2.8:1.45)*dt;
 const dx=(-Math.sin(yaw)*forward+Math.cos(yaw)*right)*speed;
 const dz=(-Math.cos(yaw)*forward-Math.sin(yaw)*right)*speed;
 let x=camera.position.x/scale,z=camera.position.z/scale;
 let feet=(camera.position.y-1.68)/scale;
 const nextX=x+dx/scale;
 const floorX=walkHeight(nextX,z,feet);
 if(floorX!==null){x=nextX;feet=floorX;}
 const nextZ=z+dz/scale;
 const floorZ=walkHeight(x,nextZ,feet);
 if(floorZ!==null){z=nextZ;feet=floorZ;}
 camera.position.set(x*scale,feet*scale+1.68,z*scale);
 camera.rotation.set(pitch,yaw,0,'YXZ');
}
function startRoute(route){
 camera.position.fromArray(route.waypoints[0]).multiplyScalar(scale);
 camera.lookAt(new THREE.Vector3().fromArray(route.waypoints[1]).multiplyScalar(scale));enterWalk();pitch=0;
 activeRoute={id:route.id,points:route.waypoints,index:1,started:performance.now(),distance:0,blockedFrames:0};
 frameSamples=[];
}
function stepRoute(dt){
 if(activeRoute.index>=activeRoute.points.length)return;
 const p=activeRoute.points[activeRoute.index],dx=p[0]*scale-camera.position.x,dz=p[2]*scale-camera.position.z;
 if(Math.hypot(dx,dz)<.65){activeRoute.index++;return;}
 yaw=Math.atan2(-dx,-dz);const before=camera.position.clone();moveWalk(1,0,dt);
 const distance=Math.hypot(camera.position.x-before.x,camera.position.z-before.z);activeRoute.distance+=distance;
 if(distance<.0001)activeRoute.blockedFrames++;
}
function makeTreeBatch(key,form,lod,count){
 const group=new THREE.Group();group.name='VEG_'+key;
 const templates=treeTemplates.get(form+'_'+lod);
 const meshes=templates.map(t=>{
  const mesh=new THREE.InstancedMesh(t.geometry,t.material,count);mesh.name=group.name+'_'+t.name;mesh.count=0;
  mesh.castShadow=lod<2;mesh.receiveShadow=lod<2;mesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);group.add(mesh);return mesh;
 });world.add(group);const batch={group,meshes,capacity:count};treeBatches.set(key,batch);return batch;
}
function updateTrees(){
 if(!treeInstances.length)return;
 const sx=camera.position.x/scale,sz=camera.position.z/scale,sy=camera.position.y/scale;
 // LOD depends on position, not orbit orientation. Keep every source instance
 // resident and update its LOD only after a meaningful camera displacement.
 if(lastTrees>=0&&lastTreePosition&&Math.hypot(sx-lastTreePosition[0],sy-lastTreePosition[1],sz-lastTreePosition[2])<4)return;
 lastTreePosition=[sx,sy,sz];
 const buckets=new Map();
 for(const tree of treeInstances){
  const p=tree.position,dist=Math.hypot(p[0]-sx,p[2]-sz,Math.max(0,sy-p[1]-8));
  const sizeFactor=tree.category==='shrub'?Math.max(.08,Math.min(.5,tree.height/10)):1;
  const lod=dist<40*sizeFactor?0:dist<150*sizeFactor?1:dist<350*sizeFactor?2:3;
  const span=lod===3?512:128;const key=Math.floor(p[0]/span)+'_'+Math.floor(p[2]/span)+'_'+tree.variant+'_'+lod;
  if(!buckets.has(key))buckets.set(key,{form:tree.variant,lod,trees:[]});buckets.get(key).trees.push(tree);
 }
 treeSlots.clear();
 // Retire obsolete LOD/spatial batches instead of retaining every previously
 // visited camera's GPU instance buffers. Prototype geometry stays shared.
 for(const [key,batch] of treeBatches){if(!buckets.has(key)){world.remove(batch.group);batch.meshes.forEach(m=>m.dispose());treeBatches.delete(key);}}
 for(const [key,bucket] of buckets){
  let batch=treeBatches.get(key);
  if(!batch||batch.capacity<bucket.trees.length){
   if(batch){world.remove(batch.group);batch.meshes.forEach(m=>m.dispose());}
   batch=makeTreeBatch(key,bucket.form,bucket.lod,Math.max(Math.ceil(bucket.trees.length/64)*64,64));
  }
  batch.group.visible=true;
  bucket.trees.forEach((tree,i)=>{
   dummy.position.fromArray(tree.position);dummy.rotation.set(0,tree.rotation_y,0);dummy.scale.fromArray(tree.scale);dummy.updateMatrix();
   for(const mesh of batch.meshes)mesh.setMatrixAt(i,dummy.matrix);
   treeSlots.set(tree.id,{node:batch.group.name,index:i,lod:bucket.lod});
  });
  for(const mesh of batch.meshes){mesh.count=bucket.trees.length;mesh.instanceMatrix.needsUpdate=true;mesh.computeBoundingSphere();}
 }
 renderer.shadowMap.needsUpdate=true;
}
async function loadSurfacePbr(){
 const config=await json('world/pbr_surface_materials.json');
 const source=await json(config.source_manifest);
 const loader=new THREE.TextureLoader();
 await Promise.all(Object.entries(config.bindings).map(async ([materialName,sourceId])=>{
  const record=source.materials.find(item=>item.id===sourceId);
  if(!record)throw Error('Missing PBR material source '+sourceId);
  const textures=await Promise.all(['albedo','normal_gl','roughness'].map(async role=>{
   const texture=await loader.loadAsync('../'+record.maps[role].path);
   texture.wrapS=texture.wrapT=THREE.RepeatWrapping;
   texture.repeat.set(config.uv_source_units_per_repeat*scale/record.tile_m[0],config.uv_source_units_per_repeat*scale/record.tile_m[1]);
   texture.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());
   texture.colorSpace=role==='albedo'?THREE.SRGBColorSpace:THREE.NoColorSpace;
   return texture;
  }));
  surfacePbr.set(materialName,{record,textures,uses:0,tint:config.base_tint_srgb||[1,1,1]});
 }));
}

function prepareModel(model,kind){model.traverse(mesh=>{
 if(!mesh.isMesh)return;mesh.castShadow=kind==='building'||kind==='ground_flora';mesh.receiveShadow=true;
 if(!mesh.material.userData.sourceColorConverted){mesh.material.color.convertSRGBToLinear();mesh.material.userData.sourceColorConverted=true;}
 if(mesh.material.map){mesh.material.map.anisotropy=renderer.capabilities.getMaxAnisotropy();}
 // Explicit environment binding gives glazing a readable daylight reflection;
 // setting only envMapIntensity while using scene.environment is not a
 // per-material override in this renderer version.
 if(/Glass/i.test(mesh.material.name)){mesh.material.envMap=scene.environment;mesh.material.envMapIntensity=.06;}
 if(kind==='surface'&&surfacePbr.has(mesh.material.name)){
  const {record,textures,tint}=surfacePbr.get(mesh.material.name);
  mesh.material.color.fromArray(tint).convertSRGBToLinear();
  mesh.material.map=textures[0];
  mesh.material.normalMap=textures[1];
  mesh.material.roughnessMap=textures[2];
  mesh.material.normalScale.setScalar(record.normal_scale_initial_inferred);
  mesh.material.roughness=record.roughness_multiplier_initial;
  mesh.material.metalness=record.metalness;
  mesh.material.userData.pbrSourceId=record.id;
  surfacePbr.get(mesh.material.name).uses++;
  mesh.material.needsUpdate=true;
 }
 if(mesh.material.name==='water'&&waterNormal){mesh.material.normalMap=waterNormal;mesh.material.normalScale.set(.45,.45);mesh.material.roughness=.27;}
 });world.add(model);}
async function parallelLoad(items,callback,workers=5){let next=0,done=0;await Promise.all(Array.from({length:workers},async()=>{
 while(next<items.length){const item=items[next++];try{await callback(item)}catch(e){failures.push(String(e));$('error').textContent=failures.at(-1)}
 done++;$('status').textContent='正在加载连续校园 '+done+' / '+items.length;
 }}));}
async function boot(){
 waterNormal=await new THREE.TextureLoader().loadAsync('../assets/materials/water_ripple_normal.png');waterNormal.wrapS=waterNormal.wrapT=THREE.RepeatWrapping;waterNormal.anisotropy=4;
 const [frames,manifest,cameras,treeRegistry,treeAssets,terrain]=await Promise.all(['world/coordinate_frames.json','world/runtime_asset_manifest.json','world/cameras.json','world/vegetation_registry.json','assets/vegetation/tree_assets.json','assets/surfaces/ground_height.json'].map(json));
 scale=frames.source_to_engineering.uniform_scale;world.scale.setScalar(scale);views=cameras.views;ground=terrain;
 await loadSurfacePbr();
 heightData=new Float32Array(await bytes(ground.file,true));
 if(ground.blocked_water_file)waterMask=new Uint8Array(await bytes(ground.blocked_water_file,true));
 if(manifest.walkable_surface_file)indexWalkSurfaces(await json(manifest.walkable_surface_file));
 colliders=manifest.colliders||[];treeInstances=(await json(treeRegistry.instance_file)).instances;treeForms=treeAssets.forms;treeColorsLinear=treeAssets.vertex_colors_linear===true;
 for(const tree of treeInstances){if(tree.category!=='tree')continue;const key=Math.floor(tree.position[0]/16)+'_'+Math.floor(tree.position[2]/16);if(!trunkCells.has(key))trunkCells.set(key,[]);trunkCells.get(key).push(tree);}
 for(const view of views){const option=document.createElement('option');option.textContent=view.label;option.value=view.id;$('view').append(option);}
 const requestedView=new URLSearchParams(location.search).get('view')||'DEFAULT';setView(views.find(v=>v.id===requestedView)||views[0]);
 const loadItems=manifest.assets.map(a=>({...a,type:'scene'}));
 for(const form of treeForms)for(const item of form.assets)loadItems.push({...item,form:form.id,type:'tree'});
 await parallelLoad(loadItems,async item=>{
  const model=await asset(item.file||item.asset);
  if(item.type==='tree'){
   model.updateMatrixWorld(true);const parts=[];model.traverse(mesh=>{
    if(!mesh.isMesh)return;const geometry=mesh.geometry.clone().applyMatrix4(mesh.matrixWorld);
    const colors=geometry.attributes.color;
    if(colors&&!treeColorsLinear){const color=new THREE.Color();for(let i=0;i<colors.count;i++){color.fromBufferAttribute(colors,i).convertSRGBToLinear();colors.setXYZ(i,color.r,color.g,color.b);}}
    mesh.material.side=THREE.DoubleSide;parts.push({name:mesh.name,geometry,material:mesh.material});
   });treeTemplates.set(item.form+'_'+item.lod,parts);
  }else{model.name=item.id;prepareModel(model,item.kind);}
 });
 updateTrees();await renderer.compileAsync(scene,camera);renderer.render(scene,camera);
 $('status').textContent=failures.length?'加载存在问题':'连续校园已就绪';
 $('detail').textContent=treeInstances.length.toLocaleString()+' 株树木与灌丛 · '+(manifest.ground_flora_source_units||0)+' 低植被单元（含 '+(manifest.ground_flora_low_shrub_patches||0)+' 矮灌丛） · '+(manifest.aquatic_instances||0)+' 片水生叶 / '+(manifest.aquatic_flowers||0)+' 株水生花 · '+(manifest.moss_ground_cover_source_groups||0)+' 苔藓源组地被 · '+manifest.assets.length+' 个场景资源 · 工程尺度 '+scale.toFixed(6)+' m/u（暂定）';
 window.campus.ready=failures.length===0;
}
$('view').onchange=()=>setView(views.find(v=>v.id===$('view').value));
$('walk').onclick=()=>{enterWalk();renderer.domElement.requestPointerLock();};
$('orbit').onclick=()=>{walking=false;controls.enabled=true;document.exitPointerLock?.();$('cross').style.display='none';controls.target.copy(camera.position).add(camera.getWorldDirection(point).multiplyScalar(30));};
$('light').onclick=()=>{const diagnostic=$('light').textContent==='诊断日光';$('light').textContent=diagnostic?'展示日光':'诊断日光';sun.intensity=diagnostic?2.4:3.;renderer.toneMappingExposure=diagnostic?1.05:1.12;};
$('source').onclick=()=>window.open('../#comparison','_blank');
addEventListener('keydown',e=>{if(e.code==='Escape'){keys.clear();document.exitPointerLock?.();return;}keys.add(e.code);});addEventListener('keyup',e=>keys.delete(e.code));
addEventListener('blur',()=>keys.clear());
addEventListener('mousemove',e=>{if(walking&&document.pointerLockElement){yaw-=e.movementX*.002;pitch=Math.max(-1.35,Math.min(1.35,pitch-e.movementY*.002));}});
addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight)});
window.campus={ready:false,setView,enterWalk,moveWalk,groundY,walkGroundY:(x,z)=>groundY(x,z,(camera.position.y-1.68+.45)/scale),terrainY,blocked,renderer,scene,camera,world,controls,scale:()=>scale,
 report:()=>({version:'NKU-NONVOXEL-20261111-R2',surfacePbr:[...surfacePbr].map(([material,value])=>({material,source:value.record.id,tile_m:value.record.tile_m,normal_strength:value.record.normal_scale_initial_inferred,mesh_uses:value.uses,textures:value.textures.map(t=>({dimensions:[t.image.width,t.image.height],colorSpace:t.colorSpace,repeat:t.repeat.toArray()}))})),targetRenderFPS,walkSurfaceTriangles:walkSurfaceCount,ready:window.campus.ready,assets:[...loadedAssets],failures,trees:treeInstances.length,placedTreeInstances:treeSlots.size,nodes:world.children.filter(n=>!n.name.startsWith('VEG_')).map(n=>n.name),position:camera.position.toArray(),target:controls.target.toArray(),fov:camera.fov,cameraMatrix:camera.matrixWorld.toArray(),projectionMatrix:camera.projectionMatrix.toArray(),scale,rootMatrix:world.matrixWorld.toArray(),lighting:{sunIntensity:sun.intensity,hemisphereIntensity:1.25,environmentIntensity:scene.environmentIntensity,exposure:renderer.toneMappingExposure,shadows:renderer.shadowMap.enabled,shadowSize:2048,fog:false},draw:renderer.info.render,memory:renderer.info.memory,frames:frameSamples.slice(-15000),route:activeRoute?{id:activeRoute.id,index:activeRoute.index,distance:activeRoute.distance,blockedFrames:activeRoute.blockedFrames,elapsed:(performance.now()-activeRoute.started)/1000}:null}),
 setShadows:enabled=>{renderer.shadowMap.enabled=!!enabled;sun.castShadow=!!enabled;world.traverse(n=>{if(n.material)for(const m of (Array.isArray(n.material)?n.material:[n.material]))m.needsUpdate=true;});renderer.shadowMap.needsUpdate=true;},
 startRoute,stopRoute:()=>{activeRoute=null;},
 instanceNodes:()=>Object.fromEntries(treeSlots),
 sceneNodeNames:()=>{const names=[];world.traverse(n=>{if(n.name)names.push(n.name)});return names;},
 resetMetrics:()=>{frameSamples=[]},treeUpdate:()=>{updateTrees()},setWalkPose:(p,target)=>{camera.position.fromArray(p).multiplyScalar(scale);camera.lookAt(new THREE.Vector3().fromArray(target).multiplyScalar(scale));enterWalk();},
};
function animate(now){
 // A real presentation-rate cap leaves GPU time for stable full-scope
 // rendering. Metrics below count rendered frames only, never skipped RAFs.
 if(now-lastTime<1000/targetRenderFPS){requestAnimationFrame(animate);return;}
 const elapsed=now-lastTime;const dt=Math.min(.05,elapsed/1000);lastTime=now;
 if(activeRoute)stepRoute(dt);else if(walking)moveWalk(Number(keys.has('KeyW'))-Number(keys.has('KeyS')),Number(keys.has('KeyD'))-Number(keys.has('KeyA')),dt);else controls.update();
 if(now-lastTrees>600&&window.campus.ready){updateTrees();lastTrees=now;}
 const cx=Math.round(camera.position.x/16)*16,cz=Math.round(camera.position.z/16)*16,newShadowCell=cx+'_'+cz;
 if(newShadowCell!==shadowCell){shadowCell=newShadowCell;sun.target.position.set(cx,0,cz);sun.position.copy(sun.target.position).add(new THREE.Vector3(-100,180,90));renderer.shadowMap.needsUpdate=true;}
 renderer.render(scene,camera);if(window.campus.ready){frameSamples.push(elapsed);hudFrames.push(elapsed);if(hudFrames.length>60)hudFrames.shift();}
 if(now-lastHud>500){const samples=hudFrames.slice().sort((a,b)=>a-b),median=samples[Math.floor(samples.length/2)]||elapsed;$('hud').textContent=(1000/Math.max(median,1)).toFixed(0)+' median FPS / last 60 frames · '+renderer.info.render.triangles.toLocaleString()+' triangles · '+renderer.info.render.calls+' draws';lastHud=now;}
 requestAnimationFrame(animate);
}
requestAnimationFrame(animate);
boot().catch(e=>{failures.push(String(e));$('error').textContent=String(e);$('status').textContent='工程资源读取失败';console.error(e)});
