'use strict';
const http=require('http');
const fs=require('fs');
const path=require('path');
const crypto=require('crypto');

const PORT=Number(process.env.PORT||3000);
const ROOT=path.join(__dirname,'public');
const DB=path.join(__dirname,'accounts.json');
const sessions=new Map();
const worldPresence=new Map();
const worldStates=new Map();
function cleanWorld(v){return String(v||'').trim().toUpperCase().replace(/[^A-Z0-9_-]/g,'').slice(0,18)}
function pruneRoom(world){const room=worldPresence.get(world);if(!room)return;const cutoff=Date.now()-15000;for(const [id,st] of room){if(st.lastSeen<cutoff)room.delete(id)}if(!room.size)worldPresence.delete(world)}
function updatePresence(world,p,b){if(!worldPresence.has(world))worldPresence.set(world,new Map());const room=worldPresence.get(world),prev=room.get(p.playerId)||{};room.set(p.playerId,{playerId:p.playerId,displayName:p.displayName,x:Number.isFinite(Number(b.x))?Number(b.x):(prev.x||120),y:Number.isFinite(Number(b.y))?Number(b.y):(prev.y||0),facing:Number(b.facing)<0?-1:1,onGround:!!b.onGround,vx:Number.isFinite(Number(b.vx))?Number(b.vx):0,vy:Number.isFinite(Number(b.vy))?Number(b.vy):0,lastSeen:Date.now()})}
function roomView(world,selfId){pruneRoom(world);const room=worldPresence.get(world);return room?[...room.values()].filter(p=>p.playerId!==selfId).map(({lastSeen,...p})=>p):[]}


function sanitizeWorldSnapshot(input){
  const s=(input&&typeof input==='object')?input:{};
  const blocks=Array.isArray(s.blocks)?s.blocks.slice(0,20000).filter(b=>b&&Number.isFinite(Number(b.x))&&Number.isFinite(Number(b.y))&&typeof b.t==='string').map(b=>({x:Number(b.x),y:Number(b.y),t:String(b.t).slice(0,32)})):[];
  const door=(s.door&&Number.isFinite(Number(s.door.x))&&Number.isFinite(Number(s.door.y)))?{x:Number(s.door.x),y:Number(s.door.y),w:Number(s.door.w)||36,h:Number(s.door.h)||40}:null;
  return {
    worldId:String(s.worldId||'').slice(0,64),
    surfaceTile:Number.isFinite(Number(s.surfaceTile))?Number(s.surfaceTile):55,
    blocks,
    door,
    caveBgRemoved:Array.isArray(s.caveBgRemoved)?s.caveBgRemoved.slice(0,12000).filter(v=>typeof v==='string'):[],
    plants:Array.isArray(s.plants)?s.plants.slice(0,5000):[],
    locks:Array.isArray(s.locks)?s.locks.slice(0,1000):[],
    weatherOrbs:Array.isArray(s.weatherOrbs)?s.weatherOrbs.slice(0,100):[],
    weather:(s.weather&&typeof s.weather==='object')?{type:String(s.weather.type||'sunny').slice(0,16)}:{type:'sunny'},
    coins:Array.isArray(s.coins)?s.coins.slice(0,5000):[],
    coinsCollected:Math.max(0,Number(s.coinsCollected||0))
  };
}
function getOrCreateWorldState(world,clientSnapshot){
  let state=worldStates.get(world);
  if(!state){
    state={revision:1,snapshot:sanitizeWorldSnapshot(clientSnapshot),updatedAt:Date.now()};
    worldStates.set(world,state);
  }
  return state;
}
function sanitizePlant(p,tx,ty){
  if(!p||typeof p!=='object')return null;
  const seed=String(p.seed||'').slice(0,40);if(!seed)return null;
  return {tx,ty,seed,spliced:!!p.spliced,rarity:Math.max(1,Math.min(99,Number(p.rarity||1))),plantedAt:Math.max(0,Number(p.plantedAt||Date.now())),growMs:Math.max(1000,Number(p.growMs||10000))};
}
function applyWorldAction(state,action){
  if(!state||!action||typeof action!=='object')return false;
  const tx=Math.floor(Number(action.tx)),ty=Math.floor(Number(action.ty));
  if(!Number.isFinite(tx)||!Number.isFinite(ty)||tx<0||ty<0||tx>=100||ty>=100)return false;
  const px=tx*40,py=ty*40,key=(b)=>Math.floor(Number(b.x)/40)===tx&&Math.floor(Number(b.y)/40)===ty;
  let changed=false;
  if(action.type==='break'){
    const before=state.snapshot.blocks.length;
    state.snapshot.blocks=state.snapshot.blocks.filter(b=>!key(b));
    changed=state.snapshot.blocks.length!==before;
    // Idempotent: already broken is still a successful action.
  }else if(action.type==='place'){
    const type=String(action.blockType||'').slice(0,32);if(!type)return false;
    const existing=state.snapshot.blocks.find(key);
    if(existing){if(existing.t!==type)return false}else{state.snapshot.blocks.push({x:px,y:py,t:type});changed=true}
  }else if(action.type==='break-bg'){
    const k=tx+','+ty;if(!state.snapshot.caveBgRemoved.includes(k)){state.snapshot.caveBgRemoved.push(k);changed=true}
  }else if(action.type==='plant-upsert'){
    const plant=sanitizePlant(action.plant,tx,ty);if(!plant)return false;
    const i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty);
    if(i>=0)state.snapshot.plants[i]=plant;else state.snapshot.plants.push(plant);changed=true;
  }else if(action.type==='plant-remove'){
    const before=state.snapshot.plants.length;
    state.snapshot.plants=state.snapshot.plants.filter(p=>!(Number(p.tx)===tx&&Number(p.ty)===ty));
    changed=state.snapshot.plants.length!==before;
  }else return false;
  if(changed){state.revision++;state.updatedAt=Date.now()}
  return true;
}

function loadDb(){try{return JSON.parse(fs.readFileSync(DB,'utf8'))}catch(_){return {accounts:{}}}}
function saveDb(db){fs.writeFileSync(DB,JSON.stringify(db,null,2))}
function cleanId(v){return String(v||'').trim().toLowerCase().replace(/[^a-z0-9_.-]/g,'').slice(0,24)}
function cleanName(v){let s=String(v||'Player').trim().replace(/[^\p{L}\p{N}_ -]/gu,'').slice(0,12);return s||'Player'}
function suffix(){return String(1000+crypto.randomInt(9000))}
function token(){return crypto.randomBytes(32).toString('hex')}
function hashPassword(password,salt=crypto.randomBytes(16).toString('hex')){
  const hash=crypto.scryptSync(String(password),salt,64).toString('hex');
  return {salt,hash};
}
function verifyPassword(password,stored){const got=hashPassword(password,stored.salt).hash;return crypto.timingSafeEqual(Buffer.from(got,'hex'),Buffer.from(stored.hash,'hex'))}
function send(res,status,obj){const data=JSON.stringify(obj);res.writeHead(status,{'Content-Type':'application/json','Content-Length':Buffer.byteLength(data),'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});res.end(data)}
function readJson(req){return new Promise((resolve,reject)=>{let body='';req.on('data',c=>{body+=c;if(body.length>5_000_000){reject(new Error('PAYLOAD_TOO_LARGE'));req.destroy()}});req.on('end',()=>{try{resolve(body?JSON.parse(body):{})}catch(e){reject(e)}});req.on('error',reject)})}
function authToken(req){const h=String(req.headers.authorization||'');return h.startsWith('Bearer ')?h.slice(7):''}
function playerPayload(p){return {playerId:p.playerId,displayName:p.displayName,accountId:p.accountId||null,accountType:p.accountType}}
function createSession(player){const t=token();sessions.set(t,{player,createdAt:Date.now()});return t}

async function api(req,res){
  if(req.method==='OPTIONS'){res.writeHead(204,{'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});return res.end()}
  if(req.method!=='POST')return send(res,405,{error:'METHOD_NOT_ALLOWED'});
  let body={};try{body=await readJson(req)}catch(_){return send(res,400,{error:'BAD_REQUEST'})}
  const db=loadDb();
  if(req.url==='/api/guest'){
    const base=cleanName(body.name);const player={playerId:'G-'+crypto.randomUUID(),displayName:`${base}_#${suffix()}`,accountType:'guest'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/register'){
    const id=cleanId(body.id),pw=String(body.password||''),base=cleanName(body.name);
    if(id.length<3||pw.length<6)return send(res,400,{error:'BAD_REQUEST'});
    if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});
    const pass=hashPassword(pw);const account={id,playerId:'A-'+crypto.randomUUID(),displayName:base,pass,createdAt:Date.now()};db.accounts[id]=account;saveDb(db);
    const player={playerId:account.playerId,displayName:account.displayName,accountId:id,accountType:'account'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/login'){
    const id=cleanId(body.id),pw=String(body.password||''),account=db.accounts[id];
    if(!account||!verifyPassword(pw,account.pass))return send(res,401,{error:'INVALID_CREDENTIALS'});
    const migrated=String(account.displayName||'Player').replace(/_#\d{4}$/,'');if(migrated!==account.displayName){account.displayName=migrated;db.accounts[id]=account;saveDb(db)}
    const player={playerId:account.playerId,displayName:account.displayName,accountId:id,accountType:'account'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/session'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});return send(res,200,{token:t,player:playerPayload(session.player)});
  }
  if(req.url==='/api/logout'){
    const t=authToken(req),session=sessions.get(t);if(session){for(const [world,room] of worldPresence){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}}if(t)sessions.delete(t);return send(res,200,{ok:true});
  }
  if(req.url==='/api/world/join'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});for(const [w,room] of worldPresence){if(w!==world){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(w)}}updatePresence(world,session.player,body);const state=getOrCreateWorldState(world,body.worldSnapshot);return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),revision:state.revision,worldSnapshot:state.snapshot});
  }
  if(req.url==='/api/world/state'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});updatePresence(world,session.player,body);const state=worldStates.get(world);const known=Math.max(0,Number(body.knownRevision||0));return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),revision:state?state.revision:0,...(state&&known<state.revision?{worldSnapshot:state.snapshot}:{}),serverTime:Date.now()});
  }
  if(req.url==='/api/world/action'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=worldStates.get(world);if(!state)return send(res,409,{error:'WORLD_NOT_READY'});const accepted=applyWorldAction(state,body.action);return send(res,accepted?200:409,{ok:accepted,world,revision:state.revision,actionId:String(body.actionId||'').slice(0,80),...(accepted?{}:{error:'ACTION_REJECTED'})});
  }
  if(req.url==='/api/world/leave'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world),room=worldPresence.get(world);if(room){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}return send(res,200,{ok:true});
  }
  return send(res,404,{error:'NOT_FOUND'});
}

function staticFile(req,res){
  let url=req.url.split('?')[0];if(url==='/')url='/index.html';
  const file=path.normalize(path.join(ROOT,url));if(!file.startsWith(ROOT))return send(res,403,{error:'FORBIDDEN'});
  fs.readFile(file,(err,data)=>{if(err){res.writeHead(404);return res.end('Not found')}const ext=path.extname(file);const type=ext==='.html'?'text/html; charset=utf-8':ext==='.js'?'application/javascript':'application/octet-stream';res.writeHead(200,{'Content-Type':type});res.end(data)})
}

const server=http.createServer((req,res)=>{if(req.url.startsWith('/api/'))return api(req,res);return staticFile(req,res)});
server.listen(PORT,()=>console.log(`Pixora Build 14.3 multiplayer world server running on http://localhost:${PORT}`));
