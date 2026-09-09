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

function sanitizeSnapshot(s){
  if(!s||!Array.isArray(s.blocks))return null;
  const blocks=s.blocks.slice(0,12000).filter(b=>b&&Number.isFinite(Number(b.x))&&Number.isFinite(Number(b.y))&&typeof b.t==='string').map(b=>({x:Number(b.x),y:Number(b.y),t:String(b.t).slice(0,32)}));
  if(blocks.length<10)return null;
  const door=s.door&&Number.isFinite(Number(s.door.x))?{x:Number(s.door.x),y:Number(s.door.y)||0,w:Number(s.door.w)||36,h:Number(s.door.h)||40}:null;
  return {
    worldId:String(s.worldId||'').slice(0,64),surfaceTile:Number.isFinite(Number(s.surfaceTile))?Number(s.surfaceTile):55,
    blocks,door,
    caveBgRemoved:Array.isArray(s.caveBgRemoved)?s.caveBgRemoved.filter(x=>typeof x==='string').slice(0,15000):[],
    plants:Array.isArray(s.plants)?s.plants.slice(0,5000):[],
    locks:Array.isArray(s.locks)?s.locks.slice(0,1000):[],
    weatherOrbs:Array.isArray(s.weatherOrbs)?s.weatherOrbs.slice(0,1000):[],
    weather:s.weather&&typeof s.weather==='object'?{type:String(s.weather.type||'sunny').slice(0,16)}:{type:'sunny'},
    coins:Array.isArray(s.coins)?s.coins.slice(0,2000):[],coinsCollected:Math.max(0,Number(s.coinsCollected||0))
  };
}
function ensureWorldState(world,snapshot){
  let state=worldStates.get(world);
  if(!state){const clean=sanitizeSnapshot(snapshot);if(!clean)return null;state={revision:1,snapshot:clean,createdAt:Date.now(),updatedAt:Date.now()};worldStates.set(world,state)}
  return state;
}
function tileKey(x,y){return `${x},${y}`}
function applyWorldAction(state,action){
  if(!state||!action||typeof action!=='object')return false;
  const tx=Math.floor(Number(action.tx)),ty=Math.floor(Number(action.ty));
  if(!Number.isFinite(tx)||!Number.isFinite(ty)||tx<0||ty<0||tx>=100||ty>=100)return false;
  const x=tx*48,y=ty*48,blocks=state.snapshot.blocks;
  const idx=blocks.findIndex(b=>Math.floor(b.x/48)===tx&&Math.floor(b.y/48)===ty);
  if(action.type==='break'){
    if(idx<0||blocks[idx].t==='bedrock')return false;
    blocks.splice(idx,1);state.revision++;state.updatedAt=Date.now();return true;
  }
  if(action.type==='place'){
    if(idx>=0)return false;
    const t=String(action.blockType||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,32);if(!t)return false;
    blocks.push({x,y,t});state.revision++;state.updatedAt=Date.now();return true;
  }
  return false;
}

function loadDb(){try{return JSON.parse(fs.readFileSync(DB,'utf8'))}catch(_){return {accounts:{}}}}
function saveDb(db){fs.writeFileSync(DB,JSON.stringify(db,null,2))}
function cleanId(v){return String(v||'').trim().toLowerCase().replace(/[^a-z0-9_.-]/g,'').slice(0,24)}
function cleanName(v){let s=String(v||'Player').trim().replace(/[^\p{L}\p{N}_ -]/gu,'').slice(0,12);return s||'Player'}
function suffix(){return String(1000+crypto.randomInt(9000))}
function token(){return crypto.randomBytes(32).toString('hex')}
function hashPassword(password,salt=crypto.randomBytes(16).toString('hex')){const hash=crypto.scryptSync(String(password),salt,64).toString('hex');return {salt,hash}}
function verifyPassword(password,stored){const got=hashPassword(password,stored.salt).hash;return crypto.timingSafeEqual(Buffer.from(got,'hex'),Buffer.from(stored.hash,'hex'))}
function send(res,status,obj){const data=JSON.stringify(obj);res.writeHead(status,{'Content-Type':'application/json','Content-Length':Buffer.byteLength(data),'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});res.end(data)}
function readJson(req){return new Promise((resolve,reject)=>{let body='';req.on('data',c=>{body+=c;if(body.length>2000000)req.destroy()});req.on('end',()=>{try{resolve(body?JSON.parse(body):{})}catch(e){reject(e)}});req.on('error',reject)})}
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
    const id=cleanId(body.id),pw=String(body.password||''),base=cleanName(body.name);if(id.length<3||pw.length<6)return send(res,400,{error:'BAD_REQUEST'});if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});
    const pass=hashPassword(pw);const account={id,playerId:'A-'+crypto.randomUUID(),displayName:`${base}_#${suffix()}`,pass,createdAt:Date.now()};db.accounts[id]=account;saveDb(db);const player={playerId:account.playerId,displayName:account.displayName,accountId:id,accountType:'account'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/login'){
    const id=cleanId(body.id),pw=String(body.password||''),account=db.accounts[id];if(!account||!verifyPassword(pw,account.pass))return send(res,401,{error:'INVALID_CREDENTIALS'});const player={playerId:account.playerId,displayName:account.displayName,accountId:id,accountType:'account'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/session'){const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});return send(res,200,{token:t,player:playerPayload(session.player)})}
  if(req.url==='/api/logout'){const t=authToken(req),session=sessions.get(t);if(session){for(const [world,room] of worldPresence){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}}if(t)sessions.delete(t);return send(res,200,{ok:true})}
  if(req.url==='/api/world/join'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});
    const state=ensureWorldState(world,body.worldSnapshot);if(!state)return send(res,400,{error:'BAD_WORLD_SNAPSHOT'});
    for(const [w,room] of worldPresence){if(w!==world){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(w)}}updatePresence(world,session.player,body);
    return send(res,200,{ok:true,world,revision:state.revision,worldSnapshot:state.snapshot,players:roomView(world,session.player.playerId)});
  }
  if(req.url==='/api/world/state'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=worldStates.get(world);if(!state)return send(res,409,{error:'WORLD_NOT_INITIALIZED'});updatePresence(world,session.player,body);const known=Math.max(0,Number(body.knownRevision||0));return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),revision:state.revision,worldSnapshot:state.revision>known?state.snapshot:null,serverTime:Date.now()});
  }
  if(req.url==='/api/world/action'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=worldStates.get(world);if(!state)return send(res,409,{error:'WORLD_NOT_INITIALIZED'});const accepted=applyWorldAction(state,body.action);return send(res,200,{ok:true,accepted,revision:state.revision,worldSnapshot:accepted?null:state.snapshot});
  }
  if(req.url==='/api/world/leave'){const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world),room=worldPresence.get(world);if(room){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}return send(res,200,{ok:true})}
  return send(res,404,{error:'NOT_FOUND'});
}

function staticFile(req,res){let url=req.url.split('?')[0];if(url==='/')url='/index.html';const file=path.normalize(path.join(ROOT,url));if(!file.startsWith(ROOT))return send(res,403,{error:'FORBIDDEN'});fs.readFile(file,(err,data)=>{if(err){res.writeHead(404);return res.end('Pixora server is online')}const ext=path.extname(file);const type=ext==='.html'?'text/html; charset=utf-8':ext==='.js'?'application/javascript':'application/octet-stream';res.writeHead(200,{'Content-Type':type});res.end(data)})}
const server=http.createServer((req,res)=>{if(req.url.startsWith('/api/'))return api(req,res);return staticFile(req,res)});
server.listen(PORT,()=>console.log(`Pixora Build 14.2 server running on http://localhost:${PORT}`));
