'use strict';
const http=require('http');
const fs=require('fs');
const path=require('path');
const crypto=require('crypto');

const PORT=Number(process.env.PORT||3000);
const ROOT=path.join(__dirname,'public');
const DB=path.join(__dirname,'accounts.json');
const sessions=new Map();
const revokedTokens=new Map();
const activeAccountTokens=new Map();
const worldPresence=new Map();
const worldStates=new Map();

function cleanWorld(v){return String(v||'').trim().toUpperCase().replace(/[^A-Z0-9_-]/g,'').slice(0,18)}
function cleanId(v){return String(v||'').trim().toLowerCase().replace(/[^a-z0-9]/g,'').slice(0,24)}
function cleanName(v){let s=String(v||'Player').trim().replace(/[^\p{L}\p{N}_ -]/gu,'').slice(0,12);return s||'Player'}
function suffix(){return String(1000+crypto.randomInt(9000))}
function token(){return crypto.randomBytes(32).toString('hex')}
function hashPassword(password,salt=crypto.randomBytes(16).toString('hex')){return {salt,hash:crypto.scryptSync(String(password),salt,64).toString('hex')}}
function verifyPassword(password,stored){
  try{const got=hashPassword(password,stored.salt).hash;return crypto.timingSafeEqual(Buffer.from(got,'hex'),Buffer.from(stored.hash,'hex'))}catch(_){return false}
}
function loadDb(){
  try{const d=JSON.parse(fs.readFileSync(DB,'utf8'));if(!d.accounts)d.accounts={};if(!d.worlds)d.worlds={};return d}
  catch(_){return {accounts:{},worlds:{}}}
}
function saveDb(db){const tmp=DB+'.tmp';fs.writeFileSync(tmp,JSON.stringify(db,null,2));fs.renameSync(tmp,DB)}
function send(res,status,obj){
  const data=JSON.stringify(obj);res.writeHead(status,{'Content-Type':'application/json','Content-Length':Buffer.byteLength(data),'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});res.end(data)
}
function readJson(req){return new Promise((resolve,reject)=>{let body='';req.on('data',c=>{body+=c;if(body.length>5_000_000){reject(new Error('PAYLOAD_TOO_LARGE'));req.destroy()}});req.on('end',()=>{try{resolve(body?JSON.parse(body):{})}catch(e){reject(e)}});req.on('error',reject)})}
function authToken(req){const h=String(req.headers.authorization||'');return h.startsWith('Bearer ')?h.slice(7):''}
function playerPayload(p){return {playerId:p.playerId,displayName:p.displayName,accountId:p.accountId||null,accountType:p.accountType}}

function createSession(player){
  const t=token();
  if(player.accountType==='account'&&player.accountId){
    const old=activeAccountTokens.get(player.accountId);
    if(old&&old!==t){const oldSession=sessions.get(old);if(oldSession)removePresence(oldSession.player.playerId);sessions.delete(old);revokedTokens.set(old,{reason:'SESSION_REPLACED',at:Date.now()})}
    activeAccountTokens.set(player.accountId,t);
  }
  sessions.set(t,{player,createdAt:Date.now()});
  return t;
}
function removePresence(playerId){for(const [world,room] of worldPresence){room.delete(playerId);if(!room.size)worldPresence.delete(world)}}
function sessionFor(req){
  const t=authToken(req);
  if(revokedTokens.has(t))return {token:t,error:revokedTokens.get(t).reason||'INVALID_SESSION'};
  const session=sessions.get(t);return session?{token:t,session}:{token:t,error:'INVALID_SESSION'}
}
function requireSession(req,res){
  const s=sessionFor(req);if(s.error){send(res,401,{error:s.error});return null}return s
}
setInterval(()=>{const cutoff=Date.now()-6*60*60*1000;for(const [t,v] of revokedTokens)if(v.at<cutoff)revokedTokens.delete(t)},60*60*1000).unref?.();

function pruneRoom(world){const room=worldPresence.get(world);if(!room)return;const cutoff=Date.now()-12000;for(const [id,st] of room){if(st.lastSeen<cutoff)room.delete(id)}if(!room.size)worldPresence.delete(world)}
function sanitizeActionState(a){
  if(!a||typeof a!=='object'||!a.active)return {active:false};
  const tx=Math.floor(Number(a.tx)),ty=Math.floor(Number(a.ty));if(!Number.isFinite(tx)||!Number.isFinite(ty))return {active:false};
  const kind=['block','bg','air'].includes(String(a.kind))?String(a.kind):'air';
  return {active:true,kind,tx,ty,progress:Math.max(0,Math.min(1,Number(a.progress||0))),tool:String(a.tool||'punch').slice(0,16)}
}
function updatePresence(world,p,b){
  if(!worldPresence.has(world))worldPresence.set(world,new Map());
  const room=worldPresence.get(world),prev=room.get(p.playerId)||{};
  room.set(p.playerId,{playerId:p.playerId,displayName:p.displayName,x:Number.isFinite(Number(b.x))?Number(b.x):(prev.x||120),y:Number.isFinite(Number(b.y))?Number(b.y):(prev.y||0),facing:Number(b.facing)<0?-1:1,onGround:!!b.onGround,vx:Number.isFinite(Number(b.vx))?Number(b.vx):0,vy:Number.isFinite(Number(b.vy))?Number(b.vy):0,actionState:sanitizeActionState(b.actionState),lastSeen:Date.now()})
}
function roomView(world,selfId){pruneRoom(world);const room=worldPresence.get(world);return room?[...room.values()].filter(p=>p.playerId!==selfId).map(({lastSeen,...p})=>p):[]}

function sanitizeDrop(d){
  if(!d||typeof d!=='object')return null;const id=String(d.id||'').slice(0,80),kind=d.kind==='gems'?'gems':'item',item=kind==='item'?String(d.item||'').slice(0,40):null;
  if(!id||(kind==='item'&&!item))return null;
  return {id,x:Number(d.x)||0,y:Number(d.y)||0,item,kind,amount:Math.max(1,Math.min(9999,Math.floor(Number(d.amount||1)))),pickupAfter:Math.max(0,Number(d.pickupAfter||0))}
}
function sanitizeWorldSnapshot(input){
  const s=(input&&typeof input==='object')?input:{};
  const blocks=Array.isArray(s.blocks)?s.blocks.slice(0,20000).filter(b=>b&&Number.isFinite(Number(b.x))&&Number.isFinite(Number(b.y))&&typeof b.t==='string').map(b=>({x:Number(b.x),y:Number(b.y),t:String(b.t).slice(0,32)})):[];
  const door=(s.door&&Number.isFinite(Number(s.door.x))&&Number.isFinite(Number(s.door.y)))?{x:Number(s.door.x),y:Number(s.door.y),w:Number(s.door.w)||36,h:Number(s.door.h)||40}:null;
  return {
    worldId:String(s.worldId||'').slice(0,64),surfaceTile:Number.isFinite(Number(s.surfaceTile))?Number(s.surfaceTile):55,blocks,door,
    caveBgRemoved:Array.isArray(s.caveBgRemoved)?s.caveBgRemoved.slice(0,12000).filter(v=>typeof v==='string'):[],
    plants:Array.isArray(s.plants)?s.plants.slice(0,5000):[],locks:Array.isArray(s.locks)?s.locks.slice(0,1000):[],weatherOrbs:Array.isArray(s.weatherOrbs)?s.weatherOrbs.slice(0,100):[],
    weather:(s.weather&&typeof s.weather==='object')?{type:String(s.weather.type||'sunny').slice(0,16)}:{type:'sunny'},
    coins:Array.isArray(s.coins)?s.coins.slice(0,5000):[],coinsCollected:Math.max(0,Number(s.coinsCollected||0)),
    drops:Array.isArray(s.drops)?s.drops.slice(0,5000).map(sanitizeDrop).filter(Boolean):[]
  }
}
function sanitizePlant(p,tx,ty){
  if(!p||typeof p!=='object')return null;const seed=String(p.seed||'').slice(0,40);if(!seed)return null;
  return {tx,ty,seed,spliced:!!p.spliced,rarity:Math.max(1,Math.min(99,Number(p.rarity||1))),plantedAt:Math.max(0,Number(p.plantedAt||Date.now())),growMs:Math.max(1000,Number(p.growMs||10000))}
}
function loadWorldFromDb(world){
  const db=loadDb(),raw=db.worlds?.[world];if(!raw)return null;
  const state={revision:Math.max(1,Number(raw.revision||1)),snapshot:sanitizeWorldSnapshot(raw.snapshot),chat:Array.isArray(raw.chat)?raw.chat.slice(-30):[],updatedAt:Number(raw.updatedAt||Date.now())};
  worldStates.set(world,state);return state
}
function persistWorld(world,state){
  const db=loadDb();db.worlds[world]={revision:state.revision,snapshot:state.snapshot,chat:(state.chat||[]).slice(-30),updatedAt:Date.now()};saveDb(db)
}
function getOrCreateWorldState(world,clientSnapshot){
  let state=worldStates.get(world)||loadWorldFromDb(world);
  if(!state){state={revision:1,snapshot:sanitizeWorldSnapshot(clientSnapshot),chat:[],updatedAt:Date.now()};worldStates.set(world,state);persistWorld(world,state)}
  return state
}
function applyWorldAction(state,action){
  if(!state||!action||typeof action!=='object')return false;
  const type=String(action.type||'');
  if(type==='drop-remove'){
    const id=String(action.dropId||'').slice(0,80);if(!id)return false;const before=state.snapshot.drops.length;state.snapshot.drops=state.snapshot.drops.filter(d=>d.id!==id);if(state.snapshot.drops.length!==before){state.revision++;state.updatedAt=Date.now()}return true
  }
  const tx=Math.floor(Number(action.tx)),ty=Math.floor(Number(action.ty));if(!Number.isFinite(tx)||!Number.isFinite(ty)||tx<0||ty<0||tx>=100||ty>=100)return false;
  const px=tx*40,py=ty*40,key=(b)=>Math.floor(Number(b.x)/40)===tx&&Math.floor(Number(b.y)/40)===ty;let changed=false;
  if(type==='break'){
    const before=state.snapshot.blocks.length;state.snapshot.blocks=state.snapshot.blocks.filter(b=>!key(b));changed=state.snapshot.blocks.length!==before
  }else if(type==='place'){
    const bt=String(action.blockType||'').slice(0,32);if(!bt)return false;const existing=state.snapshot.blocks.find(key);if(existing){if(existing.t!==bt)return false}else{state.snapshot.blocks.push({x:px,y:py,t:bt});changed=true}
  }else if(type==='break-bg'){
    const k=tx+','+ty;if(!state.snapshot.caveBgRemoved.includes(k)){state.snapshot.caveBgRemoved.push(k);changed=true}
  }else if(type==='plant-upsert'){
    const plant=sanitizePlant(action.plant,tx,ty);if(!plant)return false;const i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty);if(i>=0)state.snapshot.plants[i]=plant;else state.snapshot.plants.push(plant);changed=true
  }else if(type==='plant-remove'){
    const before=state.snapshot.plants.length;state.snapshot.plants=state.snapshot.plants.filter(p=>!(Number(p.tx)===tx&&Number(p.ty)===ty));changed=state.snapshot.plants.length!==before
  }else if(type==='harvest'){
    const before=state.snapshot.plants.length;state.snapshot.plants=state.snapshot.plants.filter(p=>!(Number(p.tx)===tx&&Number(p.ty)===ty));changed=state.snapshot.plants.length!==before;
    const add=Array.isArray(action.drops)?action.drops.slice(0,40).map(sanitizeDrop).filter(Boolean):[];for(const d of add)if(!state.snapshot.drops.some(x=>x.id===d.id))state.snapshot.drops.push(d);if(add.length)changed=true
  }else return false;
  if(changed){state.revision++;state.updatedAt=Date.now()}return true
}
function sanitizePlayerSave(input){
  if(!input||typeof input!=='object')return null;
  const inv={};for(const [k,v] of Object.entries(input.inventory||{}).slice(0,500)){const n=Math.max(0,Math.min(200,Math.floor(Number(v||0))));if(n>0)inv[String(k).slice(0,40)]=n}
  const eq={};for(const [k,v] of Object.entries(input.equipped||{}).slice(0,50))eq[String(k).slice(0,32)]=v==null?null:String(v).slice(0,40);
  return {version:4,inventory:inv,equipped:eq,gems:Math.max(0,Math.min(999999999,Math.floor(Number(input.gems||0)))),backpackCapacity:Math.max(24,Math.min(5000,Math.floor(Number(input.backpackCapacity||24)))),backpackUpgrades:Math.max(0,Math.min(500,Math.floor(Number(input.backpackUpgrades||0)))),playerLevel:Math.max(1,Math.min(999,Math.floor(Number(input.playerLevel||1)))),playerXp:Math.max(0,Math.min(999999999,Math.floor(Number(input.playerXp||0)))),quickSlots:Array.isArray(input.quickSlots)?input.quickSlots.slice(0,3).map(v=>v?String(v).slice(0,40):null):[null,null,null],savedAt:Date.now()}
}

async function api(req,res){
  if(req.method==='OPTIONS'){res.writeHead(204,{'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});return res.end()}
  if(req.method!=='POST')return send(res,405,{error:'METHOD_NOT_ALLOWED'});
  let body={};try{body=await readJson(req)}catch(_){return send(res,400,{error:'BAD_REQUEST'})}
  const db=loadDb();

  if(req.url==='/api/guest'){
    const base=cleanName(body.name),player={playerId:'G-'+crypto.randomUUID(),displayName:`${base}_#${suffix()}`,accountType:'guest'},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)})
  }
  if(req.url==='/api/register'){
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||'');
    if(!/^[A-Za-z0-9]{3,24}$/.test(rawId))return send(res,400,{error:'BAD_ID'});
    if(pw.length<6)return send(res,400,{error:'BAD_REQUEST'});
    if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});
    const account={id,username:rawId,playerId:'A-'+crypto.randomUUID(),displayName:rawId,pass:hashPassword(pw),playerSave:null,createdAt:Date.now()};db.accounts[id]=account;saveDb(db);
    const player={playerId:account.playerId,displayName:rawId,accountId:id,accountType:'account'},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:null})
  }
  if(req.url==='/api/login'){
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),account=db.accounts[id];
    if(!account)return send(res,404,{error:'ACCOUNT_NOT_FOUND'});
    if(!verifyPassword(pw,account.pass))return send(res,401,{error:'INVALID_CREDENTIALS'});
    let changed=false;if(!account.username){account.username=String(account.displayName||account.id||rawId).replace(/_#\d{4}$/,'');changed=true}if(account.displayName!==account.username){account.displayName=account.username;changed=true}if(!('playerSave' in account)){account.playerSave=null;changed=true}if(changed){db.accounts[id]=account;saveDb(db)}
    const player={playerId:account.playerId,displayName:account.username,accountId:id,accountType:'account'},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:account.playerSave||null})
  }

  const auth=requireSession(req,res);if(!auth)return;const {token:t,session}=auth;

  if(req.url==='/api/session'){
    const account=session.player.accountType==='account'?db.accounts[session.player.accountId]:null;return send(res,200,{token:t,player:playerPayload(session.player),playerSave:account?.playerSave||null})
  }
  if(req.url==='/api/player/save'){
    if(session.player.accountType!=='account')return send(res,403,{error:'ACCOUNT_REQUIRED'});const account=db.accounts[session.player.accountId];if(!account)return send(res,404,{error:'ACCOUNT_NOT_FOUND'});const save=sanitizePlayerSave(body.save);if(!save)return send(res,400,{error:'BAD_SAVE'});account.playerSave=save;db.accounts[session.player.accountId]=account;saveDb(db);return send(res,200,{ok:true,savedAt:save.savedAt})
  }
  if(req.url==='/api/player/load'){
    if(session.player.accountType!=='account')return send(res,403,{error:'ACCOUNT_REQUIRED'});const account=db.accounts[session.player.accountId];return send(res,200,{ok:true,playerSave:account?.playerSave||null})
  }
  if(req.url==='/api/logout'){
    removePresence(session.player.playerId);sessions.delete(t);if(session.player.accountType==='account'&&activeAccountTokens.get(session.player.accountId)===t)activeAccountTokens.delete(session.player.accountId);return send(res,200,{ok:true})
  }
  if(req.url==='/api/world/join'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});for(const [w,room] of worldPresence){if(w!==world){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(w)}}updatePresence(world,session.player,body);const state=getOrCreateWorldState(world,body.worldSnapshot);return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),revision:state.revision,worldSnapshot:state.snapshot,chat:(state.chat||[]).slice(-30)})
  }
  if(req.url==='/api/world/state'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});updatePresence(world,session.player,body);const state=getOrCreateWorldState(world,body.worldSnapshot);const known=Math.max(0,Number(body.knownRevision||0));return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),revision:state.revision,...(known<state.revision?{worldSnapshot:state.snapshot}:{}),chat:(state.chat||[]).slice(-30),serverTime:Date.now()})
  }
  if(req.url==='/api/world/action'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=getOrCreateWorldState(world,null),accepted=applyWorldAction(state,body.action);if(accepted)persistWorld(world,state);return send(res,accepted?200:409,{ok:accepted,world,revision:state.revision,actionId:String(body.actionId||'').slice(0,80),...(accepted?{}:{error:'ACTION_REJECTED'})})
  }
  if(req.url==='/api/world/chat'){
    const world=cleanWorld(body.world),text=String(body.text||'').trim().replace(/\s+/g,' ').slice(0,100);if(!world||!text)return send(res,400,{error:'BAD_REQUEST'});const state=getOrCreateWorldState(world,null);const msg={id:'C-'+Date.now().toString(36)+'-'+crypto.randomBytes(3).toString('hex'),playerId:session.player.playerId,name:session.player.displayName,text,at:Date.now()};state.chat=(state.chat||[]).concat(msg).slice(-30);persistWorld(world,state);return send(res,200,{ok:true,chat:state.chat})
  }
  if(req.url==='/api/world/leave'){
    const world=cleanWorld(body.world),room=worldPresence.get(world);if(room){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}return send(res,200,{ok:true})
  }
  return send(res,404,{error:'NOT_FOUND'})
}

function staticFile(req,res){
  let url=req.url.split('?')[0];if(url==='/')url='/index.html';const file=path.normalize(path.join(ROOT,url));if(!file.startsWith(ROOT))return send(res,403,{error:'FORBIDDEN'});
  fs.readFile(file,(err,data)=>{if(err){res.writeHead(200,{'Content-Type':'text/plain; charset=utf-8'});return res.end('Pixora Server Build 14.5 is live')}const ext=path.extname(file),type=ext==='.html'?'text/html; charset=utf-8':ext==='.js'?'application/javascript':'application/octet-stream';res.writeHead(200,{'Content-Type':type});res.end(data)})
}
const server=http.createServer((req,res)=>{if(req.url.startsWith('/api/'))return api(req,res);return staticFile(req,res)});
server.listen(PORT,()=>console.log(`Pixora Build 14.5 server running on port ${PORT}`));
