'use strict';

const http=require('http');
const fs=require('fs');
const path=require('path');
const crypto=require('crypto');
let PgPool=null;
try{PgPool=require('pg').Pool}catch(_){ }

const PORT=Number(process.env.PORT||3000);
const ROOT=path.join(__dirname,'public');
const FILE_DB=path.join(__dirname,'accounts.json');
const DATABASE_URL=String(process.env.DATABASE_URL||'').trim();
const sessions=new Map();
const revokedTokens=new Map();
const activeAccountTokens=new Map();
const worldPresence=new Map();
const worldStates=new Map();
const knockbackEvents=new Map();
const trades=new Map();
const tradeByPlayer=new Map();
const MAX_SERVER_PLAYERS=100;
const MAX_WORLD_PLAYERS=20;

let dbCache={accounts:{},worlds:{}};
let pgPool=null;
let storageMode='file';
let persistQueue=Promise.resolve();

function cleanWorld(v){return String(v||'').trim().toUpperCase().replace(/[^A-Z0-9_-]/g,'').slice(0,18)}
function cleanId(v){return String(v||'').trim().toLowerCase().replace(/[^a-z0-9]/g,'').slice(0,24)}
function cleanName(v){let s=String(v||'Player').trim().replace(/[^\p{L}\p{N}_ -]/gu,'').slice(0,12);return s||'Player'}
function cleanGuestId(v){return String(v||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,64)}
function guestSuffix(id){const n=parseInt(crypto.createHash('sha256').update(String(id)).digest('hex').slice(0,8),16);return String(1000+(n%9000))}
function suffix(){return String(1000+crypto.randomInt(9000))}
function token(){return crypto.randomBytes(32).toString('hex')}
function randomId(prefix='D'){return `${prefix}-${Date.now().toString(36)}-${crypto.randomBytes(5).toString('hex')}`}
function hashPassword(password,salt=crypto.randomBytes(16).toString('hex')){return {salt,hash:crypto.scryptSync(String(password),salt,64).toString('hex')}}
function verifyPassword(password,stored){
  try{const got=hashPassword(password,stored.salt).hash;return crypto.timingSafeEqual(Buffer.from(got,'hex'),Buffer.from(stored.hash,'hex'))}catch(_){return false}
}
function normalizeDb(d){if(!d||typeof d!=='object')d={};if(!d.accounts||typeof d.accounts!=='object')d.accounts={};if(!d.worlds||typeof d.worlds!=='object')d.worlds={};if(!Array.isArray(d.reports))d.reports=[];return d}
const BUILTIN_OWNER_ACCOUNT={id:'williamx',username:'WilliamX',playerId:'A-1fb8e9b4-6bd5-45fd-8f0a-d09355a4658e',displayName:'WilliamX',email:'',role:'Owner',pass:{salt:'2b0079e1e5a4fafc7d7d524d1edb63bf',hash:'374b741dd8b46cd1a00cdff94bb3280379f892128869551104dd92f9481a290ae726351fb0acc77b8d6cfddeaf743668a451ebf648edc1415b14f0e7dfbe83af'},playerSave:null,createdAt:1789017712504,builtInOwner:true};
function ensureBuiltInOwner(db){
  db=normalizeDb(db);let changed=false;
  const legacy=db.accounts.pixoraowner;
  if(legacy&&legacy.builtInOwner===true){delete db.accounts.pixoraowner;changed=true}
  const existing=db.accounts[BUILTIN_OWNER_ACCOUNT.id];
  if(existing){
    if(existing.role!=='Owner'){existing.role='Owner';changed=true}
    if(existing.username!=='WilliamX'){existing.username='WilliamX';changed=true}
    if(existing.displayName!=='WilliamX'){existing.displayName='WilliamX';changed=true}
    if(existing.builtInOwner!==true){existing.builtInOwner=true;changed=true}
    return changed
  }
  db.accounts[BUILTIN_OWNER_ACCOUNT.id]=JSON.parse(JSON.stringify(BUILTIN_OWNER_ACCOUNT));return true
}
function readFileDb(){try{return normalizeDb(JSON.parse(fs.readFileSync(FILE_DB,'utf8')))}catch(_){return {accounts:{},worlds:{}}}}
function writeFileBackup(db){try{const tmp=FILE_DB+'.tmp';fs.writeFileSync(tmp,JSON.stringify(db,null,2));fs.renameSync(tmp,FILE_DB)}catch(e){console.warn('file backup failed:',e.message)}}
async function initStorage(){
  dbCache=readFileDb();
  ensureBuiltInOwner(dbCache);
  if(DATABASE_URL&&PgPool){
    try{
      pgPool=new PgPool({connectionString:DATABASE_URL,ssl:DATABASE_URL.includes('localhost')?false:{rejectUnauthorized:false}});
      await pgPool.query('CREATE TABLE IF NOT EXISTS pixora_state (id INTEGER PRIMARY KEY, data JSONB NOT NULL, updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW())');
      const r=await pgPool.query('SELECT data FROM pixora_state WHERE id=1');
      let mustPersist=false;
      if(r.rows[0]?.data){dbCache=normalizeDb(r.rows[0].data);mustPersist=ensureBuiltInOwner(dbCache)}
      else{ensureBuiltInOwner(dbCache);mustPersist=true}
      if(mustPersist)await pgPool.query('INSERT INTO pixora_state(id,data,updated_at) VALUES(1,$1::jsonb,NOW()) ON CONFLICT(id) DO UPDATE SET data=EXCLUDED.data, updated_at=NOW()',[JSON.stringify(dbCache)]);
      storageMode='postgres';
      writeFileBackup(dbCache);
      console.log('Pixora persistence: PostgreSQL');
      return;
    }catch(e){console.error('PostgreSQL init failed, using local file fallback:',e.message);try{await pgPool?.end()}catch(_){}pgPool=null}
  }
  ensureBuiltInOwner(dbCache);writeFileBackup(dbCache);
  storageMode='file';
  console.warn('Pixora persistence: local file only. Set DATABASE_URL for durable accounts/worlds across Render redeploys.');
}
function loadDb(){return dbCache}
function saveDb(db){
  dbCache=normalizeDb(db);writeFileBackup(dbCache);
  if(pgPool){
    const snapshot=JSON.stringify(dbCache);
    persistQueue=persistQueue.then(()=>pgPool.query('INSERT INTO pixora_state(id,data,updated_at) VALUES(1,$1::jsonb,NOW()) ON CONFLICT(id) DO UPDATE SET data=EXCLUDED.data, updated_at=NOW()',[snapshot])).catch(e=>console.error('PostgreSQL save failed:',e.message));
  }
}

function send(res,status,obj){
  const data=JSON.stringify(obj);res.writeHead(status,{'Content-Type':'application/json','Content-Length':Buffer.byteLength(data),'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});res.end(data)
}
function readJson(req){return new Promise((resolve,reject)=>{let body='';req.on('data',c=>{body+=c;if(body.length>5_000_000){reject(new Error('PAYLOAD_TOO_LARGE'));req.destroy()}});req.on('end',()=>{try{resolve(body?JSON.parse(body):{})}catch(e){reject(e)}});req.on('error',reject)})}
function authToken(req){const h=String(req.headers.authorization||'');return h.startsWith('Bearer ')?h.slice(7):''}
function playerPayload(p){return {playerId:p.playerId,displayName:p.displayName,accountId:p.accountId||null,accountType:p.accountType,role:p.role||'Player'}}
const OWNER_ACCOUNT_ID=cleanId(process.env.PIXORA_OWNER_ID||'');
function roleForAccount(account){if(!account)return 'Player';if(OWNER_ACCOUNT_ID&&account.id===OWNER_ACCOUNT_ID)return 'Owner';return ['Player','Moderator','Admin','Owner'].includes(account.role)?account.role:'Player'}
function accountByPlayerId(db,playerId){return Object.values(db.accounts||{}).find(a=>a&&a.playerId===playerId)||null}
function sessionByPlayerId(playerId){for(const [t,s] of sessions){if(s?.player?.playerId===playerId)return {token:t,session:s}}return null}
function queueEvent(playerId,ev){const q=knockbackEvents.get(playerId)||[];q.push(ev);knockbackEvents.set(playerId,q.slice(-20))}
function cleanEmail(v){const e=String(v||'').trim().toLowerCase().slice(0,160);return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(e)?e:''}
function publicTrade(trade,db){if(!trade)return null;const label=id=>{const a=accountByPlayerId(db,id);return a?.username||a?.displayName||id};return {id:trade.id,a:trade.a,b:trade.b,status:trade.status,offers:trade.offers,confirmed:trade.confirmed,finalConfirmed:trade.finalConfirmed,names:{[trade.a]:label(trade.a),[trade.b]:label(trade.b)},updatedAt:trade.updatedAt}}
function cancelTradeFor(playerId,reason='CANCELLED'){const id=tradeByPlayer.get(playerId);if(!id)return;const tr=trades.get(id);if(!tr)return;tr.status='cancelled';tr.reason=reason;tr.updatedAt=Date.now();tradeByPlayer.delete(tr.a);tradeByPlayer.delete(tr.b);queueEvent(tr.a,{type:'trade-cancelled',tradeId:id,reason});queueEvent(tr.b,{type:'trade-cancelled',tradeId:id,reason})}


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
  const t=authToken(req);if(revokedTokens.has(t))return {token:t,error:revokedTokens.get(t).reason||'INVALID_SESSION'};
  const session=sessions.get(t);return session?{token:t,session}:{token:t,error:'INVALID_SESSION'}
}
function requireSession(req,res){const s=sessionFor(req);if(s.error){send(res,401,{error:s.error});return null}return s}
setInterval(()=>{const cutoff=Date.now()-6*60*60*1000;for(const [t,v] of revokedTokens)if(v.at<cutoff)revokedTokens.delete(t)},60*60*1000).unref?.();

function pruneRoom(world){const room=worldPresence.get(world);if(!room)return;const cutoff=Date.now()-12000;for(const [id,st] of room){if(st.lastSeen<cutoff)room.delete(id)}if(!room.size)worldPresence.delete(world)}
function sanitizeActionState(a){
  if(!a||typeof a!=='object'||!a.active)return {active:false,seq:Math.max(0,Math.floor(Number(a?.seq||0)))};
  const tx=Math.floor(Number(a.tx)),ty=Math.floor(Number(a.ty));if(!Number.isFinite(tx)||!Number.isFinite(ty))return {active:false,seq:Math.max(0,Math.floor(Number(a.seq||0)))};
  const kind=['block','bg','air'].includes(String(a.kind))?String(a.kind):'air';
  return {active:true,kind,tx,ty,progress:Math.max(0,Math.min(1,Number(a.progress||0))),tool:String(a.tool||'punch').slice(0,16),seq:Math.max(0,Math.floor(Number(a.seq||0)))}
}
function sanitizePresenceEquipment(e){const src=(e&&typeof e==='object')?e:{};const out={};for(const k of ['hair','shirt','pants','shoes','back','tool'])out[k]=src[k]==null?null:String(src[k]).slice(0,40);return out}
function updatePresence(world,p,b){
  if(!worldPresence.has(world))worldPresence.set(world,new Map());
  const room=worldPresence.get(world),prev=room.get(p.playerId)||{};
  room.set(p.playerId,{playerId:p.playerId,displayName:p.displayName,role:p.role||'Player',accountType:p.accountType||'guest',x:Number.isFinite(Number(b.x))?Number(b.x):(prev.x||120),y:Number.isFinite(Number(b.y))?Number(b.y):(prev.y||0),facing:Number(b.facing)<0?-1:1,onGround:!!b.onGround,vx:Number.isFinite(Number(b.vx))?Number(b.vx):0,vy:Number.isFinite(Number(b.vy))?Number(b.vy):0,equipped:sanitizePresenceEquipment(b.equipped||prev.equipped),actionState:sanitizeActionState(b.actionState),lastSeen:Date.now()})
}
function roomView(world,selfId){pruneRoom(world);const room=worldPresence.get(world);return room?[...room.values()].filter(p=>p.playerId!==selfId).map(({lastSeen,...p})=>p):[]}
function activePresenceIds(){const ids=new Set();for(const [w] of worldPresence){pruneRoom(w);const room=worldPresence.get(w);if(room)for(const id of room.keys())ids.add(id)}return ids}
function canJoinWorld(world,playerId){pruneRoom(world);const room=worldPresence.get(world);if(room?.has(playerId))return {ok:true};if((room?.size||0)>=MAX_WORLD_PLAYERS)return {ok:false,error:'WORLD_FULL'};if(activePresenceIds().size>=MAX_SERVER_PLAYERS)return {ok:false,error:'SERVER_FULL'};return {ok:true}}
function tileOccupiedByPlayer(world,tx,ty){pruneRoom(world);const room=worldPresence.get(world);if(!room)return false;const x=tx*40,y=ty*40;for(const p of room.values()){const px=Number(p.x||0),py=Number(p.y||0);if(px< x+40&&px+30>x&&py<y+40&&py+40>y)return true}return false}
function queueKnockback(playerId,ev){queueEvent(playerId,ev)}
function consumeEvents(playerId){const q=knockbackEvents.get(playerId)||[];knockbackEvents.delete(playerId);return q}

function sanitizeDrop(d,{serverId=false}={}){
  if(!d||typeof d!=='object')return null;
  const kind=d.kind==='gems'?'gems':'item',item=kind==='item'?String(d.item||'').slice(0,40):null;
  if(kind==='item'&&!item)return null;
  return {id:serverId?randomId(kind==='gems'?'G':'D'):String(d.id||randomId(kind==='gems'?'G':'D')).slice(0,80),x:Number(d.x)||0,y:Number(d.y)||0,item,kind,amount:Math.max(1,Math.min(9999,Math.floor(Number(d.amount||1)))),pickupAfter:Math.max(0,Number(d.pickupAfter||0))}
}
function sanitizeWorldSnapshot(input){
  const s=(input&&typeof input==='object')?input:{};
  const jammers=Array.isArray(s.jammers)?s.jammers.slice(0,50).filter(j=>j&&Number.isFinite(Number(j.tx))&&Number.isFinite(Number(j.ty))&&String(j.type||'')==='punch').map(j=>({tx:Math.floor(Number(j.tx)),ty:Math.floor(Number(j.ty)),type:'punch',owner:String(j.owner||'').slice(0,80)})):[];
  const blocks=Array.isArray(s.blocks)?s.blocks.slice(0,20000).filter(b=>b&&Number.isFinite(Number(b.x))&&Number.isFinite(Number(b.y))&&typeof b.t==='string').map(b=>({x:Number(b.x),y:Number(b.y),t:String(b.t).slice(0,32)})):[];
  const door=(s.door&&Number.isFinite(Number(s.door.x))&&Number.isFinite(Number(s.door.y)))?{x:Number(s.door.x),y:Number(s.door.y),w:Number(s.door.w)||36,h:Number(s.door.h)||40}:null;
  const placedDoors=Array.isArray(s.placedDoors)?s.placedDoors.slice(0,1000).filter(d=>d&&Number.isFinite(Number(d.tx))&&Number.isFinite(Number(d.ty))&&['woodDoor','worldDoor'].includes(String(d.type||''))).map(d=>({id:String(d.id||randomId('DOOR')).slice(0,80),tx:Math.floor(Number(d.tx)),ty:Math.floor(Number(d.ty)),type:String(d.type),owner:String(d.owner||'').slice(0,80),doorId:String(d.doorId||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,18),targetWorld:cleanWorld(d.targetWorld),targetId:String(d.targetId||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,18),open:!!d.open})):[];
  return {worldId:String(s.worldId||'').slice(0,64),surfaceTile:Number.isFinite(Number(s.surfaceTile))?Number(s.surfaceTile):55,blocks,door,placedDoors,caveBgRemoved:Array.isArray(s.caveBgRemoved)?s.caveBgRemoved.slice(0,12000).filter(v=>typeof v==='string'):[],plants:Array.isArray(s.plants)?s.plants.slice(0,5000):[],locks:Array.isArray(s.locks)?s.locks.slice(0,1000).filter(l=>l&&Number.isFinite(Number(l.tx))&&Number.isFinite(Number(l.ty))).map(l=>({...l,tx:Math.floor(Number(l.tx)),ty:Math.floor(Number(l.ty)),type:String(l.type||'worldLock').slice(0,32),owner:String(l.owner||'').slice(0,80),trusted:Array.isArray(l.trusted)?l.trusted.slice(0,200).map(v=>String(v).slice(0,80)):[]})):[],weatherOrbs:Array.isArray(s.weatherOrbs)?s.weatherOrbs.slice(0,100):[],jammers,worldBans:Array.isArray(s.worldBans)?s.worldBans.slice(0,500).map(v=>String(v).slice(0,80)):[],weather:(s.weather&&typeof s.weather==='object')?{type:String(s.weather.type||'sunny').slice(0,16)}:{type:'sunny'},drops:Array.isArray(s.drops)?s.drops.slice(0,5000).map(sanitizeDrop).filter(Boolean):[]}
}
function sanitizePlant(p,tx,ty){
  if(!p||typeof p!=='object')return null;const seed=String(p.seed||'').slice(0,40);if(!seed)return null;
  return {tx,ty,seed,spliced:!!p.spliced,rarity:Math.max(1,Math.min(99,Number(p.rarity||1))),plantedAt:Math.max(0,Number(p.plantedAt||Date.now())),growMs:Math.max(1000,Number(p.growMs||10000))}
}
function loadWorldFromDb(world){
  const db=loadDb(),raw=db.worlds?.[world];if(!raw)return null;
  const state={revision:Math.max(1,Number(raw.revision||1)),snapshot:sanitizeWorldSnapshot(raw.snapshot),chat:Array.isArray(raw.chat)?raw.chat.slice(-30):[],updatedAt:Number(raw.updatedAt||Date.now())};worldStates.set(world,state);return state
}
function persistWorld(world,state){const db=loadDb();db.worlds[world]={revision:state.revision,snapshot:state.snapshot,chat:(state.chat||[]).slice(-30),updatedAt:Date.now()};saveDb(db)}
function getOrCreateWorldState(world,clientSnapshot){let state=worldStates.get(world)||loadWorldFromDb(world);if(!state){state={revision:1,snapshot:sanitizeWorldSnapshot(clientSnapshot),chat:[],updatedAt:Date.now()};worldStates.set(world,state);persistWorld(world,state)}return state}

const DROP_RATE={grass:{block:.42,seed:.30,gems:.28},dirt:{block:.38,seed:.20,gems:.24},stone:{block:.32,seed:.08,gems:.34},wood:{block:.45,seed:.24,gems:.25},leaf:{block:.24,seed:.42,gems:.22},sand:{block:.40,seed:.18,gems:.22},glass:{block:.31,seed:.12,gems:.38},brick:{block:.36,seed:.12,gems:.32},ice:{block:.34,seed:.22,gems:.30},metal:{block:.28,seed:.06,gems:.46},caveStone:{block:.32,seed:.10,gems:.40},moss:{block:.36,seed:.34,gems:.24},lava:{block:.22,seed:0,gems:.44},farmBlock:{block:.46,seed:.34,gems:.38},woodPlatform:{block:.45,seed:.20,gems:.20},woodDoor:{block:.40,seed:.16,gems:.24},worldDoor:{block:.30,seed:.10,gems:.34}};
const SEED_FOR_BLOCK={grass:'grassSeed',dirt:'dirtSeed',stone:'stoneSeed',wood:'woodSeed',leaf:'leafSeed',sand:'sandSeed',glass:'glassSeed',brick:'brickSeed',ice:'iceSeed',metal:'metalSeed',caveStone:'caveStoneSeed',moss:'mossSeed',farmBlock:'farmSeed',woodPlatform:'platformSeed',woodDoor:'doorSeed',worldDoor:'worldDoorSeed'};
const BLOCK_RARITY={grass:1,dirt:1,stone:1,caveStone:1,lava:1,wood:2,leaf:2,sand:2,brick:3,moss:3,glass:4,ice:3,metal:3,farmBlock:8,woodPlatform:3,woodDoor:5,worldDoor:10,bedrock:99};
const PLANT_BLOCK={grassSeed:'grass',dirtSeed:'dirt',stoneSeed:'stone',woodSeed:'wood',leafSeed:'leaf',sandSeed:'sand',glassSeed:'glass',brickSeed:'brick',iceSeed:'ice',metalSeed:'metal',caveStoneSeed:'caveStone',mossSeed:'moss',farmSeed:'farmBlock',platformSeed:'woodPlatform',doorSeed:'woodDoor',worldDoorSeed:'worldDoor'};
const PLANT_YIELD={grassSeed:[1,3],dirtSeed:[1,4],stoneSeed:[1,2],woodSeed:[2,4],leafSeed:[1,3],sandSeed:[1,4],glassSeed:[1,2],brickSeed:[1,3],iceSeed:[1,3],metalSeed:[1,2],caveStoneSeed:[1,3],mossSeed:[1,4],farmSeed:[1,3],platformSeed:[1,3],doorSeed:[1,2],worldDoorSeed:[1,1]};
function gemAmountForRarity(r){r=Math.max(1,Number(r||1));if(r<=10)return 1;const max=1+Math.floor((r-1)/10);return 1+Math.floor(Math.random()*max)}
function seedRarity(seed){const block=PLANT_BLOCK[seed];return BLOCK_RARITY[block]||1}
function seedGemChance(seed){const r=seedRarity(seed);return Math.min(.48,.08+r*.025)}
function seedGemAmount(seed){return seed==='farmSeed'?1+crypto.randomInt(14):gemAmountForRarity(seedRarity(seed))}
function makeDrop(tx,ty,item,amount=1,kind='item',delay=250,spread=16){return sanitizeDrop({x:tx*40+20+(Math.random()-.5)*spread,y:ty*40+20+(Math.random()-.5)*10,item,kind,amount,pickupAfter:Date.now()+delay},{serverId:true})}
function addDrops(state,list){const added=[];for(const d of list.filter(Boolean)){if(state.snapshot.drops.length>=5000)break;state.snapshot.drops.push(d);added.push(d)}return added}
function generateBreakDrops(blockType,tx,ty){
  // Build 14.6.3: Block + Seed kembali memakai drop-rate farming lama. Clothes/Wearable tetap Store-only.
  const out=[],rate=DROP_RATE[blockType]||{block:.25,seed:0,gems:.25},r=Math.random();
  if(r<rate.block)out.push(makeDrop(tx,ty,blockType));
  else if(rate.seed>0&&r<rate.block+rate.seed){const seed=SEED_FOR_BLOCK[blockType];if(seed)out.push(makeDrop(tx,ty,seed))}
  if(Math.random()<(rate.gems||.25)){const amount=blockType==='farmBlock'?1+crypto.randomInt(14):gemAmountForRarity(BLOCK_RARITY[blockType]||1);out.push(makeDrop(tx,ty,null,amount,'gems',0,12))}
  return out;
}
function generateHarvestDrops(plant,tx,ty){
  const seed=String(plant.seed||''),block=PLANT_BLOCK[seed]||'dirt',range=PLANT_YIELD[seed]||[1,3],amount=range[0]+crypto.randomInt(range[1]-range[0]+1),out=[];
  for(let i=0;i<amount;i++)out.push(makeDrop(tx,ty,block,1,'item',250,20));
  if(Math.random()<.46)out.push(makeDrop(tx,ty,seed));
  if(Math.random()<.10)out.push(makeDrop(tx,ty,seed));
  if(Math.random()<seedGemChance(seed))out.push(makeDrop(tx,ty,null,seedGemAmount(seed),'gems',0,12));
  return {drops:out,amount,item:block};
}

function applyWorldAction(state,action,session,world){
  if(!state||!action||typeof action!=='object')return {accepted:false};
  const type=String(action.type||'');
  if(type==='player-punch'){
    const sourceId=session?.player?.playerId,targetId=String(action.targetPlayerId||'').slice(0,80),room=worldPresence.get(world);
    if(!sourceId||!targetId||targetId===sourceId||!room)return {accepted:false};pruneRoom(world);
    const src=room.get(sourceId),target=room.get(targetId);if(!src||!target)return {accepted:false};
    if(Array.isArray(state.snapshot.jammers)&&state.snapshot.jammers.some(j=>j?.type==='punch'))return {accepted:true,blocked:true};
    const sx=Number(src.x||0)+15,sy=Number(src.y||0)+20,txp=Number(target.x||0)+15,typ=Number(target.y||0)+20,dx=txp-sx,dy=Math.abs(typ-sy),facing=Number(src.facing)<0?-1:1;
    if(Math.sign(dx||facing)!==facing||Math.abs(dx)>98||dy>42)return {accepted:false};
    queueKnockback(targetId,{type:'knockback',vx:facing*4.8,vy:-5.8,from:sourceId,at:Date.now()});return {accepted:true,knockback:true,targetId};
  }
  if(type==='world-command'){
    const sourceId=session?.player?.playerId,targetId=String(action.targetPlayerId||'').slice(0,80),cmd=String(action.command||'');
    const wl=Array.isArray(state.snapshot.locks)&&state.snapshot.locks.find(l=>l?.type==='worldLock'&&String(l.owner||'')===sourceId);
    const room=worldPresence.get(world);pruneRoom(world);const src=room?.get(sourceId),target=room?.get(targetId);
    if(!wl||!src||!target||targetId===sourceId)return {accepted:false};
    if(cmd==='pull'){queueEvent(targetId,{type:'pull',world,x:Number(src.x||0),y:Number(src.y||0)-44,from:sourceId});return {accepted:true,command:'pull'}}
    if(cmd==='kick'){queueEvent(targetId,{type:'world-kick',world,reason:'KICKED',from:sourceId});return {accepted:true,command:'kick'}}
    if(cmd==='ban'){state.snapshot.worldBans=Array.isArray(state.snapshot.worldBans)?state.snapshot.worldBans:[];if(!state.snapshot.worldBans.includes(targetId))state.snapshot.worldBans.push(targetId);state.revision++;state.updatedAt=Date.now();queueEvent(targetId,{type:'world-kick',world,reason:'BANNED',from:sourceId});return {accepted:true,command:'ban',changed:true}}
    return {accepted:false};
  }
  if(type==='drop-pickup'){
    const id=String(action.dropId||'').slice(0,80);if(!id)return {accepted:false};const i=state.snapshot.drops.findIndex(d=>d.id===id);if(i<0)return {accepted:false};const [d]=state.snapshot.drops.splice(i,1);state.revision++;state.updatedAt=Date.now();return {accepted:true,reward:{kind:d.kind,item:d.item||null,amount:d.amount||1}}
  }
  if(type==='drop-remove'){
    const id=String(action.dropId||'').slice(0,80);if(!id)return {accepted:false};const before=state.snapshot.drops.length;state.snapshot.drops=state.snapshot.drops.filter(d=>d.id!==id);if(state.snapshot.drops.length===before)return {accepted:false};state.revision++;state.updatedAt=Date.now();return {accepted:true}
  }
  if(type==='drop-add'){
    const d=sanitizeDrop(action.drop,{serverId:true});if(!d)return {accepted:false};const added=addDrops(state,[d]);if(!added.length)return {accepted:false};state.revision++;state.updatedAt=Date.now();return {accepted:true,dropsAdded:added}
  }

  const tx=Math.floor(Number(action.tx)),ty=Math.floor(Number(action.ty));if(!Number.isFinite(tx)||!Number.isFinite(ty)||tx<0||ty<0||tx>=100||ty>=100)return {accepted:false};
  const px=tx*40,py=ty*40,key=(b)=>Math.floor(Number(b.x)/40)===tx&&Math.floor(Number(b.y)/40)===ty;let changed=false,dropsAdded=[],result={};
  if(type==='break'){
    const i=state.snapshot.blocks.findIndex(key);if(i<0)return {accepted:false};const [removed]=state.snapshot.blocks.splice(i,1);if(removed.t==='bedrock'){state.snapshot.blocks.splice(i,0,removed);return {accepted:false}}changed=true;dropsAdded=addDrops(state,generateBreakDrops(removed.t,tx,ty));
  }else if(type==='place'){
    const bt=String(action.blockType||'').slice(0,32);if(!bt)return {accepted:false};const existing=state.snapshot.blocks.find(key);if(existing||tileOccupiedByPlayer(world,tx,ty)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};state.snapshot.blocks.push({x:px,y:py,t:bt});changed=true;
  }else if(type==='lock-place'){
    const lt=String(action.lockType||'').slice(0,32);if(!['smallLock','bigLock','hugeLock','worldLock'].includes(lt))return {accepted:false};
    if(tileOccupiedByPlayer(world,tx,ty)||state.snapshot.blocks.some(key)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};
    if(lt==='worldLock'&&state.snapshot.locks.some(l=>l?.type==='worldLock'))return {accepted:false};
    state.snapshot.locks.push({tx,ty,type:lt,owner:session?.player?.playerId||'',trusted:[],hitsTaken:0});changed=true;
  }else if(type==='lock-remove'){
    const i=state.snapshot.locks.findIndex(l=>Number(l.tx)===tx&&Number(l.ty)===ty);if(i<0)return {accepted:false};const l=state.snapshot.locks[i];if(String(l.owner||'')!==session?.player?.playerId)return {accepted:false};state.snapshot.locks.splice(i,1);changed=true;
  }else if(type==='door-place'){
    const dt=String(action.doorType||'');if(!['woodDoor','worldDoor'].includes(dt))return {accepted:false};
    if(tileOccupiedByPlayer(world,tx,ty)||state.snapshot.blocks.some(key)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};
    const d={id:randomId('DOOR'),tx,ty,type:dt,owner:session?.player?.playerId||'',doorId:'',targetWorld:'',targetId:'',open:false};state.snapshot.placedDoors.push(d);changed=true;result.door=d;
  }else if(type==='door-update'){
    const i=state.snapshot.placedDoors.findIndex(d=>Number(d.tx)===tx&&Number(d.ty)===ty);if(i<0)return {accepted:false};const d=state.snapshot.placedDoors[i];if(String(d.owner||'')!==session?.player?.playerId)return {accepted:false};if(d.type==='worldDoor'){d.doorId=String(action.doorId||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,18);d.targetWorld=cleanWorld(action.targetWorld);d.targetId=String(action.targetId||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,18)}else d.open=!!action.open;changed=true;result.door=d;
  }else if(type==='door-remove'){
    const i=state.snapshot.placedDoors.findIndex(d=>Number(d.tx)===tx&&Number(d.ty)===ty);if(i<0)return {accepted:false};const d=state.snapshot.placedDoors[i];if(String(d.owner||'')!==session?.player?.playerId)return {accepted:false};state.snapshot.placedDoors.splice(i,1);changed=true;result.removedDoor=d;
  }else if(type==='jammer-place'){
    if(tileOccupiedByPlayer(world,tx,ty)||state.snapshot.blocks.some(key)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};state.snapshot.jammers.push({tx,ty,type:'punch',owner:session?.player?.playerId||''});changed=true;
  }else if(type==='jammer-remove'){
    const i=state.snapshot.jammers.findIndex(j=>Number(j.tx)===tx&&Number(j.ty)===ty&&j.type==='punch');if(i<0)return {accepted:false};const j=state.snapshot.jammers[i];if(j.owner&&j.owner!==session?.player?.playerId)return {accepted:false};state.snapshot.jammers.splice(i,1);changed=true;
  }else if(type==='break-bg'){
    const k=tx+','+ty;if(state.snapshot.caveBgRemoved.includes(k))return {accepted:false};state.snapshot.caveBgRemoved.push(k);changed=true;
    // Cave Background always yields its farmable seed in Build 14.6.
    dropsAdded=addDrops(state,[makeDrop(tx,ty,'caveStoneSeed',1,'item',250,14)]);
  }else if(type==='plant-upsert'){
    const plant=sanitizePlant(action.plant,tx,ty);if(!plant)return {accepted:false};const i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty);if(i>=0)state.snapshot.plants[i]=plant;else state.snapshot.plants.push(plant);changed=true;
  }else if(type==='plant-remove'){
    const before=state.snapshot.plants.length;state.snapshot.plants=state.snapshot.plants.filter(p=>!(Number(p.tx)===tx&&Number(p.ty)===ty));changed=state.snapshot.plants.length!==before;
  }else if(type==='harvest'){
    const i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty);if(i<0)return {accepted:false};const [plant]=state.snapshot.plants.splice(i,1);const harvest=generateHarvestDrops(plant,tx,ty);dropsAdded=addDrops(state,harvest.drops);changed=true;result.harvestAmount=harvest.amount;result.harvestItem=harvest.item;
  }else return {accepted:false};
  if(changed){state.revision++;state.updatedAt=Date.now()}
  return {accepted:changed,dropsAdded,...result};
}

function sanitizePlayerSave(input){
  if(!input||typeof input!=='object')return null;
  const inv={};for(const [k,v] of Object.entries(input.inventory||{}).slice(0,500)){const n=Math.max(0,Math.min(200,Math.floor(Number(v||0))));if(n>0)inv[String(k).slice(0,40)]=n}
  const eq={};for(const [k,v] of Object.entries(input.equipped||{}).slice(0,50))eq[String(k).slice(0,32)]=v==null?null:String(v).slice(0,40);
  return {version:6,inventory:inv,equipped:eq,gems:Math.max(0,Math.min(999999999,Math.floor(Number(input.gems||0)))),backpackCapacity:Math.max(24,Math.min(5000,Math.floor(Number(input.backpackCapacity||24)))),backpackUpgrades:Math.max(0,Math.min(500,Math.floor(Number(input.backpackUpgrades||0)))),playerLevel:Math.max(1,Math.min(999,Math.floor(Number(input.playerLevel||1)))),playerXp:Math.max(0,Math.min(999999999,Math.floor(Number(input.playerXp||0)))),quickSlots:Array.isArray(input.quickSlots)?input.quickSlots.slice(0,3).map(v=>v?String(v).slice(0,40):null):[null,null,null],friends:Array.isArray(input.friends)?input.friends.slice(0,500).map(v=>String(v).slice(0,80)):[],blocked:Array.isArray(input.blocked)?input.blocked.slice(0,500).map(v=>String(v).slice(0,80)):[],ignored:Array.isArray(input.ignored)?input.ignored.slice(0,500).map(v=>String(v).slice(0,80)):[],savedAt:Date.now()}
}

async function api(req,res){
  if(req.method==='OPTIONS'){res.writeHead(204,{'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});return res.end()}
  if(req.method!=='POST')return send(res,405,{error:'METHOD_NOT_ALLOWED'});
  let body={};try{body=await readJson(req)}catch(_){return send(res,400,{error:'BAD_REQUEST'})}
  const db=loadDb();

  if(req.url==='/api/status')return send(res,200,{ok:true,build:'14.7.0',storage:storageMode,persistent:storageMode==='postgres'});
  if(req.url==='/api/guest'){
    const base=cleanName(body.name),guestId=cleanGuestId(body.guestId)||crypto.randomUUID(),player={playerId:'G-'+guestId,displayName:`${base}_#${guestSuffix(guestId)}`,accountType:'guest',role:'Player'},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)})
  }
  if(req.url==='/api/register'){
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),confirm=String(body.confirmPassword||''),email=cleanEmail(body.email);
    if(!/^[A-Za-z0-9]{3,24}$/.test(rawId))return send(res,400,{error:'BAD_ID'});
    if(pw.length<6||pw!==confirm||!email)return send(res,400,{error:pw!==confirm?'PASSWORD_MISMATCH':(!email?'BAD_EMAIL':'BAD_REQUEST')});
    if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});
    if(Object.values(db.accounts).some(a=>String(a.email||'').toLowerCase()===email))return send(res,409,{error:'EMAIL_EXISTS'});
    const account={id,username:rawId,playerId:'A-'+crypto.randomUUID(),displayName:rawId,email,role:(OWNER_ACCOUNT_ID&&id===OWNER_ACCOUNT_ID)?'Owner':'Player',pass:hashPassword(pw),playerSave:null,createdAt:Date.now()};db.accounts[id]=account;saveDb(db);
    const player={playerId:account.playerId,displayName:rawId,accountId:id,accountType:'account',role:roleForAccount(account)},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:null})
  }
  if(req.url==='/api/login'){
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),account=db.accounts[id];
    if(!account)return send(res,404,{error:'ACCOUNT_NOT_FOUND'});
    if(!verifyPassword(pw,account.pass))return send(res,401,{error:'INVALID_CREDENTIALS'});
    let changed=false;if(!account.username){account.username=String(account.displayName||account.id||rawId).replace(/_#\d{4}$/,'');changed=true}if(account.displayName!==account.username){account.displayName=account.username;changed=true}if(!('playerSave' in account)){account.playerSave=null;changed=true}if(!account.role){account.role=(OWNER_ACCOUNT_ID&&id===OWNER_ACCOUNT_ID)?'Owner':'Player';changed=true}if(changed){db.accounts[id]=account;saveDb(db)}
    const player={playerId:account.playerId,displayName:account.username,accountId:id,accountType:'account',role:roleForAccount(account)},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:account.playerSave||null})
  }

  const auth=requireSession(req,res);if(!auth)return;const {token:t,session}=auth;
  if(req.url==='/api/guest/convert'){
    if(session.player.accountType!=='guest')return send(res,409,{error:'ALREADY_ACCOUNT'});
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),confirm=String(body.confirmPassword||''),email=cleanEmail(body.email);
    if(!/^[A-Za-z0-9]{3,24}$/.test(rawId))return send(res,400,{error:'BAD_ID'});if(pw.length<6||pw!==confirm||!email)return send(res,400,{error:pw!==confirm?'PASSWORD_MISMATCH':(!email?'BAD_EMAIL':'BAD_REQUEST')});
    if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});if(Object.values(db.accounts).some(a=>String(a.email||'').toLowerCase()===email))return send(res,409,{error:'EMAIL_EXISTS'});
    const save=sanitizePlayerSave(body.save)||null,account={id,username:rawId,playerId:session.player.playerId,displayName:rawId,email,role:(OWNER_ACCOUNT_ID&&id===OWNER_ACCOUNT_ID)?'Owner':'Player',pass:hashPassword(pw),playerSave:save,createdAt:Date.now(),convertedGuest:true};db.accounts[id]=account;saveDb(db);
    session.player={playerId:account.playerId,displayName:rawId,accountId:id,accountType:'account',role:roleForAccount(account)};activeAccountTokens.set(id,t);return send(res,200,{token:t,player:playerPayload(session.player),playerSave:save})
  }
  if(req.url==='/api/player/profile'){
    const targetId=String(body.playerId||session.player.playerId).slice(0,80);let target=sessionByPlayerId(targetId)?.session?.player||null;const acc=accountByPlayerId(db,targetId);if(!target&&acc)target={playerId:acc.playerId,displayName:acc.username||acc.displayName,accountId:acc.id,accountType:'account',role:roleForAccount(acc)};
    if(!target)return send(res,404,{error:'PLAYER_NOT_FOUND'});const save=acc?.playerSave||null;return send(res,200,{ok:true,profile:{...playerPayload(target),level:Math.max(1,Number(save?.playerLevel||1)),xp:Math.max(0,Number(save?.playerXp||0)),equipped:save?.equipped||{}}})
  }
  if(req.url==='/api/report'){
    const targetPlayerId=String(body.targetPlayerId||'').slice(0,80),reason=String(body.reason||'').trim().slice(0,240);if(!targetPlayerId||targetPlayerId===session.player.playerId)return send(res,400,{error:'BAD_REQUEST'});db.reports.push({id:randomId('R'),from:session.player.playerId,target:targetPlayerId,reason:reason||'Player report',at:Date.now(),world:cleanWorld(body.world)});db.reports=db.reports.slice(-2000);saveDb(db);return send(res,200,{ok:true})
  }
  if(req.url==='/api/mod/reports'){
    if(!['Moderator','Admin','Owner'].includes(String(session.player.role||'Player')))return send(res,403,{error:'MODERATOR_REQUIRED'});
    return send(res,200,{ok:true,reports:(db.reports||[]).slice(-100).reverse()})
  }
  if(req.url==='/api/mod/role'){
    if((session.player.role||'Player')!=='Owner')return send(res,403,{error:'OWNER_REQUIRED'});const target=accountByPlayerId(db,String(body.targetPlayerId||''));const role=String(body.role||'Player');if(!target||!['Player','Moderator','Admin'].includes(role))return send(res,400,{error:'BAD_REQUEST'});target.role=role;saveDb(db);const live=sessionByPlayerId(target.playerId)?.session;if(live)live.player.role=role;return send(res,200,{ok:true,playerId:target.playerId,role})
  }
  if(req.url==='/api/trade/request'){
    if(session.player.accountType!=='account')return send(res,403,{error:'ACCOUNT_REQUIRED'});const targetId=String(body.targetPlayerId||'').slice(0,80),targetSession=sessionByPlayerId(targetId)?.session;if(!targetSession||targetSession.player.accountType!=='account'||targetId===session.player.playerId)return send(res,400,{error:'PLAYER_NOT_AVAILABLE'});if(tradeByPlayer.has(session.player.playerId)||tradeByPlayer.has(targetId))return send(res,409,{error:'TRADE_BUSY'});
    const id=randomId('T'),tr={id,a:session.player.playerId,b:targetId,status:'pending',offers:{[session.player.playerId]:{},[targetId]:{}},confirmed:{[session.player.playerId]:false,[targetId]:false},finalConfirmed:{[session.player.playerId]:false,[targetId]:false},updatedAt:Date.now()};trades.set(id,tr);tradeByPlayer.set(tr.a,id);tradeByPlayer.set(tr.b,id);queueEvent(targetId,{type:'trade-request',tradeId:id,from:tr.a,name:session.player.displayName});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/accept'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||tr.b!==session.player.playerId||tr.status!=='pending')return send(res,409,{error:'TRADE_INVALID'});tr.status='active';tr.updatedAt=Date.now();queueEvent(tr.a,{type:'trade-open',tradeId:id});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/state'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||![tr.a,tr.b].includes(session.player.playerId))return send(res,404,{error:'TRADE_NOT_FOUND'});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/offer'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||tr.status!=='active'||![tr.a,tr.b].includes(session.player.playerId))return send(res,409,{error:'TRADE_INVALID'});const acc=accountByPlayerId(db,session.player.playerId),inv=acc?.playerSave?.inventory||{};if(!acc?.playerSave)return send(res,409,{error:'SAVE_REQUIRED'});const offer={};for(const [item,raw] of Object.entries(body.offer||{}).slice(0,8)){const n=Math.max(0,Math.min(200,Math.floor(Number(raw||0))));if(!n||item==='spliceBook')continue;if(Number(inv[item]||0)<n)return send(res,409,{error:'ITEM_CHANGED'});offer[String(item).slice(0,40)]=n}tr.offers[session.player.playerId]=offer;tr.confirmed[tr.a]=tr.confirmed[tr.b]=false;tr.finalConfirmed[tr.a]=tr.finalConfirmed[tr.b]=false;tr.status='active';tr.updatedAt=Date.now();queueEvent(tr.a,{type:'trade-updated',tradeId:id});queueEvent(tr.b,{type:'trade-updated',tradeId:id});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/confirm'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||![tr.a,tr.b].includes(session.player.playerId))return send(res,409,{error:'TRADE_INVALID'});const pid=session.player.playerId;
    if(tr.status==='active'){tr.confirmed[pid]=true;if(tr.confirmed[tr.a]&&tr.confirmed[tr.b]){tr.status='locked';tr.finalConfirmed[tr.a]=tr.finalConfirmed[tr.b]=false}tr.updatedAt=Date.now();queueEvent(tr.a,{type:'trade-updated',tradeId:id});queueEvent(tr.b,{type:'trade-updated',tradeId:id});return send(res,200,{ok:true,trade:publicTrade(tr,db)})}
    if(tr.status!=='locked')return send(res,409,{error:'TRADE_INVALID'});tr.finalConfirmed[pid]=true;if(!(tr.finalConfirmed[tr.a]&&tr.finalConfirmed[tr.b])){tr.updatedAt=Date.now();return send(res,200,{ok:true,trade:publicTrade(tr,db)})}
    const aa=accountByPlayerId(db,tr.a),bb=accountByPlayerId(db,tr.b);if(!aa?.playerSave||!bb?.playerSave)return send(res,409,{error:'SAVE_REQUIRED'});
    const a0={...(aa.playerSave.inventory||{})},b0={...(bb.playerSave.inventory||{})},ao=tr.offers[tr.a]||{},bo=tr.offers[tr.b]||{};
    const enough=(inv,offer)=>Object.entries(offer).every(([item,n])=>item!=='spliceBook'&&Number(inv[item]||0)>=Number(n||0));
    if(!enough(a0,ao)||!enough(b0,bo))return send(res,409,{error:'TRADE_INVENTORY_CHANGED'});
    const ai={...a0},bi={...b0};
    for(const [item,n0] of Object.entries(ao)){const n=Number(n0||0);ai[item]=Number(ai[item]||0)-n;bi[item]=Number(bi[item]||0)+n}
    for(const [item,n0] of Object.entries(bo)){const n=Number(n0||0);bi[item]=Number(bi[item]||0)-n;ai[item]=Number(ai[item]||0)+n}
    if(Object.values(ai).some(v=>Number(v)<0||Number(v)>200)||Object.values(bi).some(v=>Number(v)<0||Number(v)>200))return send(res,409,{error:'TRADE_INVENTORY_CHANGED'});
    aa.playerSave.inventory=ai;bb.playerSave.inventory=bi;aa.playerSave.savedAt=bb.playerSave.savedAt=Date.now();saveDb(db);tr.status='done';tr.updatedAt=Date.now();tradeByPlayer.delete(tr.a);tradeByPlayer.delete(tr.b);queueEvent(tr.a,{type:'trade-complete',tradeId:id,playerSave:aa.playerSave});queueEvent(tr.b,{type:'trade-complete',tradeId:id,playerSave:bb.playerSave});return send(res,200,{ok:true,trade:publicTrade(tr,db),playerSave:pid===tr.a?aa.playerSave:bb.playerSave})
  }
  if(req.url==='/api/trade/cancel'){cancelTradeFor(session.player.playerId,'CANCELLED');return send(res,200,{ok:true})}
  if(req.url==='/api/session'){
    const account=session.player.accountType==='account'?db.accounts[session.player.accountId]:null;return send(res,200,{token:t,player:playerPayload(session.player),playerSave:account?.playerSave||null,storage:storageMode})
  }
  if(req.url==='/api/player/save'){
    if(session.player.accountType!=='account')return send(res,403,{error:'ACCOUNT_REQUIRED'});const account=db.accounts[session.player.accountId];if(!account)return send(res,404,{error:'ACCOUNT_NOT_FOUND'});const save=sanitizePlayerSave(body.save);if(!save)return send(res,400,{error:'BAD_SAVE'});account.playerSave=save;db.accounts[session.player.accountId]=account;saveDb(db);return send(res,200,{ok:true,savedAt:save.savedAt})
  }
  if(req.url==='/api/player/load'){
    if(session.player.accountType!=='account')return send(res,403,{error:'ACCOUNT_REQUIRED'});const account=db.accounts[session.player.accountId];return send(res,200,{ok:true,playerSave:account?.playerSave||null})
  }
  if(req.url==='/api/logout'){
    cancelTradeFor(session.player.playerId,'DISCONNECTED');removePresence(session.player.playerId);sessions.delete(t);if(session.player.accountType==='account'&&activeAccountTokens.get(session.player.accountId)===t)activeAccountTokens.delete(session.player.accountId);return send(res,200,{ok:true})
  }
  if(req.url==='/api/world/join'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=getOrCreateWorldState(world,body.worldSnapshot);if(Array.isArray(state.snapshot.worldBans)&&state.snapshot.worldBans.includes(session.player.playerId))return send(res,403,{error:'WORLD_BANNED'});for(const [w,room] of worldPresence){if(w!==world){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(w)}}const cap=canJoinWorld(world,session.player.playerId);if(!cap.ok)return send(res,409,{error:cap.error,maxWorld:MAX_WORLD_PLAYERS,maxServer:MAX_SERVER_PLAYERS});updatePresence(world,session.player,body);return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),events:consumeEvents(session.player.playerId),revision:state.revision,worldSnapshot:state.snapshot,chat:(state.chat||[]).slice(-30),storage:storageMode})
  }
  if(req.url==='/api/world/state'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=getOrCreateWorldState(world,body.worldSnapshot);if(Array.isArray(state.snapshot.worldBans)&&state.snapshot.worldBans.includes(session.player.playerId))return send(res,403,{error:'WORLD_BANNED'});const cap=canJoinWorld(world,session.player.playerId);if(!cap.ok)return send(res,409,{error:cap.error,maxWorld:MAX_WORLD_PLAYERS,maxServer:MAX_SERVER_PLAYERS});updatePresence(world,session.player,body);const known=Math.max(0,Number(body.knownRevision||0));return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),events:consumeEvents(session.player.playerId),revision:state.revision,...(known<state.revision?{worldSnapshot:state.snapshot}:{}),chat:(state.chat||[]).slice(-30),serverTime:Date.now()})
  }
  if(req.url==='/api/world/action'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});const state=getOrCreateWorldState(world,null),result=applyWorldAction(state,body.action,session,world);if(result.accepted&&(result.knockback!==true&&result.blocked!==true))persistWorld(world,state);return send(res,result.accepted?200:409,{ok:result.accepted,world,revision:state.revision,actionId:String(body.actionId||'').slice(0,80),...(result.accepted?result:{error:'ACTION_REJECTED'})})
  }
  if(req.url==='/api/world/chat'){
    const world=cleanWorld(body.world),raw=String(body.text||'').trim().replace(/\s+/g,' ');if(raw.length>120)return send(res,400,{error:'CHAT_TOO_LONG'});const text=raw.slice(0,120);if(!world||!text)return send(res,400,{error:'BAD_REQUEST'});const state=getOrCreateWorldState(world,null);const msg={id:randomId('C'),playerId:session.player.playerId,name:session.player.displayName,text,at:Date.now()};state.chat=(state.chat||[]).concat(msg).slice(-30);persistWorld(world,state);return send(res,200,{ok:true,chat:state.chat})
  }
  if(req.url==='/api/world/leave'){
    const world=cleanWorld(body.world),room=worldPresence.get(world);if(room){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}return send(res,200,{ok:true})
  }
  return send(res,404,{error:'NOT_FOUND'})
}

function staticFile(req,res){
  let url=req.url.split('?')[0];if(url==='/')url='/index.html';const file=path.normalize(path.join(ROOT,url));if(!file.startsWith(ROOT))return send(res,403,{error:'FORBIDDEN'});
  fs.readFile(file,(err,data)=>{if(err){res.writeHead(200,{'Content-Type':'text/plain; charset=utf-8'});return res.end(`Pixora Server Build 14.7.0 is live | storage=${storageMode}`)}const ext=path.extname(file),type=ext==='.html'?'text/html; charset=utf-8':ext==='.js'?'application/javascript':'application/octet-stream';res.writeHead(200,{'Content-Type':type});res.end(data)})
}
const server=http.createServer((req,res)=>{if(req.url.startsWith('/api/'))return api(req,res);return staticFile(req,res)});

async function shutdown(){try{await persistQueue}catch(_){}try{await pgPool?.end()}catch(_){}process.exit(0)}
process.on('SIGTERM',shutdown);process.on('SIGINT',shutdown);
initStorage().then(()=>server.listen(PORT,()=>console.log(`Pixora Build 14.7.0 server running on port ${PORT}`))).catch(e=>{console.error(e);process.exit(1)});
