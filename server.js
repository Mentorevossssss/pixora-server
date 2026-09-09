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
function cleanWorld(v){return String(v||'').trim().toUpperCase().replace(/[^A-Z0-9_-]/g,'').slice(0,18)}
function pruneRoom(world){const room=worldPresence.get(world);if(!room)return;const cutoff=Date.now()-15000;for(const [id,st] of room){if(st.lastSeen<cutoff)room.delete(id)}if(!room.size)worldPresence.delete(world)}
function updatePresence(world,p,b){if(!worldPresence.has(world))worldPresence.set(world,new Map());const room=worldPresence.get(world),prev=room.get(p.playerId)||{};room.set(p.playerId,{playerId:p.playerId,displayName:p.displayName,x:Number.isFinite(Number(b.x))?Number(b.x):(prev.x||120),y:Number.isFinite(Number(b.y))?Number(b.y):(prev.y||0),facing:Number(b.facing)<0?-1:1,onGround:!!b.onGround,vx:Number.isFinite(Number(b.vx))?Number(b.vx):0,vy:Number.isFinite(Number(b.vy))?Number(b.vy):0,lastSeen:Date.now()})}
function roomView(world,selfId){pruneRoom(world);const room=worldPresence.get(world);return room?[...room.values()].filter(p=>p.playerId!==selfId).map(({lastSeen,...p})=>p):[]}

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
function readJson(req){return new Promise((resolve,reject)=>{let body='';req.on('data',c=>{body+=c;if(body.length>20000)req.destroy()});req.on('end',()=>{try{resolve(body?JSON.parse(body):{})}catch(e){reject(e)}});req.on('error',reject)})}
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
    const pass=hashPassword(pw);const account={id,playerId:'A-'+crypto.randomUUID(),displayName:`${base}_#${suffix()}`,pass,createdAt:Date.now()};db.accounts[id]=account;saveDb(db);
    const player={playerId:account.playerId,displayName:account.displayName,accountId:id,accountType:'account'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/login'){
    const id=cleanId(body.id),pw=String(body.password||''),account=db.accounts[id];
    if(!account||!verifyPassword(pw,account.pass))return send(res,401,{error:'INVALID_CREDENTIALS'});
    const player={playerId:account.playerId,displayName:account.displayName,accountId:id,accountType:'account'};const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player)});
  }
  if(req.url==='/api/session'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});return send(res,200,{token:t,player:playerPayload(session.player)});
  }
  if(req.url==='/api/logout'){
    const t=authToken(req),session=sessions.get(t);if(session){for(const [world,room] of worldPresence){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}}if(t)sessions.delete(t);return send(res,200,{ok:true});
  }
  if(req.url==='/api/world/join'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});for(const [w,room] of worldPresence){if(w!==world){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(w)}}updatePresence(world,session.player,body);return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId)});
  }
  if(req.url==='/api/world/state'){
    const t=authToken(req),session=sessions.get(t);if(!session)return send(res,401,{error:'INVALID_SESSION'});const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});updatePresence(world,session.player,body);return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId),serverTime:Date.now()});
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
server.listen(PORT,()=>console.log(`Pixora Build 14 auth server running on http://localhost:${PORT}`));
