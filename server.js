'use strict';
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const PORT = Number(process.env.PORT || 3000);
const DATA_FILE = process.env.PIXORA_DATA_FILE || path.join(__dirname, 'pixora-data.json');
const ALLOWED_ORIGIN = process.env.ALLOWED_ORIGIN || '*';

function loadDb(){
  try { return JSON.parse(fs.readFileSync(DATA_FILE,'utf8')); }
  catch { return {accounts:{}}; }
}
function saveDb(db){
  const tmp = DATA_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(db,null,2));
  fs.renameSync(tmp, DATA_FILE);
}
const db = loadDb();
const sessions = new Map();

function json(res,status,obj){
  res.writeHead(status,{
    'Content-Type':'application/json; charset=utf-8',
    'Access-Control-Allow-Origin':ALLOWED_ORIGIN,
    'Access-Control-Allow-Headers':'Content-Type, Authorization',
    'Access-Control-Allow-Methods':'POST, OPTIONS',
    'Cache-Control':'no-store'
  });
  res.end(JSON.stringify(obj));
}
function safeDisplayName(v){
  const s=String(v||'Player').trim().replace(/[^A-Za-z0-9_\- ]/g,'').slice(0,12);
  return s || 'Player';
}
function makeTag(name){
  const n=crypto.randomInt(0,10000).toString().padStart(4,'0');
  return `${safeDisplayName(name)}_#${n}`;
}
function token(){ return crypto.randomBytes(32).toString('hex'); }
function hashPassword(password,salt=crypto.randomBytes(16).toString('hex')){
  const hash=crypto.scryptSync(password,salt,64).toString('hex');
  return {salt,hash};
}
function verifyPassword(password,record){
  const a=Buffer.from(hashPassword(password,record.salt).hash,'hex');
  const b=Buffer.from(record.hash,'hex');
  return a.length===b.length && crypto.timingSafeEqual(a,b);
}
function playerView(p){
  return {playerId:p.playerId,accountId:p.accountId||null,displayName:p.displayName,guest:!!p.guest,role:p.role||'player'};
}
function bearer(req){
  const h=String(req.headers.authorization||'');
  return h.startsWith('Bearer ')?h.slice(7):'';
}
function body(req){
  return new Promise((resolve,reject)=>{
    let raw='';
    req.on('data',c=>{raw+=c;if(raw.length>1e6){reject(new Error('too_large'));req.destroy();}});
    req.on('end',()=>{try{resolve(raw?JSON.parse(raw):{})}catch{reject(new Error('bad_json'))}});
    req.on('error',reject);
  });
}
function openSession(player){
  const t=token();
  sessions.set(t,{...player,createdAt:Date.now()});
  return t;
}

const server=http.createServer(async(req,res)=>{
  if(req.method==='OPTIONS') return json(res,204,{});
  if(req.method!=='POST') return json(res,404,{error:'NOT_FOUND'});
  try{
    const data=await body(req);
    if(req.url==='/api/guest'){
      const p={playerId:'guest_'+crypto.randomUUID(),displayName:makeTag(data.name),guest:true,role:'player'};
      const t=openSession(p); return json(res,200,{token:t,player:playerView(p)});
    }
    if(req.url==='/api/register'){
      const id=String(data.id||'').trim().toLowerCase();
      const password=String(data.password||'');
      if(!/^[a-z0-9_.-]{3,24}$/.test(id)||password.length<6) return json(res,400,{error:'BAD_REQUEST'});
      if(db.accounts[id]) return json(res,409,{error:'ACCOUNT_EXISTS'});
      const hp=hashPassword(password);
      const p={playerId:'acct_'+crypto.randomUUID(),accountId:id,displayName:makeTag(data.name),guest:false,role:'player'};
      db.accounts[id]={...p,password:hp,createdAt:Date.now()}; saveDb(db);
      const t=openSession(p); return json(res,200,{token:t,player:playerView(p)});
    }
    if(req.url==='/api/login'){
      const id=String(data.id||'').trim().toLowerCase();
      const a=db.accounts[id];
      if(!a||!verifyPassword(String(data.password||''),a.password)) return json(res,401,{error:'INVALID_CREDENTIALS'});
      const t=openSession(a); return json(res,200,{token:t,player:playerView(a)});
    }
    if(req.url==='/api/session'){
      const t=bearer(req),p=sessions.get(t);
      if(!p) return json(res,401,{error:'INVALID_SESSION'});
      return json(res,200,{token:t,player:playerView(p)});
    }
    if(req.url==='/api/logout'){
      sessions.delete(bearer(req)); return json(res,200,{ok:true});
    }
    return json(res,404,{error:'NOT_FOUND'});
  }catch(e){ return json(res,400,{error:'BAD_REQUEST'}); }
});
server.listen(PORT,()=>console.log(`Pixora auth server running on :${PORT}`));
