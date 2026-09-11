'use strict';

const http=require('http');
const fs=require('fs');
const path=require('path');
const crypto=require('crypto');
let PgPool=null;
try{PgPool=require('pg').Pool}catch(_){ }

const PORT=Number(process.env.PORT||3000);
const ROOT=path.join(__dirname,'public');
const DATA_DIR=String(process.env.PIXORA_DATA_DIR||path.join(__dirname,'data'));
const FILE_DB=String(process.env.PIXORA_DATA_FILE||path.join(DATA_DIR,'accounts.json'));
const LEGACY_FILE_DB=path.join(__dirname,'accounts.json');
const DATABASE_URL=String(process.env.DATABASE_URL||'').trim();
const sessions=new Map();
const revokedTokens=new Map();
const activeAccountTokens=new Map();
const worldPresence=new Map();
const worldStates=new Map();
const knockbackEvents=new Map();
const trades=new Map();
const tradeByPlayer=new Map();
const chatCooldowns=new Map();
const emoteCooldowns=new Map();
const recentReplies=new Map();
const IOTM_TESTING=true;
const MAX_SERVER_PLAYERS=100;
const MAX_WORLD_PLAYERS=20;
const PIXORA_KINGDOM_TEMPLATE_VERSION=1;
const HELL_WORLD='HELL';
const ROLE_RANK={Player:0,Moderator:1,Admin:2,Owner:3};

let dbCache={accounts:{},worlds:{}};
let pgPool=null;
let storageMode='file';
let persistQueue=Promise.resolve();
let restartPlan={active:false,restartAt:0,startedAt:0,minutes:0,by:'',lastMarker:null};
let restartTicker=null;

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
function normalizeDb(d){if(!d||typeof d!=='object')d={};if(!d.accounts||typeof d.accounts!=='object')d.accounts={};if(!d.guests||typeof d.guests!=='object')d.guests={};if(!d.sessions||typeof d.sessions!=='object')d.sessions={};if(!d.worlds||typeof d.worlds!=='object')d.worlds={};if(!Array.isArray(d.reports))d.reports=[];if(!Array.isArray(d.auditLog))d.auditLog=[];if(!d.serverBans||typeof d.serverBans!=='object')d.serverBans={};if(!d.hellJail||typeof d.hellJail!=='object')d.hellJail={};if(!d.friends||typeof d.friends!=='object')d.friends={};if(!Array.isArray(d.friendRequests))d.friendRequests=[];if(!d.mutes||typeof d.mutes!=='object')d.mutes={};if(!d.freezes||typeof d.freezes!=='object')d.freezes={};if(!d.playerNotes||typeof d.playerNotes!=='object')d.playerNotes={};if(!Array.isArray(d.tradeHistory))d.tradeHistory=[];if(!d.worldLogs||typeof d.worldLogs!=='object')d.worldLogs={};if(!d.bannedWorlds||typeof d.bannedWorlds!=='object')d.bannedWorlds={};if(!d.worldSlowmode||typeof d.worldSlowmode!=='object')d.worldSlowmode={};if(!d.gemEvent||typeof d.gemEvent!=='object')d.gemEvent={multiplier:1,until:0};if(!d.worldRecoveryBackups||typeof d.worldRecoveryBackups!=='object')d.worldRecoveryBackups={};if(!d.ownerGrantedItems||typeof d.ownerGrantedItems!=='object')d.ownerGrantedItems={};return d}
const BUILTIN_OWNER_ACCOUNT={id:'williamx',username:'Pixora',playerId:'A-1fb8e9b4-6bd5-45fd-8f0a-d09355a4658e',displayName:'Pixora',email:'',role:'Owner',pass:{salt:'2b0079e1e5a4fafc7d7d524d1edb63bf',hash:'374b741dd8b46cd1a00cdff94bb3280379f892128869551104dd92f9481a290ae726351fb0acc77b8d6cfddeaf743668a451ebf648edc1415b14f0e7dfbe83af'},playerSave:null,createdAt:1789017712504,builtInOwner:true};
function ensureBuiltInOwner(db){
  db=normalizeDb(db);let changed=false;
  const legacy=db.accounts.pixoraowner;
  if(legacy&&legacy.builtInOwner===true){delete db.accounts.pixoraowner;changed=true}
  const existing=db.accounts[BUILTIN_OWNER_ACCOUNT.id];
  if(existing){
    if(existing.role!=='Owner'){existing.role='Owner';changed=true}
    if(existing.username!=='Pixora'){existing.username='Pixora';changed=true}
    if(existing.displayName!=='Pixora'){existing.displayName='Pixora';changed=true}
    if(existing.builtInOwner!==true){existing.builtInOwner=true;changed=true}
    return changed
  }
  db.accounts[BUILTIN_OWNER_ACCOUNT.id]=JSON.parse(JSON.stringify(BUILTIN_OWNER_ACCOUNT));return true
}
function readFileDb(){for(const file of [FILE_DB,LEGACY_FILE_DB]){try{if(fs.existsSync(file))return normalizeDb(JSON.parse(fs.readFileSync(file,'utf8')))}catch(_){ }}return {accounts:{},worlds:{}}}
function writeFileBackup(db){try{fs.mkdirSync(path.dirname(FILE_DB),{recursive:true});const tmp=FILE_DB+'.tmp';fs.writeFileSync(tmp,JSON.stringify(db,null,2));fs.renameSync(tmp,FILE_DB)}catch(e){console.warn('file backup failed:',e.message)}}
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
function roleRank(role){return ROLE_RANK[String(role||'Player')]??0}
function hasRole(role,minRole){return roleRank(role)>=roleRank(minRole)}
function canStaffTarget(actor,target){return !!actor&&!!target&&actor.playerId!==target.playerId&&roleRank(target.role)<roleRank(actor.role)}
function addAudit(db,actor,action,target='',details={}){db.auditLog.push({id:randomId('AUD'),at:Date.now(),actorId:actor?.playerId||'',actorName:actor?.displayName||'',actorRole:actor?.role||'Player',action:String(action||'').slice(0,40),target:String(target||'').slice(0,100),details});db.auditLog=db.auditLog.slice(-2000)}
function resolveWorldTarget(world,query){pruneRoom(world);const room=worldPresence.get(world);if(!room)return {error:'PLAYER_NOT_FOUND'};const q=String(query||'').trim().toLowerCase();if(!q)return {error:'PLAYER_NOT_FOUND'};let exact=[...room.values()].filter(p=>String(p.playerId).toLowerCase()===q||String(p.displayName).toLowerCase()===q);if(exact.length===1)return {player:exact[0]};let partial=[...room.values()].filter(p=>String(p.displayName).toLowerCase().startsWith(q));if(partial.length===1)return {player:partial[0]};return {error:partial.length>1?'PLAYER_AMBIGUOUS':'PLAYER_NOT_FOUND'}}
function guestByPlayerId(db,playerId){return (db.guests&&db.guests[playerId])||null}
function resolveAnyKnownPlayer(db,query){const q=String(query||'').trim().toLowerCase();if(!q)return null;for(const a of Object.values(db.accounts||{})){if(String(a.playerId||'').toLowerCase()===q||String(a.id||'').toLowerCase()===q||String(a.username||'').toLowerCase()===q)return {playerId:a.playerId,displayName:a.username||a.displayName||a.id,role:roleForAccount(a),account:a,accountType:'account'}}for(const g of Object.values(db.guests||{})){if(String(g.playerId||'').toLowerCase()===q||String(g.displayName||'').toLowerCase()===q)return {playerId:g.playerId,displayName:g.displayName||g.playerId,role:'Player',guest:g,accountType:'guest'}}return null}
function isWorldOwnershipLockType(type){return type==='worldLock'||type==='ownerLock'}
function worldLockFor(world){const state=worldStates.get(world)||loadWorldFromDb(world);return state?.snapshot?.locks?.find(l=>isWorldOwnershipLockType(l?.type))||null}
function currentWorldOwner(world,playerId){const wl=worldLockFor(world);return !!wl&&String(wl.owner||'')===String(playerId||'')}
function worldMembership(world,playerId){const wl=worldLockFor(world);if(!wl)return 'player';if(String(wl.owner||'')===String(playerId||''))return 'owner';if(Array.isArray(wl.trusted)&&wl.trusted.includes(String(playerId||'')))return 'admin';return 'player'}
function publicHelp(worldOwner=false){const out=['/help','/who','/warp <world>','/mods','/rules','/worldinfo','/msg <player> <message>','/r <message>','/sb <message>','/dance','/wave','/sleep','/laugh','/cry','/angry','/happy','/love','/shrug','/cheer','/facepalm','/point','/me <action>','/emote'];if(worldOwner)out.push('/pull <player>','/kick <player>','Wrench: grant/remove World Admin access');return out}
function staffHelp(role){const out=[];if(hasRole(role,'Moderator'))out.push('/staffhelp','/warn <player> [reason]','/mute <player> [minutes] [reason]','/unmute <player>','/freeze <player>','/unfreeze <player>','/goto <player>','/reports','/staffchat <message>','/history <player>','/tradehistory <player>','/worldlog [world]','/note <player> <note>','/hidden [on|off]');if(hasRole(role,'Admin'))out.push('/ban <player> [reason]','/unban <id/player>','/tempban <player> <minutes> [reason]','/baninfo <player/id>','/forcewarp <player> <world>','/announce <message>','/slowmode <seconds>','/eventxgems <x> [minutes]|off','/banworld <world> [reason]','/unbanworld <world>');if(role==='Owner')out.push('/give <item> [amount] [player]','/role <player> <player|moderator|admin>','/hell <player> [reason]','/unhell <id/player>','/vanish','/unvanish','/staff [on|off]','/ownerbreak <on|off>','/audit [count]','/resetserver <minutes>|cancel');return out}
function commandError(message='Unknown command.'){return {ok:false,message}}
function isServerBanned(db,playerId){const b=db.serverBans?.[playerId];if(!b)return null;if(Number(b.until||0)>0&&Date.now()>=Number(b.until)){delete db.serverBans[playerId];saveDb(db);return null}return b}
function isMuted(db,playerId){const m=db.mutes?.[playerId];if(!m)return null;if(Number(m.until||0)>0&&Date.now()>=Number(m.until)){delete db.mutes[playerId];saveDb(db);return null}return m}
function onlinePlayerByQuery(query){const q=String(query||'').trim().toLowerCase();if(!q)return null;const rows=[];for(const [world,room] of worldPresence){pruneRoom(world);for(const p of room?.values()||[]){if(String(p.playerId).toLowerCase()===q||String(p.displayName).toLowerCase()===q)rows.push({...p,world});}}if(rows.length===1)return rows[0];const partial=[];for(const [world,room] of worldPresence){for(const p of room?.values()||[]){if(String(p.displayName).toLowerCase().startsWith(q))partial.push({...p,world});}}return partial.length===1?partial[0]:null}
function appendSystemChat(world,text,name='SYSTEM'){world=cleanWorld(world);if(!world)return;const state=getOrCreateWorldState(world,null);const msg={id:randomId('SYS'),playerId:'',name,text:String(text||'').slice(0,700),at:Date.now(),system:true};state.chat=(state.chat||[]).concat(msg).slice(-30);persistWorld(world,state);return msg}
function broadcastSystem(db,text,name='SYSTEM'){const worlds=new Set([...Object.keys(db.worlds||{}),...worldStates.keys()]);for(const w of worlds)appendSystemChat(w,text,name)}
function appendSuperBroadcast(sender,world,text){
  const at=Date.now(),name=`${String(sender?.displayName||'PLAYER').slice(0,24)} (${cleanWorld(world)})`,msg={id:randomId('SB'),playerId:'',name,text:`\"${String(text||'').slice(0,120)}\"`,at,system:true,superBroadcast:true};
  const activeWorlds=new Set([...worldPresence.keys()].map(cleanWorld).filter(Boolean));activeWorlds.add(cleanWorld(world));
  for(const w of activeWorlds){const state=getOrCreateWorldState(w,null);state.chat=(state.chat||[]).concat({...msg}).slice(-30);persistWorld(w,state)}
  return msg
}
function addWorldLog(db,world,actor,action,target='',details={}){world=cleanWorld(world);if(!world)return;const rows=Array.isArray(db.worldLogs[world])?db.worldLogs[world]:[];rows.push({id:randomId('WLOG'),at:Date.now(),actorId:actor?.playerId||'',actorName:actor?.displayName||'',actorRole:actor?.role||'Player',action:String(action||'').slice(0,40),target:String(target||'').slice(0,100),details});db.worldLogs[world]=rows.slice(-500)}
function addModerationAction(db,actor,action,target,details={}){addAudit(db,actor,action,target,details)}
function hiddenActorLabel(actor){return actor?.hidden?'Staff':(actor?.displayName||'Staff')}
function targetForStaff(db,query){return onlinePlayerByQuery(query)||resolveAnyKnownPlayer(db,query)}
function targetRoleOf(t){return String(t?.role||'Player')}
function targetAllowed(actor,t){if(!t||!actor)return false;if(String(t.playerId)===String(actor.playerId))return false;return roleRank(targetRoleOf(t))<roleRank(actor.role)}
function roomBroadcastEvent(world,ev,except=''){pruneRoom(world);const room=worldPresence.get(world);if(!room)return;for(const p of room.values())if(p.playerId!==except)queueEvent(p.playerId,ev)}
function allStaffOnline(){const seen=new Map();for(const [world,room] of worldPresence){pruneRoom(world);for(const p of room?.values()||[])if(hasRole(p.role,'Moderator')&&!p.hidden&&!p.vanished)seen.set(p.playerId,{...p,world})}return [...seen.values()]}
function friendSet(db,id){if(!Array.isArray(db.friends[id]))db.friends[id]=[];return new Set(db.friends[id])}
function areFriends(db,a,b){return friendSet(db,a).has(b)&&friendSet(db,b).has(a)}
function syncFriendSave(db,id){const save=getPlayerSave(db,id);if(save){save.friends=[...friendSet(db,id)];setPlayerSave(db,id,save)}}
function moderationAnnounce(db,actor,text){broadcastSystem(db,text+(actor?.hidden?'':' • by '+(actor?.displayName||'Staff')),'MODERATION')}
function publicRestartPlan(){return restartPlan.active?{active:true,restartAt:restartPlan.restartAt,startedAt:restartPlan.startedAt,minutes:restartPlan.minutes}:{active:false}}
function restartAnnouncementFor(seconds){
  if(seconds>60&&seconds%60===0)return `Server restart in ${Math.floor(seconds/60)} minute${seconds===60?'':'s'}.`;
  if(seconds===60)return 'Server restart in 1 minute. Pixora restart theme started.';
  if([50,40,30,20,10].includes(seconds))return `Server restart in ${seconds} seconds.`;
  if(seconds>=1&&seconds<=9)return `Server restart in ${seconds}...`;
  return '';
}
function markerForRestart(seconds){if(seconds>60){const mins=Math.ceil(seconds/60);return mins*60}if(seconds===60)return 60;if([50,40,30,20,10].includes(seconds))return seconds;if(seconds>=1&&seconds<=9)return seconds;return null}
function flushAllWorldStates(){for(const [world,state] of worldStates)persistWorld(world,state);saveDb(loadDb())}
function cancelServerRestart(db,actor){
  if(!restartPlan.active)return false;restartPlan={active:false,restartAt:0,startedAt:0,minutes:0,by:'',lastMarker:null};if(restartTicker){clearInterval(restartTicker);restartTicker=null}
  broadcastSystem(db,'Scheduled server restart was cancelled.','SYSTEM');if(actor)addAudit(db,actor,'cancel-reset-server','',{});saveDb(db);return true
}
function scheduleServerRestart(db,actor,minutes){
  minutes=Math.max(1,Math.min(1440,Math.floor(Number(minutes||0))));if(restartPlan.active)return {ok:false,error:'RESTART_ALREADY_SCHEDULED'};
  const now=Date.now();restartPlan={active:true,restartAt:now+minutes*60000,startedAt:now,minutes,by:actor?.playerId||'',lastMarker:null};
  addAudit(db,actor,'reset-server','',{minutes});broadcastSystem(db,`Server restart scheduled in ${minutes} minute${minutes===1?'':'s'}.`,'SYSTEM');saveDb(db);
  restartTicker=setInterval(async()=>{
    if(!restartPlan.active)return;const seconds=Math.max(0,Math.ceil((restartPlan.restartAt-Date.now())/1000));
    if(seconds<=0){if(restartTicker){clearInterval(restartTicker);restartTicker=null}restartPlan.active=false;broadcastSystem(loadDb(),'Server restarting now. Saving all worlds and sessions…','SYSTEM');flushAllWorldStates();try{await persistQueue}catch(_){}setTimeout(()=>shutdown(),250);return}
    const marker=markerForRestart(seconds);if(marker!==null&&marker!==restartPlan.lastMarker){restartPlan.lastMarker=marker;const msg=restartAnnouncementFor(marker);if(msg)broadcastSystem(loadDb(),msg,'SYSTEM')}
  },250);
  return {ok:true,plan:publicRestartPlan()}
}
const EMOTES={dance:{text:'~ dance ~',duration:5000},wave:{text:'o/',duration:3000},sleep:{text:'-_- zZ',duration:6000},laugh:{text:'XD',duration:3000},cry:{text:'T_T',duration:3000},angry:{text:'>:(',duration:3000},happy:{text:'^_^',duration:3000},love:{text:'<3',duration:3000},shrug:{text:'¯\\_(ツ)_/¯',duration:3500},cheer:{text:'\\o/',duration:3000},facepalm:{text:'-_-;',duration:3000},point:{text:'->',duration:3000}};
function runChatCommand({raw,world,session,db}){
  const parts=String(raw||'').trim().slice(1).split(/\s+/),cmd=String(parts.shift()||'').toLowerCase(),role=session.player.role||'Player',pid=session.player.playerId;
  pruneRoom(world);const room=worldPresence.get(world),worldOwner=currentWorldOwner(world,pid),ok=(message,extra={})=>({ok:true,message,...extra});
  if(cmd==='help')return ok('Commands: '+publicHelp(worldOwner).join(' • '),{history:true,historyName:'HELP'});
  if(cmd==='staffhelp'){if(!hasRole(role,'Moderator'))return commandError();return ok('Staff commands: '+staffHelp(role).join(' • '),{history:true,historyName:'STAFF HELP'});}
  if(cmd==='who'){const visible=room?[...room.values()].filter(p=>!p.vanished&&(!p.hidden||hasRole(role,'Moderator'))):[];return ok('Online di '+world+': '+(visible.map(p=>p.displayName).join(', ')||'hanya kamu'),{history:true,historyName:'WHO'});}
  if(cmd==='warp'){const dest=cleanWorld(parts[0]);if(!dest)return commandError('Pakai: /warp <world>');if(db.hellJail[pid]&&dest!==HELL_WORLD)return commandError('Kamu sedang dikunci di HELL.');return ok('Warp ke '+dest,{teleportWorld:dest})}
  if(cmd==='mods'){const staff=allStaffOnline();return ok(staff.length?'Staff online: '+staff.map(p=>`${p.displayName} [${p.role}]`).join(' • '):'No staff currently online.',{history:true,historyName:'MODS'});}
  if(cmd==='rules')return ok('PIXORA RULES • No scam • Casino/gambling dilarang • Jangan exploit/dupe • Jangan impersonate staff • Hormati player lain.',{history:true,historyName:'RULES'});
  if(cmd==='worldinfo'){const wl=worldLockFor(world),owner=wl?knownPlayerLabel(db,wl.owner):'None',admins=wl&&Array.isArray(wl.trusted)?wl.trusted.map(id=>knownPlayerLabel(db,id)).filter(Boolean):[],slow=Math.max(0,Number(db.worldSlowmode?.[world]||0)),banned=!!db.bannedWorlds?.[world],lockLabel=wl?(wl.type==='ownerLock'?'OWNER LOCK':'WORLD LOCK'):'UNLOCKED';return ok(`WORLD ${world} • ${lockLabel} • Owner: ${owner} • World Admin: ${admins.join(', ')||'None'} • Players: ${room?.size||0}/${MAX_WORLD_PLAYERS} • Slowmode: ${slow}s • World Ban: ${banned?'YES':'NO'}`,{history:true,historyName:'WORLD INFO'});}
  if(cmd==='msg'||cmd==='r'){
    let target,text;if(cmd==='r'){target=onlinePlayerByQuery(recentReplies.get(pid)||'');text=parts.join(' ')}else{target=onlinePlayerByQuery(parts.shift());text=parts.join(' ')}
    if(!target)return commandError(cmd==='r'?'Belum ada player untuk dibalas.':'Player tidak online.');if(target.playerId===pid)return commandError('Tidak bisa message diri sendiri.');if(!text)return commandError(cmd==='r'?'Pakai: /r <pesan>':'Pakai: /msg <player> <pesan>');
    const mine=getPlayerSave(db,pid)||{},theirs=getPlayerSave(db,target.playerId)||{};if((mine.blocked||[]).includes(target.playerId)||(mine.ignored||[]).includes(target.playerId)||(theirs.blocked||[]).includes(pid)||(theirs.ignored||[]).includes(pid))return commandError('Private message diblokir oleh Block/Ignore.');
    recentReplies.set(pid,target.playerId);recentReplies.set(target.playerId,pid);queueEvent(target.playerId,{type:'private-message',from:pid,name:session.player.displayName,text:text.slice(0,180)});return ok(`To ${target.displayName}: ${text.slice(0,180)}`,{history:true,historyName:'PM'});
  }
  if(cmd==='sb'){
    const save=getPlayerSave(db,pid)||{},level=Math.max(1,Math.floor(Number(save.playerLevel||1))),text=parts.join(' ').trim().replace(/\s+/g,' ').slice(0,120);
    if(level<5)return commandError('Super Broadcast membutuhkan minimal Level 5.');if(!text)return commandError('Pakai: /sb <pesan>');const mute=isMuted(db,pid);if(mute)return commandError('Kamu sedang di-mute.');
    appendSuperBroadcast(session.player,world,text);addAudit(db,session.player,'super-broadcast',world,{text});saveDb(db);return ok('Super Broadcast sent.');
  }
  if(cmd==='me'){const action=parts.join(' ').slice(0,140);if(!action)return commandError('Pakai: /me <aksi>');const now=Date.now(),last=Number(emoteCooldowns.get(pid)||0);if(now-last<1200)return commandError('Tunggu sebentar sebelum emote lagi.');emoteCooldowns.set(pid,now);const m={id:randomId('ACT'),playerId:pid,name:'* '+session.player.displayName,text:action,at:now,action:true};const state=getOrCreateWorldState(world,null);state.chat=(state.chat||[]).concat(m).slice(-30);persistWorld(world,state);roomBroadcastEvent(world,{type:'emote',playerId:pid,kind:'me',text:action,duration:3000},pid);return ok(session.player.displayName+' '+action,{emote:{kind:'me',text:action,duration:3000}})}
  if(EMOTES[cmd]){const now=Date.now(),last=Number(emoteCooldowns.get(pid)||0);if(now-last<1200)return commandError('Tunggu sebentar sebelum emote lagi.');emoteCooldowns.set(pid,now);const em={kind:cmd,...EMOTES[cmd]};roomBroadcastEvent(world,{type:'emote',playerId:pid,...em},pid);return ok(cmd.toUpperCase(),{emote:em});}
  if(cmd==='emote')return ok('Emote panel',{openEmote:true});
  if(cmd==='pull'||cmd==='kick'){
    const staffAllowed=hasRole(role,'Moderator');if(!worldOwner&&!staffAllowed)return commandError();const r=resolveWorldTarget(world,parts[0]);if(!r.player)return commandError(r.error==='PLAYER_AMBIGUOUS'?'Nama player ambigu.':'Player tidak ditemukan.');if(staffAllowed&&!worldOwner&&!canStaffTarget(session.player,r.player))return commandError('Tidak bisa menarget role yang sama/lebih tinggi.');if(worldOwner&&roleRank(r.player.role)>roleRank(role))return commandError('World Owner tidak bisa menarget staff dengan role lebih tinggi.');
    if(cmd==='pull'){const src=room?.get(pid);queueEvent(r.player.playerId,{type:'pull',world,x:Number(src?.x||0),y:Number(src?.y||0)-44,from:pid,staff:staffAllowed});addAudit(db,session.player,'pull',r.player.playerId,{world});addWorldLog(db,world,session.player,'pull',r.player.playerId,{});saveDb(db);return ok('Pulled '+r.player.displayName)}
    queueEvent(r.player.playerId,{type:'world-kick',world,reason:staffAllowed?'STAFF_KICK':'OWNER_KICK',from:pid});addAudit(db,session.player,'kick',r.player.playerId,{world});addWorldLog(db,world,session.player,'kick',r.player.playerId,{});saveDb(db);return ok('Kicked '+r.player.displayName)
  }
  if(['warn','mute','unmute','freeze','unfreeze'].includes(cmd)){
    if(!hasRole(role,'Moderator'))return commandError();const t=targetForStaff(db,parts.shift());if(!t)return commandError('Player tidak ditemukan.');if(!targetAllowed(session.player,t))return commandError('Tidak bisa menarget role yang sama/lebih tinggi.');
    if(cmd==='warn'){const reason=parts.join(' ').slice(0,160)||'Staff warning';addModerationAction(db,session.player,'warn',t.playerId,{reason,world});queueEvent(t.playerId,{type:'moderation-notice',action:'WARN',reason,by:hiddenActorLabel(session.player)});saveDb(db);return ok('Warned '+t.displayName)}
    if(cmd==='mute'){let mins=Math.max(1,Math.min(10080,Math.floor(Number(parts[0])||10)));if(/^\d+$/.test(parts[0]||''))parts.shift();const reason=parts.join(' ').slice(0,160)||'Staff mute';db.mutes[t.playerId]={at:Date.now(),until:Date.now()+mins*60000,by:pid,reason};addModerationAction(db,session.player,'mute',t.playerId,{mins,reason});queueEvent(t.playerId,{type:'moderation-notice',action:'MUTE',reason,duration:mins});saveDb(db);return ok(`Muted ${t.displayName} ${mins}m`)}
    if(cmd==='unmute'){delete db.mutes[t.playerId];addModerationAction(db,session.player,'unmute',t.playerId,{});queueEvent(t.playerId,{type:'moderation-notice',action:'UNMUTE'});saveDb(db);return ok('Unmuted '+t.displayName)}
    if(cmd==='freeze'){db.freezes[t.playerId]={at:Date.now(),by:pid,world};addModerationAction(db,session.player,'freeze',t.playerId,{world});queueEvent(t.playerId,{type:'freeze',enabled:true});saveDb(db);return ok('Frozen '+t.displayName)}
    delete db.freezes[t.playerId];addModerationAction(db,session.player,'unfreeze',t.playerId,{world});queueEvent(t.playerId,{type:'freeze',enabled:false});saveDb(db);return ok('Unfrozen '+t.displayName)
  }
  if(cmd==='goto'){if(!hasRole(role,'Moderator'))return commandError();const t=onlinePlayerByQuery(parts[0]);if(!t)return commandError('Player harus online.');if(!targetAllowed(session.player,t)&&t.playerId!==pid)return commandError('Target role terlalu tinggi.');return ok('Going to '+t.displayName,{teleportWorld:t.world,teleportPosition:{x:t.x,y:t.y}})}
  if(cmd==='reports'){if(!hasRole(role,'Moderator'))return commandError();return ok('Opening reports…',{openReports:true})}
  if(cmd==='staffchat'){if(!hasRole(role,'Moderator'))return commandError();const text=parts.join(' ').slice(0,180);if(!text)return commandError('Pakai: /staffchat <pesan>');for(const p of allStaffOnline())queueEvent(p.playerId,{type:'staff-chat',name:session.player.displayName,role,text});return ok('Staff chat sent')}
  if(cmd==='history'){if(!hasRole(role,'Moderator'))return commandError();const t=resolveAnyKnownPlayer(db,parts[0])||onlinePlayerByQuery(parts[0]);if(!t)return commandError('Player tidak ditemukan.');const rows=(db.auditLog||[]).filter(a=>a.target===t.playerId||a.actorId===t.playerId).slice(-6).reverse().map(a=>`${a.action} ${a.details?.reason?'('+a.details.reason+')':''}`.trim());return ok(`${t.displayName} history: ${rows.join(' • ')||'empty'}`,{history:true,historyName:'MOD HISTORY'})}
  if(cmd==='tradehistory'){if(!hasRole(role,'Moderator'))return commandError();const t=resolveAnyKnownPlayer(db,parts[0])||onlinePlayerByQuery(parts[0]);if(!t)return commandError('Player tidak ditemukan.');const rows=(db.tradeHistory||[]).filter(x=>x.a===t.playerId||x.b===t.playerId).slice(-5).reverse().map(x=>`${new Date(x.at).toISOString().slice(0,16)} ${knownPlayerLabel(db,x.a)} ↔ ${knownPlayerLabel(db,x.b)} [${Object.entries(x.aOffer||{}).map(([i,n])=>i+'x'+n).join(',')||'-'} | ${Object.entries(x.bOffer||{}).map(([i,n])=>i+'x'+n).join(',')||'-'}]`);return ok(`Trade history: ${rows.join(' • ')||'empty'}`,{history:true,historyName:'TRADE HISTORY'})}
  if(cmd==='worldlog'){if(!hasRole(role,'Moderator'))return commandError();const w=cleanWorld(parts[0]||world),rows=(db.worldLogs?.[w]||[]).slice(-8).reverse().map(x=>`${x.actorName||'SYSTEM'} ${x.action}${x.target?' → '+knownPlayerLabel(db,x.target):''}`);return ok(`${w} log: ${rows.join(' • ')||'empty'}`,{history:true,historyName:'WORLD LOG'})}
  if(cmd==='note'){if(!hasRole(role,'Moderator'))return commandError();const targetQuery=parts.shift();const t=resolveAnyKnownPlayer(db,targetQuery)||onlinePlayerByQuery(targetQuery);const note=parts.join(' ').slice(0,240);if(!t||!note)return commandError('Pakai: /note <player> <catatan>');const rows=Array.isArray(db.playerNotes[t.playerId])?db.playerNotes[t.playerId]:[];rows.push({id:randomId('NOTE'),at:Date.now(),by:pid,byName:session.player.displayName,note});db.playerNotes[t.playerId]=rows.slice(-100);addAudit(db,session.player,'note',t.playerId,{note});saveDb(db);return ok('Internal note saved for '+t.displayName)}
  if(cmd==='hidden'){if(!hasRole(role,'Moderator'))return commandError();const arg=String(parts[0]||'').toLowerCase(),on=arg==='on'?true:arg==='off'?false:!session.player.hidden;session.player.hidden=on;const p=room?.get(pid);if(p)p.hidden=on;addAudit(db,session.player,'hidden-mode',pid,{enabled:on});saveDb(db);return ok(on?'Hidden ON':'Hidden OFF',{hidden:on})}
  if(cmd==='ban'){
    if(!hasRole(role,'Admin'))return commandError();const t=targetForStaff(db,parts.shift());if(!t)return commandError('Player tidak ditemukan.');if(!targetAllowed(session.player,t))return commandError('Tidak bisa ban role yang sama/lebih tinggi.');const reason=parts.join(' ').slice(0,160)||'Staff ban';db.serverBans[t.playerId]={at:Date.now(),by:pid,byName:session.player.displayName,targetName:t.displayName,reason,until:0};addAudit(db,session.player,'server-ban',t.playerId,{reason,world});moderationAnnounce(db,session.player,`${t.displayName} was BANNED • ${reason}`);saveDb(db);cancelTradeFor(t.playerId,'BANNED');removePresence(t.playerId);queueEvent(t.playerId,{type:'server-ban',reason});return ok('Server banned '+t.displayName)}
  if(cmd==='tempban'){if(!hasRole(role,'Admin'))return commandError();const t=targetForStaff(db,parts.shift()),mins=Math.max(1,Math.min(43200,Math.floor(Number(parts.shift())||0)));if(!t||!mins)return commandError('Pakai: /tempban <player> <minutes> [reason]');if(!targetAllowed(session.player,t))return commandError('Tidak bisa ban role yang sama/lebih tinggi.');const reason=parts.join(' ').slice(0,160)||'Temporary ban';db.serverBans[t.playerId]={at:Date.now(),until:Date.now()+mins*60000,by:pid,byName:session.player.displayName,targetName:t.displayName,reason};addAudit(db,session.player,'tempban',t.playerId,{mins,reason});moderationAnnounce(db,session.player,`${t.displayName} was TEMP BANNED ${mins}m • ${reason}`);saveDb(db);removePresence(t.playerId);queueEvent(t.playerId,{type:'server-ban',reason});return ok(`Temp banned ${t.displayName} ${mins}m`)}
  if(cmd==='unban'){if(!hasRole(role,'Admin'))return commandError();const known=resolveAnyKnownPlayer(db,parts[0]);let targetId=known?.playerId||String(parts[0]||'');if(!db.serverBans[targetId]){const hit=Object.keys(db.serverBans).find(x=>x.toLowerCase()===targetId.toLowerCase()||String(db.serverBans[x]?.targetName||'').toLowerCase()===String(parts[0]||'').toLowerCase());if(hit)targetId=hit}if(!db.serverBans[targetId])return commandError('Ban tidak ditemukan.');const label=db.serverBans[targetId]?.targetName||known?.displayName||targetId;delete db.serverBans[targetId];addAudit(db,session.player,'server-unban',targetId,{});moderationAnnounce(db,session.player,`${label} was UNBANNED`);saveDb(db);return ok('Unbanned '+label)}
  if(cmd==='baninfo'){if(!hasRole(role,'Admin'))return commandError();const known=resolveAnyKnownPlayer(db,parts[0]);let id=known?.playerId||String(parts[0]||''),b=isServerBanned(db,id);if(!b){const hit=Object.keys(db.serverBans).find(x=>String(db.serverBans[x]?.targetName||'').toLowerCase()===String(parts[0]||'').toLowerCase());if(hit){id=hit;b=isServerBanned(db,id)}}if(!b)return ok('No active ban.');return ok(`BAN ${b.targetName||knownPlayerLabel(db,id)} • reason: ${b.reason||'-'} • ${b.until?'until '+new Date(b.until).toISOString():'permanent'}`,{history:true,historyName:'BAN INFO'})}
  if(cmd==='forcewarp'){if(!hasRole(role,'Admin'))return commandError();const t=onlinePlayerByQuery(parts.shift()),dest=cleanWorld(parts.shift());if(!t||!dest)return commandError('Pakai: /forcewarp <player> <world>');if(!targetAllowed(session.player,t))return commandError('Target role terlalu tinggi.');queueEvent(t.playerId,{type:'staff-warp',world:dest,reason:'FORCEWARP'});addAudit(db,session.player,'forcewarp',t.playerId,{dest});saveDb(db);return ok(`Forcewarped ${t.displayName} → ${dest}`)}
  if(cmd==='give'){if(role!=='Owner')return commandError();const rawItem=String(parts[0]||'').slice(0,40),amount=Math.max(1,Math.min(200,Math.floor(Number(parts[1]||1))));let target=session.player;if(parts[2]){const r=resolveWorldTarget(world,parts[2]);if(!r.player)return commandError('Target player tidak ditemukan.');target=r.player}if(!rawItem)return commandError('Pakai: /give <item> [amount] [player]');const GIVE_ITEMS=new Set(['grass','dirt','stone','wood','leaf','sand','glass','brick','ice','metal','caveStone','moss','lava','farmBlock','woodPlatform','woodDoor','worldDoor','bedrock','grassSeed','dirtSeed','stoneSeed','woodSeed','leafSeed','sandSeed','glassSeed','brickSeed','iceSeed','metalSeed','caveStoneSeed','mossSeed','farmSeed','platformSeed','doorSeed','worldDoorSeed','redShirt','bluePants','blackHair','whiteShoes','pixoraWing','alphaWing','pixoraHat','smallLock','bigLock','hugeLock','worldLock','punchJammer','pickaxe','sunnyOrb','rainOrb','cloudyOrb','fogOrb','stormOrb','spliceBook']);const item=[...GIVE_ITEMS].find(x=>x.toLowerCase()===rawItem.toLowerCase());if(!item)return commandError('Item tidak dikenal.');const targetSave=getPlayerSave(db,target.playerId);if(!targetSave)return commandError('Target belum memiliki save server.');const inv=targetSave.inventory||{};inv[item]=Math.min(200,Number(inv[item]||0)+amount);targetSave.inventory=inv;if(!db.ownerGrantedItems||typeof db.ownerGrantedItems!=='object')db.ownerGrantedItems={};if(['bedrock','alphaWing','pixoraHat'].includes(item)){const grants=new Set(Array.isArray(db.ownerGrantedItems[target.playerId])?db.ownerGrantedItems[target.playerId]:[]);grants.add(item);db.ownerGrantedItems[target.playerId]=[...grants]}setPlayerSave(db,target.playerId,targetSave);saveDb(db);const live=sessionByPlayerId(target.playerId)?.session;if(live)queueEvent(target.playerId,{type:'staff-save-refresh',playerSave:targetSave});addAudit(db,session.player,'give',target.playerId,{item,amount});saveDb(db);return ok('Gave '+amount+' '+item+' to '+target.displayName)}
  if(cmd==='announce'){if(!hasRole(role,'Admin'))return commandError();const text=parts.join(' ').slice(0,300);if(!text)return commandError('Pakai: /announce <pesan>');broadcastSystem(db,text,'ANNOUNCEMENT');addAudit(db,session.player,'announce','',{text});saveDb(db);return ok('Announcement sent')}
  if(cmd==='slowmode'){if(!hasRole(role,'Admin'))return commandError();const sec=Math.max(0,Math.min(120,Math.floor(Number(parts[0]||0))));db.worldSlowmode[world]=sec;addAudit(db,session.player,'slowmode',world,{seconds:sec});appendSystemChat(world,sec?`Slowmode enabled: ${sec}s`:'Slowmode disabled','SYSTEM');saveDb(db);return ok(sec?`Slowmode ${sec}s`:'Slowmode OFF')}
  if(cmd==='eventxgems'){if(!hasRole(role,'Admin'))return commandError();const arg=String(parts.shift()||'').toLowerCase();if(arg==='off'){db.gemEvent={multiplier:1,until:0,by:pid};broadcastSystem(db,'xGems event ended.','EVENT');saveDb(db);return ok('xGems OFF',{gemEvent:db.gemEvent})}const mult=Math.max(1,Math.min(10,Number(arg||0))),mins=Math.max(1,Math.min(1440,Math.floor(Number(parts.shift()||60))));if(!Number.isFinite(mult)||mult<=1)return commandError('Pakai: /eventxgems <2-10> [minutes] atau /eventxgems off');db.gemEvent={multiplier:mult,until:Date.now()+mins*60000,by:pid};broadcastSystem(db,`${mult}x GEMS EVENT active for ${mins} minutes!`,'EVENT');addAudit(db,session.player,'eventxgems','',{mult,mins});saveDb(db);return ok(`${mult}x Gems ${mins}m`,{gemEvent:db.gemEvent})}
  if(cmd==='banworld'||cmd==='unbanworld'){if(!hasRole(role,'Admin'))return commandError();const w=cleanWorld(parts.shift()||world);if(!w)return commandError('World tidak valid.');if([HELL_WORLD,'START','SYSTEM'].includes(w))return commandError('System world protected.');if(cmd==='banworld'){const reason=parts.join(' ').slice(0,160)||'Staff world ban';db.bannedWorlds[w]={at:Date.now(),by:pid,byName:session.player.displayName,reason};addAudit(db,session.player,'ban-world',w,{reason});moderationAnnounce(db,session.player,`WORLD ${w} was BANNED • ${reason}`);for(const pp of worldPresence.get(w)?.values()||[])if(!hasRole(pp.role,'Moderator'))queueEvent(pp.playerId,{type:'world-kick',world:w,reason:'WORLD_CLOSED'});saveDb(db);return ok('World banned '+w)}delete db.bannedWorlds[w];addAudit(db,session.player,'unban-world',w,{});moderationAnnounce(db,session.player,`WORLD ${w} was UNBANNED`);saveDb(db);return ok('World unbanned '+w)}
  if(cmd==='role'){if(role!=='Owner')return commandError();const t=resolveAnyKnownPlayer(db,parts.shift()),newRole=String(parts.shift()||'').toLowerCase(),roleMap={player:'Player',moderator:'Moderator',admin:'Admin'};if(!t?.account||!roleMap[newRole])return commandError('Pakai: /role <player> <player|moderator|admin>');if(String(t.playerId)===pid)return commandError('Owner tidak dapat mengubah role sendiri.');t.account.role=roleMap[newRole];const live=sessionByPlayerId(t.playerId)?.session;if(live)live.player.role=roleMap[newRole];addAudit(db,session.player,'role',t.playerId,{role:roleMap[newRole]});saveDb(db);return ok(`${t.displayName} → ${roleMap[newRole]}`)}
  if(cmd==='hell'){if(role!=='Owner')return commandError();const t=targetForStaff(db,parts.shift());if(!t)return commandError('Player tidak ditemukan.');if(!targetAllowed(session.player,t))return commandError('Target protected.');const reason=parts.join(' ').slice(0,160)||'Owner punishment';db.hellJail[t.playerId]={at:Date.now(),by:pid,reason};addAudit(db,session.player,'hell',t.playerId,{reason});moderationAnnounce(db,session.player,`${t.displayName} was sent to HELL • ${reason}`);saveDb(db);queueEvent(t.playerId,{type:'staff-warp',world:HELL_WORLD,reason:'HELL'});return ok('Sent '+t.displayName+' to HELL')}
  if(cmd==='unhell'){if(role!=='Owner')return commandError();const known=resolveAnyKnownPlayer(db,parts[0]);let targetId=known?.playerId||String(parts[0]||'');if(!db.hellJail[targetId])return commandError('Player tidak sedang di HELL.');delete db.hellJail[targetId];addAudit(db,session.player,'unhell',targetId,{});moderationAnnounce(db,session.player,`${known?.displayName||targetId} was released from HELL`);saveDb(db);return ok('Released '+(known?.displayName||targetId)+' from HELL')}
  if(cmd==='vanish'||cmd==='unvanish'){if(role!=='Owner')return commandError();const on=cmd==='vanish';session.player.vanished=on;const p=room?.get(pid);if(p)p.vanished=on;addAudit(db,session.player,on?'vanish':'unvanish',pid,{});saveDb(db);return ok(on?'Vanish ON':'Vanish OFF',{vanished:on})}
  if(cmd==='staff'){if(role!=='Owner')return commandError();const arg=String(parts[0]||'').toLowerCase(),on=arg==='on'?true:arg==='off'?false:!session.player.staffMode;session.player.staffMode=on;const p=room?.get(pid);if(p)p.staffMode=on;addAudit(db,session.player,'staff-mode',pid,{enabled:on});saveDb(db);return ok(on?'Staff Mode ON • fly/noclip aktif':'Staff Mode OFF',{staffMode:on})}
  if(cmd==='ownerbreak'){if(role!=='Owner')return commandError();const arg=String(parts[0]||'').toLowerCase();if(!['on','off'].includes(arg))return commandError('Pakai: /ownerbreak <on|off>');const on=arg==='on';session.player.ownerBreak=on;const p=room?.get(pid);if(p)p.ownerBreak=on;addAudit(db,session.player,'owner-break-mode',pid,{enabled:on});saveDb(db);return ok(on?'Owner Break Mode ON • protected objects can be broken':'Owner Break Mode OFF',{ownerBreak:on})}
  if(cmd==='audit'){if(role!=='Owner')return commandError();const n=Math.max(1,Math.min(10,Math.floor(Number(parts[0]||5)))),rows=(db.auditLog||[]).slice(-n).reverse().map(a=>a.actorName+' '+a.action+(a.target?' → '+a.target:'')).join(' | ');return ok(rows||'Audit log kosong.',{history:true,historyName:'AUDIT'})}
  if(cmd==='resetserver'){if(role!=='Owner')return commandError();const arg=String(parts[0]||'').toLowerCase();if(arg==='cancel'){if(!restartPlan.active)return commandError('Tidak ada restart countdown aktif.');cancelServerRestart(db,session.player);return ok('Server restart cancelled.',{restartCancelled:true,serverRestart:publicRestartPlan()})}const minutes=Math.floor(Number(arg));if(!Number.isFinite(minutes)||minutes<1||minutes>1440)return commandError('Pakai: /resetserver <minutes> atau /resetserver cancel');const scheduled=scheduleServerRestart(db,session.player,minutes);if(!scheduled.ok)return commandError('Restart countdown sudah aktif. Pakai /resetserver cancel dulu.');return ok(`Server restart scheduled in ${minutes} minute${minutes===1?'':'s'}.`,{serverRestart:scheduled.plan})}
  return commandError();
}
function accountByPlayerId(db,playerId){return Object.values(db.accounts||{}).find(a=>a&&a.playerId===playerId)||null}
function saveRecordByPlayerId(db,playerId){const a=accountByPlayerId(db,playerId);if(a)return {kind:'account',record:a};const g=guestByPlayerId(db,playerId);return g?{kind:'guest',record:g}:null}
function getPlayerSave(db,playerId){return saveRecordByPlayerId(db,playerId)?.record?.playerSave||null}
function setPlayerSave(db,playerId,save){const ref=saveRecordByPlayerId(db,playerId);if(!ref)return false;ref.record.playerSave=save;return true}
function knownPlayerLabel(db,id){const a=accountByPlayerId(db,id);if(a)return a.username||a.displayName||id;const g=guestByPlayerId(db,id);return g?.displayName||id}
function sessionByPlayerId(playerId){for(const [t,s] of sessions){if(s?.player?.playerId===playerId)return {token:t,session:s}}return null}
function queueEvent(playerId,ev){const q=knockbackEvents.get(playerId)||[];q.push(ev);knockbackEvents.set(playerId,q.slice(-20))}
function cleanEmail(v){const e=String(v||'').trim().toLowerCase().slice(0,160);return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(e)?e:''}
function publicTrade(trade,db){if(!trade)return null;const label=id=>knownPlayerLabel(db,id);return {id:trade.id,a:trade.a,b:trade.b,status:trade.status,offers:trade.offers,confirmed:trade.confirmed,finalConfirmed:trade.finalConfirmed,names:{[trade.a]:label(trade.a),[trade.b]:label(trade.b)},updatedAt:trade.updatedAt}}
function cancelTradeFor(playerId,reason='CANCELLED'){const id=tradeByPlayer.get(playerId);if(!id)return;const tr=trades.get(id);if(!tr)return;tr.status='cancelled';tr.reason=reason;tr.updatedAt=Date.now();tradeByPlayer.delete(tr.a);tradeByPlayer.delete(tr.b);queueEvent(tr.a,{type:'trade-cancelled',tradeId:id,reason});queueEvent(tr.b,{type:'trade-cancelled',tradeId:id,reason})}


function sessionKey(t){return crypto.createHash('sha256').update(String(t||'')).digest('hex')}
function durablePlayer(db,player){
  if(!player)return null;
  if(player.accountType==='account'){const a=db.accounts?.[player.accountId];if(!a)return null;return {...player,playerId:a.playerId,displayName:a.username||a.displayName||player.displayName,role:roleForAccount(a)}}
  const g=db.guests?.[player.playerId];if(!g)return null;return {...player,displayName:g.displayName||player.displayName,role:'Player',accountType:'guest'}
}
function createSession(player){
  const t=token(),db=loadDb(),now=Date.now();
  if(player.accountType==='account'&&player.accountId){
    const old=activeAccountTokens.get(player.accountId);
    if(old&&old!==t){const oldSession=sessions.get(old);if(oldSession)removePresence(oldSession.player.playerId);sessions.delete(old);revokedTokens.set(old,{reason:'SESSION_REPLACED',at:now})}
    for(const [k,v] of Object.entries(db.sessions||{}))if(v?.player?.accountType==='account'&&v.player.accountId===player.accountId)delete db.sessions[k];
    activeAccountTokens.set(player.accountId,t);
  }
  const session={player,createdAt:now};sessions.set(t,session);db.sessions[sessionKey(t)]={player:playerPayload(player),createdAt:now,lastSeen:now};saveDb(db);return t;
}
function removePresence(playerId){for(const [world,room] of worldPresence){room.delete(playerId);if(!room.size)worldPresence.delete(world)}}
function sessionFor(req){
  const t=authToken(req);if(!t)return {token:t,error:'INVALID_SESSION'};if(revokedTokens.has(t))return {token:t,error:revokedTokens.get(t).reason||'INVALID_SESSION'};
  let session=sessions.get(t);if(session)return {token:t,session};
  const db=loadDb(),saved=db.sessions?.[sessionKey(t)];if(!saved)return {token:t,error:'INVALID_SESSION'};const player=durablePlayer(db,saved.player);if(!player){delete db.sessions[sessionKey(t)];saveDb(db);return {token:t,error:'INVALID_SESSION'}}
  session={player,createdAt:Number(saved.createdAt||Date.now())};sessions.set(t,session);saved.lastSeen=Date.now();if(player.accountType==='account'&&player.accountId)activeAccountTokens.set(player.accountId,t);return {token:t,session};
}
function requireSession(req,res){const s=sessionFor(req);if(s.error){send(res,401,{error:s.error});return null}return s}
setInterval(()=>{const now=Date.now(),cutoff=now-6*60*60*1000;for(const [t,v] of revokedTokens)if(v.at<cutoff)revokedTokens.delete(t);const db=loadDb(),expiry=now-30*24*60*60*1000;let changed=false;for(const [k,v] of Object.entries(db.sessions||{}))if(Number(v?.lastSeen||v?.createdAt||0)<expiry){delete db.sessions[k];changed=true}if(changed)saveDb(db)},60*60*1000).unref?.();

function pruneRoom(world){const room=worldPresence.get(world);if(!room)return;const cutoff=Date.now()-12000;for(const [id,st] of room){if(st.lastSeen<cutoff)room.delete(id)}if(!room.size)worldPresence.delete(world)}
function sanitizeActionState(a){
  if(!a||typeof a!=='object'||!a.active)return {active:false,seq:Math.max(0,Math.floor(Number(a?.seq||0)))};
  const tx=Math.floor(Number(a.tx)),ty=Math.floor(Number(a.ty));if(!Number.isFinite(tx)||!Number.isFinite(ty))return {active:false,seq:Math.max(0,Math.floor(Number(a.seq||0)))};
  const kind=['block','bg','air'].includes(String(a.kind))?String(a.kind):'air';
  return {active:true,kind,tx,ty,progress:Math.max(0,Math.min(1,Number(a.progress||0))),tool:String(a.tool||'punch').slice(0,16),seq:Math.max(0,Math.floor(Number(a.seq||0)))}
}
function sanitizePresenceEquipment(e){const src=(e&&typeof e==='object')?e:{};const out={};for(const k of ['hair','hat','shirt','pants','shoes','back','tool'])out[k]=src[k]==null?null:String(src[k]).slice(0,40);return out}
function updatePresence(world,p,b){
  if(!worldPresence.has(world))worldPresence.set(world,new Map());
  const room=worldPresence.get(world),prev=room.get(p.playerId)||{},frozen=!!loadDb().freezes?.[p.playerId];
  const nx=frozen&&prev.playerId?Number(prev.x||0):(Number.isFinite(Number(b.x))?Number(b.x):(prev.x||120)),ny=frozen&&prev.playerId?Number(prev.y||0):(Number.isFinite(Number(b.y))?Number(b.y):(prev.y||0));
  room.set(p.playerId,{playerId:p.playerId,displayName:p.displayName,role:p.role||'Player',accountType:p.accountType||'guest',vanished:!!p.vanished,hidden:!!p.hidden,staffMode:!!p.staffMode,x:nx,y:ny,facing:Number(b.facing)<0?-1:1,onGround:frozen?!!prev.onGround:!!b.onGround,vx:frozen?0:(Number.isFinite(Number(b.vx))?Number(b.vx):0),vy:frozen?0:(Number.isFinite(Number(b.vy))?Number(b.vy):0),equipped:sanitizePresenceEquipment(b.equipped||prev.equipped),actionState:sanitizeActionState(b.actionState),lastSeen:Date.now()})
}
function roomView(world,selfId,viewerRole='Player'){pruneRoom(world);const room=worldPresence.get(world);return room?[...room.values()].filter(p=>p.playerId!==selfId&&(!p.vanished||hasRole(viewerRole,'Moderator'))).map(({lastSeen,vanished,staffMode,hidden,...p})=>({...p,role:hidden?'Player':p.role,worldRole:worldMembership(world,p.playerId)})):[]}
function activePresenceIds(){const ids=new Set();for(const [w] of worldPresence){pruneRoom(w);const room=worldPresence.get(w);if(room)for(const id of room.keys())ids.add(id)}return ids}
function canJoinWorld(world,playerId){pruneRoom(world);const room=worldPresence.get(world);if(room?.has(playerId))return {ok:true};if((room?.size||0)>=MAX_WORLD_PLAYERS)return {ok:false,error:'WORLD_FULL'};if(activePresenceIds().size>=MAX_SERVER_PLAYERS)return {ok:false,error:'SERVER_FULL'};return {ok:true}}
function tileOccupiedByPlayer(world,tx,ty){pruneRoom(world);const room=worldPresence.get(world);if(!room)return false;const x=tx*40,y=ty*40;for(const p of room.values()){if(p.vanished)continue;/* Match client movement collision body: wearables/wing visuals never expand placement collision. */const px=Number(p.x||0)+3,py=Number(p.y||0)+8,pw=24,ph=30;if(px<x+40&&px+pw>x&&py<y+40&&py+ph>y)return true}return false}
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
  return {worldId:String(s.worldId||'').slice(0,64),templateVersion:Math.max(0,Math.floor(Number(s.templateVersion||0))),surfaceTile:Number.isFinite(Number(s.surfaceTile))?Number(s.surfaceTile):55,blocks,door,placedDoors,caveBgRemoved:Array.isArray(s.caveBgRemoved)?s.caveBgRemoved.slice(0,12000).filter(v=>typeof v==='string'):[],plants:Array.isArray(s.plants)?s.plants.slice(0,5000).map(p=>sanitizePlant(p,Math.floor(Number(p?.tx)),Math.floor(Number(p?.ty)))).filter(Boolean):[],locks:Array.isArray(s.locks)?s.locks.slice(0,1000).filter(l=>l&&Number.isFinite(Number(l.tx))&&Number.isFinite(Number(l.ty))).map(l=>({...l,tx:Math.floor(Number(l.tx)),ty:Math.floor(Number(l.ty)),type:String(l.type||'worldLock').slice(0,32),owner:String(l.owner||'').slice(0,80),trusted:Array.isArray(l.trusted)?l.trusted.slice(0,200).map(v=>String(v).slice(0,80)):[]})):[],weatherOrbs:Array.isArray(s.weatherOrbs)?s.weatherOrbs.slice(0,100):[],jammers,worldBans:Array.isArray(s.worldBans)?s.worldBans.slice(0,500).map(v=>String(v).slice(0,80)):[],weather:(s.weather&&typeof s.weather==='object')?{type:String(s.weather.type||'sunny').slice(0,16)}:{type:'sunny'},drops:Array.isArray(s.drops)?s.drops.slice(0,5000).map(sanitizeDrop).filter(Boolean):[],savedAt:Math.max(0,Number(s.savedAt||0))}
}
function sanitizePlant(p,tx,ty){
  if(!p||typeof p!=='object')return null;const seed=String(p.seed||'').slice(0,40);if(!seed)return null;
  const rarity=Math.max(1,Math.min(99,Number(p.rarity||1))),growMs=30000+(Math.floor(rarity)-1)*15000;return {tx,ty,seed,spliced:!!p.spliced,rarity,plantedAt:Math.max(0,Number(p.plantedAt||Date.now())),growMs,hitsTaken:Math.max(0,Math.min(99,Math.floor(Number(p.hitsTaken||0)))),lastHitAt:Math.max(0,Number(p.lastHitAt||0))}
}
function migrateLegacySurfaceGrass(snapshot){
  if(!snapshot||!Array.isArray(snapshot.blocks))return false;
  const sy=Math.floor(Number(snapshot.surfaceTile||55)),surfaceGrass=snapshot.blocks.filter(b=>b&&b.t==='grass'&&Math.floor(Number(b.y)/40)===sy);
  // 14.8.1 generated nearly the full surface as Grass. Convert only majority-row cases so player-built Grass survives.
  if(surfaceGrass.length<50)return false;
  for(const b of surfaceGrass)b.t='dirt';
  return true;
}
function applyPixoraKingdomTemplateToSnapshot(snapshot){
  if(!snapshot||Number(snapshot.templateVersion||0)>=PIXORA_KINGDOM_TEMPLATE_VERSION)return false;
  const gy=Math.floor(Number(snapshot.surfaceTile||55));
  const map=new Map();for(const b of snapshot.blocks||[]){const tx=Math.floor(Number(b.x)/40),ty=Math.floor(Number(b.y)/40);map.set(tx+','+ty,{x:tx*40,y:ty*40,t:String(b.t||'dirt')})}
  const set=(tx,ty,t)=>{if(tx<0||ty<0||tx>=100||ty>=100)return;map.set(tx+','+ty,{x:tx*40,y:ty*40,t})};
  const clear=(tx,ty)=>map.delete(tx+','+ty);
  const fill=(x1,y1,x2,y2,t)=>{for(let y=y1;y<=y2;y++)for(let x=x1;x<=x2;x++)set(x,y,t)};
  const clearRect=(x1,y1,x2,y2)=>{for(let y=y1;y<=y2;y++)for(let x=x1;x<=x2;x++)clear(x,y)};
  const tree=(cx)=>{for(let y=gy-4;y<=gy-1;y++)set(cx,y,'wood');for(let y=gy-8;y<=gy-5;y++)for(let x=cx-3;x<=cx+3;x++)if(Math.abs(x-cx)+Math.abs((gy-6)-y)<=5)set(x,y,'leaf');set(cx-2,gy-4,'leaf');set(cx+2,gy-4,'leaf')};
  clearRect(24,gy-20,75,gy-1);
  for(let x=12;x<=87;x++)set(x,gy,'brick');
  fill(28,gy-11,35,gy-1,'stone');fill(64,gy-11,71,gy-1,'stone');fill(29,gy-13,34,gy-12,'stone');fill(65,gy-13,70,gy-12,'stone');
  for(const x of [28,30,32,34,35])set(x,gy-14,'metal');for(const x of [64,65,67,69,71])set(x,gy-14,'metal');set(31,gy-15,'farmBlock');set(32,gy-15,'farmBlock');set(67,gy-15,'farmBlock');set(68,gy-15,'farmBlock');
  fill(39,gy-10,60,gy-1,'brick');fill(43,gy-15,56,gy-11,'stone');for(const x of [43,45,47,49,51,53,55,56])set(x,gy-16,'metal');fill(37,gy-8,38,gy-1,'stone');fill(61,gy-8,62,gy-1,'stone');
  for(const [x,y] of [[30,gy-9],[33,gy-6],[66,gy-9],[69,gy-6],[44,gy-13],[55,gy-13],[43,gy-7],[56,gy-7]])set(x,y,'glass');
  for(let x=27;x<=36;x++)set(x,gy-7,'woodPlatform');for(let x=63;x<=72;x++)set(x,gy-7,'woodPlatform');for(let x=42;x<=57;x++)if(x<47||x>52)set(x,gy-9,'woodPlatform');
  clearRect(48,gy-6,51,gy-1);fill(47,gy-6,47,gy-1,'stone');fill(52,gy-6,52,gy-1,'stone');for(let x=48;x<=51;x++)set(x,gy-7,'stone');set(47,gy-7,'metal');set(52,gy-7,'metal');
  for(let y=gy-14;y<=gy-9;y++)set(48,y,'farmBlock');for(let x=49;x<=51;x++)set(x,gy-14,'farmBlock');set(51,gy-13,'farmBlock');set(51,gy-12,'farmBlock');for(let x=49;x<=50;x++)set(x,gy-11,'farmBlock');
  for(let x=47;x<=52;x++)set(x,gy-18,'farmBlock');for(const x of [47,49,52])set(x,gy-19,'farmBlock');set(46,gy-18,'metal');set(53,gy-18,'metal');
  tree(17);tree(82);tree(8);tree(92);
  for(const base of [76,86]){set(base,gy-2,'wood');set(base,gy-1,'wood');set(base+6,gy-2,'wood');set(base+6,gy-1,'wood');for(let x=base;x<=base+6;x++)set(x,gy-4,'woodPlatform');set(base+1,gy-3,'farmBlock');set(base+5,gy-3,'farmBlock')}
  for(const x of [22,77]){set(x,gy-2,'wood');set(x,gy-1,'wood');set(x,gy-3,'farmBlock')}
  clear(49,gy-1);clear(50,gy-1);clear(51,gy-1);set(50,gy,'bedrock');
  snapshot.blocks=[...map.values()];snapshot.door={x:50*40+2,y:gy*40-40,w:36,h:40};snapshot.templateVersion=PIXORA_KINGDOM_TEMPLATE_VERSION;snapshot.weather={type:'sunny'};snapshot.savedAt=Date.now();
  // Clear conflicting objects only inside the castle construction zone; side-world player content survives.
  const inRoyalZone=o=>{const tx=Number(o?.tx),ty=Number(o?.ty);return Number.isFinite(tx)&&Number.isFinite(ty)&&tx>=24&&tx<=75&&ty>=gy-20&&ty<=gy};
  snapshot.plants=(snapshot.plants||[]).filter(o=>!inRoyalZone(o));snapshot.locks=(snapshot.locks||[]).filter(o=>!inRoyalZone(o));snapshot.placedDoors=(snapshot.placedDoors||[]).filter(o=>!inRoyalZone(o));snapshot.weatherOrbs=(snapshot.weatherOrbs||[]).filter(o=>!inRoyalZone(o));snapshot.jammers=(snapshot.jammers||[]).filter(o=>!inRoyalZone(o));
  return true;
}
function ensurePixoraKingdom(world,state){
  if(world!=='PIXORA'||!state||Number(state.snapshot?.templateVersion||0)>=PIXORA_KINGDOM_TEMPLATE_VERSION)return false;
  const db=loadDb(),rows=Array.isArray(db.worldRecoveryBackups?.[world])?db.worldRecoveryBackups[world]:[];rows.unshift({at:Date.now(),revision:state.revision,snapshot:JSON.parse(JSON.stringify(state.snapshot)),reason:'before-pixora-kingdom'});db.worldRecoveryBackups[world]=rows.slice(0,3);
  if(!applyPixoraKingdomTemplateToSnapshot(state.snapshot))return false;state.revision=Math.max(1,Number(state.revision||1))+1;state.updatedAt=Date.now();persistWorld(world,state);saveDb(db);return true;
}

function upgradeOwnerWorldLocks(snapshot){
  if(!snapshot||!Array.isArray(snapshot.locks))return false;const db=loadDb();let changed=false;
  for(const l of snapshot.locks){if(l?.type!=='worldLock')continue;const a=accountByPlayerId(db,String(l.owner||''));if(a&&roleForAccount(a)==='Owner'){l.type='ownerLock';l.hitsTaken=0;changed=true}}
  return changed
}
function loadWorldFromDb(world){
  const db=loadDb(),raw=db.worlds?.[world];if(!raw)return null;
  const snapshot=sanitizeWorldSnapshot(raw.snapshot),migrated=migrateLegacySurfaceGrass(snapshot),ownerLockUpgraded=upgradeOwnerWorldLocks(snapshot);
  const state={revision:Math.max(1,Number(raw.revision||1))+((migrated||ownerLockUpgraded)?1:0),snapshot,chat:Array.isArray(raw.chat)?raw.chat.slice(-30):[],updatedAt:Number(raw.updatedAt||Date.now())};
  if(migrated||ownerLockUpgraded){db.worlds[world]={revision:state.revision,snapshot:state.snapshot,chat:state.chat,updatedAt:Date.now()};saveDb(db)}
  worldStates.set(world,state);return state
}
function persistWorld(world,state){const db=loadDb();db.worlds[world]={revision:state.revision,snapshot:state.snapshot,chat:(state.chat||[]).slice(-30),updatedAt:Date.now()};saveDb(db)}
function getOrCreateWorldState(world,clientSnapshot){let state=worldStates.get(world)||loadWorldFromDb(world);if(!state){const snapshot=sanitizeWorldSnapshot(clientSnapshot);migrateLegacySurfaceGrass(snapshot);upgradeOwnerWorldLocks(snapshot);state={revision:1,snapshot,chat:[],updatedAt:Date.now()};worldStates.set(world,state);persistWorld(world,state)}return state}
function worldActivityScore(s){if(!s)return 0;return (s.locks?.length||0)*50+(s.plants?.length||0)*14+(s.placedDoors?.length||0)*22+(s.weatherOrbs?.length||0)*10+(s.jammers?.length||0)*10+(s.caveBgRemoved?.length||0)*2+(s.worldBans?.length||0)*10}
function maybeRecoverFreshWorldFromClient(world,state,input,playerId){
  if(!state||!input||typeof input!=='object')return false;const client=sanitizeWorldSnapshot(input),serverSnap=state.snapshot;
  // Never let an older local PIXORA snapshot undo the newer one-time Royal Kingdom template.
  if(world==='PIXORA'&&Number(serverSnap?.templateVersion||0)>Number(client.templateVersion||0))return false;
  if(!client.worldId||!serverSnap?.worldId||client.worldId===serverSnap.worldId||client.blocks.length<80)return false;
  const age=Date.now()-Number(state.updatedAt||0),serverActivity=worldActivityScore(serverSnap),clientActivity=worldActivityScore(client),blockDelta=Math.abs(client.blocks.length-(serverSnap.blocks?.length||0));
  const serverLooksFresh=state.revision<=3&&age>=0&&age<30*60*1000&&serverActivity<=10;
  const clientHasOwnership=(client.locks||[]).some(l=>String(l.owner||'')===String(playerId||''));
  const clientHasHistory=clientHasOwnership||clientActivity>=14||blockDelta>=8;
  if(!serverLooksFresh||!clientHasHistory)return false;
  const db=loadDb(),rows=Array.isArray(db.worldRecoveryBackups?.[world])?db.worldRecoveryBackups[world]:[];rows.unshift({at:Date.now(),revision:state.revision,snapshot:serverSnap});db.worldRecoveryBackups[world]=rows.slice(0,3);
  state.snapshot=client;state.revision=Math.max(1,Number(state.revision||1))+1;state.updatedAt=Date.now();persistWorld(world,state);return true
}

const DROP_RATE={grass:{block:.42,seed:.30,gems:.28},dirt:{block:.38,seed:.20,gems:.24},stone:{block:.32,seed:.08,gems:.34},wood:{block:.45,seed:.24,gems:.25},leaf:{block:.24,seed:.42,gems:.22},sand:{block:.40,seed:.18,gems:.22},glass:{block:.31,seed:.12,gems:.38},brick:{block:.36,seed:.12,gems:.32},ice:{block:.34,seed:.22,gems:.30},metal:{block:.28,seed:.06,gems:.46},caveStone:{block:.32,seed:.10,gems:.40},moss:{block:.36,seed:.34,gems:.24},lava:{block:.22,seed:0,gems:.44},farmBlock:{block:.46,seed:.34,gems:.38},woodPlatform:{block:.45,seed:.20,gems:.20},woodDoor:{block:.40,seed:.16,gems:.24},worldDoor:{block:.30,seed:.10,gems:.34}};
const SEED_FOR_BLOCK={grass:'grassSeed',dirt:'dirtSeed',stone:'stoneSeed',wood:'woodSeed',leaf:'leafSeed',sand:'sandSeed',glass:'glassSeed',brick:'brickSeed',ice:'iceSeed',metal:'metalSeed',caveStone:'caveStoneSeed',moss:'mossSeed',farmBlock:'farmSeed',woodPlatform:'platformSeed',woodDoor:'doorSeed',worldDoor:'worldDoorSeed'};
const BLOCK_RARITY={grass:1,dirt:1,stone:1,caveStone:1,lava:1,wood:2,leaf:2,sand:2,brick:3,moss:3,glass:4,ice:3,metal:3,farmBlock:8,woodPlatform:3,woodDoor:5,worldDoor:10,bedrock:99};
const PLANT_BLOCK={grassSeed:'grass',dirtSeed:'dirt',stoneSeed:'stone',woodSeed:'wood',leafSeed:'leaf',sandSeed:'sand',glassSeed:'glass',brickSeed:'brick',iceSeed:'ice',metalSeed:'metal',caveStoneSeed:'caveStone',mossSeed:'moss',farmSeed:'farmBlock',platformSeed:'woodPlatform',doorSeed:'woodDoor',worldDoorSeed:'worldDoor'};
const PLANT_YIELD={grassSeed:[1,3],dirtSeed:[1,4],stoneSeed:[1,2],woodSeed:[2,4],leafSeed:[1,3],sandSeed:[1,4],glassSeed:[1,2],brickSeed:[1,3],iceSeed:[1,3],metalSeed:[1,2],caveStoneSeed:[1,3],mossSeed:[1,4],farmSeed:[1,3],platformSeed:[1,3],doorSeed:[1,2],worldDoorSeed:[1,1]};
const BLOCK_HITS_SERVER={leaf:2,sand:2,glass:2,dirt:3,grass:3,ice:3,moss:3,wood:4,stone:5,brick:5,lava:6,caveStone:6,metal:7,farmBlock:4,woodPlatform:3,woodDoor:4,worldDoor:6};
function plantMatureServer(p){return Date.now()-Number(p?.plantedAt||0)>=Number(p?.growMs||0)}
function immaturePlantHits(p){const block=PLANT_BLOCK[String(p?.seed||'')]||'dirt';return Math.max(2,(BLOCK_HITS_SERVER[block]||3)*2)}
function gemAmountForRarity(r){r=Math.max(1,Number(r||1));if(r<=10)return 1;const max=1+Math.floor((r-1)/10);return 1+Math.floor(Math.random()*max)}
function seedRarity(seed){const block=PLANT_BLOCK[seed];return BLOCK_RARITY[block]||1}
function seedGemChance(seed){const r=seedRarity(seed);return Math.min(.48,.08+r*.025)}
function seedGemAmount(seed){return seed==='farmSeed'?1+crypto.randomInt(14):gemAmountForRarity(seedRarity(seed))}
function makeDrop(tx,ty,item,amount=1,kind='item',delay=250,spread=16){return sanitizeDrop({x:tx*40+20+(Math.random()-.5)*spread,y:ty*40+20+(Math.random()-.5)*10,item,kind,amount,pickupAfter:Date.now()+delay},{serverId:true})}
function addDrops(state,list){const added=[];for(const d of list.filter(Boolean)){if(state.snapshot.drops.length>=5000)break;state.snapshot.drops.push(d);added.push(d)}return added}
function currentGemMultiplier(){const db=loadDb(),g=db.gemEvent||{};if(Number(g.until||0)>0&&Date.now()>=Number(g.until)){db.gemEvent={multiplier:1,until:0};saveDb(db);return 1}return Math.max(1,Math.min(10,Number(g.multiplier||1)))}
function boostedGemAmount(n){return Math.max(1,Math.floor(Number(n||1)*currentGemMultiplier()))}
function generateBreakDrops(blockType,tx,ty){
  // Build 14.6.3: Block + Seed kembali memakai drop-rate farming lama. Clothes/Wearable tetap Store-only.
  const out=[],rate=DROP_RATE[blockType]||{block:.25,seed:0,gems:.25},r=Math.random();
  if(r<rate.block)out.push(makeDrop(tx,ty,blockType));
  else if(rate.seed>0&&r<rate.block+rate.seed){const seed=SEED_FOR_BLOCK[blockType];if(seed)out.push(makeDrop(tx,ty,seed))}
  if(Math.random()<(rate.gems||.25)){const amount=blockType==='farmBlock'?1+crypto.randomInt(14):gemAmountForRarity(BLOCK_RARITY[blockType]||1);out.push(makeDrop(tx,ty,null,boostedGemAmount(amount),'gems',0,12))}
  return out;
}
function generateHarvestDrops(plant,tx,ty){
  const seed=String(plant.seed||''),block=PLANT_BLOCK[seed]||'dirt',range=PLANT_YIELD[seed]||[1,3],amount=range[0]+crypto.randomInt(range[1]-range[0]+1),out=[];
  for(let i=0;i<amount;i++)out.push(makeDrop(tx,ty,block,1,'item',250,20));
  if(Math.random()<.46)out.push(makeDrop(tx,ty,seed));
  if(Math.random()<.10)out.push(makeDrop(tx,ty,seed));
  if(Math.random()<seedGemChance(seed))out.push(makeDrop(tx,ty,null,boostedGemAmount(seedGemAmount(seed)),'gems',0,12));
  return {drops:out,amount,item:block};
}

function serverLockBounds(l){
  const sizes={smallLock:10,bigLock:20,hugeLock:35,worldLock:100,ownerLock:100},size=sizes[String(l?.type||'worldLock')]||100;if(size>=100)return {x1:0,y1:0,x2:99,y2:99};const half=Math.floor(size/2);return {x1:Number(l.tx)-half,y1:Number(l.ty)-half,x2:Number(l.tx)-half+size-1,y2:Number(l.ty)-half+size-1}
}
function serverLockCovering(state,tx,ty){return (state?.snapshot?.locks||[]).find(l=>{const b=serverLockBounds(l);return tx>=b.x1&&tx<=b.x2&&ty>=b.y1&&ty<=b.y2})||null}
function ownerBreakActive(session){return String(session?.player?.role||'')==='Owner'&&session?.player?.ownerBreak===true}
function canSessionEditTile(state,session,tx,ty){if(ownerBreakActive(session))return true;const l=serverLockCovering(state,tx,ty);if(!l)return true;const pid=String(session?.player?.playerId||'');return String(l.owner||'')===pid||(Array.isArray(l.trusted)&&l.trusted.includes(pid))}
function sessionTileInReach(world,session,tx,ty){pruneRoom(world);const p=worldPresence.get(world)?.get(session?.player?.playerId);if(!p)return false;const gx=Math.floor((Number(p.x||0)+15)/40),gy=Math.floor((Number(p.y||0)+20)/40);return Math.abs(tx-gx)<=2&&Math.abs(ty-gy)<=2}

function applyWorldAction(state,action,session,world){
  if(!state||!action||typeof action!=='object')return {accepted:false};
  const type=String(action.type||'');
  if(type==='player-punch'){
    const sourceId=session?.player?.playerId,targetId=String(action.targetPlayerId||'').slice(0,80),room=worldPresence.get(world);
    if(!sourceId||!targetId||targetId===sourceId||!room)return {accepted:false};pruneRoom(world);
    const src=room.get(sourceId),target=room.get(targetId);if(!src||!target)return {accepted:false};if(target.vanished&&!hasRole(session?.player?.role,'Moderator'))return {accepted:false};
    if(Array.isArray(state.snapshot.jammers)&&state.snapshot.jammers.some(j=>j?.type==='punch'))return {accepted:true,blocked:true};
    const sx=Number(src.x||0)+15,sy=Number(src.y||0)+20,txp=Number(target.x||0)+15,typ=Number(target.y||0)+20,dx=txp-sx,dy=Math.abs(typ-sy),facing=Number(src.facing)<0?-1:1;
    if(Math.sign(dx||facing)!==facing||Math.abs(dx)>98||dy>42)return {accepted:false};
    queueKnockback(targetId,{type:'knockback',vx:facing*4.8,vy:-5.8,from:sourceId,at:Date.now()});return {accepted:true,knockback:true,targetId};
  }
  if(type==='world-command'){
    const sourceId=session?.player?.playerId,targetId=String(action.targetPlayerId||'').slice(0,80),cmd=String(action.command||'');
    const wl=Array.isArray(state.snapshot.locks)&&state.snapshot.locks.find(l=>isWorldOwnershipLockType(l?.type)&&String(l.owner||'')===sourceId);
    const room=worldPresence.get(world);pruneRoom(world);const src=room?.get(sourceId),target=room?.get(targetId);
    if(!wl||!src||!target||targetId===sourceId)return {accepted:false};if(roleRank(target.role)>roleRank(session?.player?.role||'Player'))return {accepted:false};
    if(cmd==='pull'){queueEvent(targetId,{type:'pull',world,x:Number(src.x||0),y:Number(src.y||0)-44,from:sourceId});return {accepted:true,command:'pull'}}
    if(cmd==='kick'){queueEvent(targetId,{type:'world-kick',world,reason:'KICKED',from:sourceId});return {accepted:true,command:'kick'}}
    if(cmd==='ban'){state.snapshot.worldBans=Array.isArray(state.snapshot.worldBans)?state.snapshot.worldBans:[];if(!state.snapshot.worldBans.includes(targetId))state.snapshot.worldBans.push(targetId);state.revision++;state.updatedAt=Date.now();queueEvent(targetId,{type:'world-kick',world,reason:'BANNED',from:sourceId});const db=loadDb();addAudit(db,session.player,'world-player-ban',targetId,{world});addWorldLog(db,world,session.player,'world-player-ban',targetId,{});appendSystemChat(world,`${target.displayName} was banned from this world${session.player.hidden?'':' • by '+session.player.displayName}`,'MODERATION');saveDb(db);return {accepted:true,command:'ban',changed:true}}
    if(cmd==='access'){
      wl.trusted=Array.isArray(wl.trusted)?wl.trusted:[];const i=wl.trusted.indexOf(targetId),grant=i<0;
      if(grant)wl.trusted.push(targetId);else wl.trusted.splice(i,1);
      state.revision++;state.updatedAt=Date.now();const db=loadDb();addAudit(db,session.player,grant?'world-access-add':'world-access-remove',targetId,{world});addWorldLog(db,world,session.player,grant?'world-access-add':'world-access-remove',targetId,{});appendSystemChat(world,`${target.displayName} ${grant?'is now':'is no longer'} World Admin${session.player.hidden?'':' • by '+session.player.displayName}`,'WORLD');saveDb(db);return {accepted:true,command:'access',accessGranted:grant,changed:true}
    }
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
  if(type==='owner-break'){
    if(!ownerBreakActive(session)||!sessionTileInReach(world,session,tx,ty))return {accepted:false};
    const main=state.snapshot.door;if(main&&px<Number(main.x||0)+Number(main.w||36)&&px+40>Number(main.x||0)&&py<Number(main.y||0)+Number(main.h||40)&&py+40>Number(main.y||0)){state.snapshot.door=null;changed=true;result.removedKind='main-door'}
    else{let i=state.snapshot.placedDoors.findIndex(d=>Number(d.tx)===tx&&Number(d.ty)===ty);if(i>=0){result.removedKind='door';result.removedType=state.snapshot.placedDoors[i].type;state.snapshot.placedDoors.splice(i,1);changed=true}
      else if((i=state.snapshot.locks.findIndex(l=>Number(l.tx)===tx&&Number(l.ty)===ty))>=0){result.removedKind='lock';result.removedType=state.snapshot.locks[i].type;state.snapshot.locks.splice(i,1);changed=true}
      else if((i=state.snapshot.weatherOrbs.findIndex(o=>Number(o.tx)===tx&&Number(o.ty)===ty))>=0){result.removedKind='weather-orb';state.snapshot.weatherOrbs.splice(i,1);changed=true}
      else if((i=state.snapshot.jammers.findIndex(j=>Number(j.tx)===tx&&Number(j.ty)===ty))>=0){result.removedKind='jammer';state.snapshot.jammers.splice(i,1);changed=true}
      else if((i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty))>=0){result.removedKind='plant';state.snapshot.plants.splice(i,1);changed=true}
      else if((i=state.snapshot.blocks.findIndex(key))>=0){result.removedKind='block';result.removedType=state.snapshot.blocks[i].t;state.snapshot.blocks.splice(i,1);changed=true}
      else{const bgKey=tx+','+ty;if(!state.snapshot.caveBgRemoved.includes(bgKey)){state.snapshot.caveBgRemoved.push(bgKey);changed=true;result.removedKind='background'}}
    }
    if(changed){state.revision++;state.updatedAt=Date.now();addWorldLog(loadDb(),world,session.player,'owner-break',result.removedKind||'object',{tx,ty,type:result.removedType||''})}
    return {accepted:changed,...result};
  }
  if(type==='break'){
    if(!canSessionEditTile(state,session,tx,ty))return {accepted:false};const i=state.snapshot.blocks.findIndex(key);if(i<0)return {accepted:false};const [removed]=state.snapshot.blocks.splice(i,1);if(removed.t==='bedrock'&&!ownerBreakActive(session)){state.snapshot.blocks.splice(i,0,removed);return {accepted:false}}changed=true;if(removed.t!=='bedrock')dropsAdded=addDrops(state,generateBreakDrops(removed.t,tx,ty));
  }else if(type==='place'){
    const bt=String(action.blockType||'').slice(0,32);if(!bt)return {accepted:false};if(bt==='bedrock'&&!(ownerBreakActive(session)&&String(session?.player?.role)==='Owner'))return {accepted:false};if(!canSessionEditTile(state,session,tx,ty))return {accepted:false};const existing=state.snapshot.blocks.find(key);if(existing||tileOccupiedByPlayer(world,tx,ty)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};state.snapshot.blocks.push({x:px,y:py,t:bt});changed=true;
  }else if(type==='lock-place'){
    if(!canSessionEditTile(state,session,tx,ty))return {accepted:false};
    const lt=String(action.lockType||'').slice(0,32);if(!['smallLock','bigLock','hugeLock','worldLock'].includes(lt))return {accepted:false};
    if(tileOccupiedByPlayer(world,tx,ty)||state.snapshot.blocks.some(key)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};
    if(lt==='worldLock'&&state.snapshot.locks.some(l=>isWorldOwnershipLockType(l?.type)))return {accepted:false};
    const placedType=(lt==='worldLock'&&String(session?.player?.role||'')==='Owner')?'ownerLock':lt,placedLock={tx,ty,type:placedType,owner:session?.player?.playerId||'',trusted:[],hitsTaken:0};state.snapshot.locks.push(placedLock);addWorldLog(loadDb(),world,session.player,'lock-place',placedType,{tx,ty});changed=true;result.lock=placedLock;
  }else if(type==='lock-remove'){
    const i=state.snapshot.locks.findIndex(l=>Number(l.tx)===tx&&Number(l.ty)===ty);if(i<0)return {accepted:false};const l=state.snapshot.locks[i];if(l.type==='ownerLock'&&!ownerBreakActive(session))return {accepted:false};if(String(l.owner||'')!==session?.player?.playerId&&!ownerBreakActive(session))return {accepted:false};state.snapshot.locks.splice(i,1);addWorldLog(loadDb(),world,session.player,'lock-remove',l.type||'lock',{tx,ty});changed=true;
  }else if(type==='door-place'){
    if(!canSessionEditTile(state,session,tx,ty))return {accepted:false};
    const dt=String(action.doorType||'');if(!['woodDoor','worldDoor'].includes(dt))return {accepted:false};
    if(tileOccupiedByPlayer(world,tx,ty)||state.snapshot.blocks.some(key)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};
    const d={id:randomId('DOOR'),tx,ty,type:dt,owner:session?.player?.playerId||'',doorId:'',targetWorld:'',targetId:'',open:false};state.snapshot.placedDoors.push(d);changed=true;result.door=d;
  }else if(type==='door-update'){
    const i=state.snapshot.placedDoors.findIndex(d=>Number(d.tx)===tx&&Number(d.ty)===ty);if(i<0)return {accepted:false};const d=state.snapshot.placedDoors[i];if(String(d.owner||'')!==session?.player?.playerId)return {accepted:false};if(d.type==='worldDoor'){d.doorId=String(action.doorId||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,18);d.targetWorld=cleanWorld(action.targetWorld);d.targetId=String(action.targetId||'').replace(/[^A-Za-z0-9_-]/g,'').slice(0,18)}else d.open=!!action.open;changed=true;result.door=d;
  }else if(type==='door-remove'){
    const i=state.snapshot.placedDoors.findIndex(d=>Number(d.tx)===tx&&Number(d.ty)===ty);if(i<0)return {accepted:false};const d=state.snapshot.placedDoors[i];if(String(d.owner||'')!==session?.player?.playerId&&!ownerBreakActive(session))return {accepted:false};state.snapshot.placedDoors.splice(i,1);changed=true;result.removedDoor=d;
  }else if(type==='jammer-place'){
    if(!canSessionEditTile(state,session,tx,ty))return {accepted:false};
    if(tileOccupiedByPlayer(world,tx,ty)||state.snapshot.blocks.some(key)||state.snapshot.jammers.some(j=>Number(j.tx)===tx&&Number(j.ty)===ty)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.weatherOrbs.some(o=>Number(o.tx)===tx&&Number(o.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};state.snapshot.jammers.push({tx,ty,type:'punch',owner:session?.player?.playerId||''});changed=true;
  }else if(type==='jammer-remove'){
    const i=state.snapshot.jammers.findIndex(j=>Number(j.tx)===tx&&Number(j.ty)===ty&&j.type==='punch');if(i<0)return {accepted:false};const j=state.snapshot.jammers[i];if(j.owner&&j.owner!==session?.player?.playerId)return {accepted:false};state.snapshot.jammers.splice(i,1);changed=true;
  }else if(type==='break-bg'){
    // Build 15: foreground always has punch priority. Background cannot be broken through a tree/block/object.
    if(state.snapshot.blocks.some(key)||state.snapshot.plants.some(p=>Number(p.tx)===tx&&Number(p.ty)===ty)||state.snapshot.locks.some(l=>Number(l.tx)===tx&&Number(l.ty)===ty)||state.snapshot.placedDoors.some(d=>Number(d.tx)===tx&&Number(d.ty)===ty))return {accepted:false};
    const k=tx+','+ty;if(state.snapshot.caveBgRemoved.includes(k))return {accepted:false};state.snapshot.caveBgRemoved.push(k);changed=true;
    // Cave Background always yields its farmable seed in Build 14.6.
    dropsAdded=addDrops(state,[makeDrop(tx,ty,'caveStoneSeed',1,'item',250,14)]);
  }else if(type==='plant-upsert'){
    const plant=sanitizePlant(action.plant,tx,ty);if(!plant)return {accepted:false};const i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty);if(i>=0)state.snapshot.plants[i]=plant;else state.snapshot.plants.push(plant);changed=true;
  }else if(type==='plant-remove'){
    const before=state.snapshot.plants.length;state.snapshot.plants=state.snapshot.plants.filter(p=>!(Number(p.tx)===tx&&Number(p.ty)===ty));changed=state.snapshot.plants.length!==before;
  }else if(type==='plant-hit'||type==='harvest'){
    const i=state.snapshot.plants.findIndex(p=>Number(p.tx)===tx&&Number(p.ty)===ty);if(i<0)return {accepted:false};const plant=state.snapshot.plants[i];
    if(plantMatureServer(plant)){state.snapshot.plants.splice(i,1);const harvest=generateHarvestDrops(plant,tx,ty);dropsAdded=addDrops(state,harvest.drops);changed=true;result.harvestAmount=harvest.amount;result.harvestItem=harvest.item;result.matureHarvest=true}
    else{const now=Date.now(),need=immaturePlantHits(plant);if(now-Number(plant.lastHitAt||0)>1200)plant.hitsTaken=0;plant.hitsTaken=Math.min(need,Number(plant.hitsTaken||0)+1);plant.lastHitAt=now;result.plantHits=plant.hitsTaken;result.plantHitsNeeded=need;if(plant.hitsTaken>=need){state.snapshot.plants.splice(i,1);changed=true;result.immatureBroken=true}else{changed=true}}
  }else return {accepted:false};
  if(changed){state.revision++;state.updatedAt=Date.now()}
  return {accepted:changed,dropsAdded,...result};
}

function sanitizePlayerSave(input){
  if(!input||typeof input!=='object')return null;
  const inv={};for(const [k,v] of Object.entries(input.inventory||{}).slice(0,500)){const n=Math.max(0,Math.min(200,Math.floor(Number(v||0))));if(n>0)inv[String(k).slice(0,40)]=n}
  const eq={};for(const [k,v] of Object.entries(input.equipped||{}).slice(0,50))eq[String(k).slice(0,32)]=v==null?null:String(v).slice(0,40);
  return {version:7,inventory:inv,equipped:eq,gems:Math.max(0,Math.min(999999999,Math.floor(Number(input.gems||0)))),backpackCapacity:Math.max(24,Math.min(5000,Math.floor(Number(input.backpackCapacity||24)))),backpackUpgrades:Math.max(0,Math.min(500,Math.floor(Number(input.backpackUpgrades||0)))),playerLevel:Math.max(1,Math.min(999,Math.floor(Number(input.playerLevel||1)))),playerXp:Math.max(0,Math.min(999999999,Math.floor(Number(input.playerXp||0)))),quickSlots:Array.isArray(input.quickSlots)?input.quickSlots.slice(0,3).map(v=>v?String(v).slice(0,40):null):[null,null,null],friends:Array.isArray(input.friends)?input.friends.slice(0,500).map(v=>String(v).slice(0,80)):[],blocked:Array.isArray(input.blocked)?input.blocked.slice(0,500).map(v=>String(v).slice(0,80)):[],ignored:Array.isArray(input.ignored)?input.ignored.slice(0,500).map(v=>String(v).slice(0,80)):[],savedAt:Date.now()}
}

async function api(req,res){
  if(req.method==='OPTIONS'){res.writeHead(204,{'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type, Authorization','Access-Control-Allow-Methods':'POST, OPTIONS'});return res.end()}
  if(req.method!=='POST')return send(res,405,{error:'METHOD_NOT_ALLOWED'});
  let body={};try{body=await readJson(req)}catch(_){return send(res,400,{error:'BAD_REQUEST'})}
  const db=loadDb();

  if(req.url==='/api/status')return send(res,200,{ok:true,build:'15.0.6',storage:storageMode,persistent:storageMode==='postgres'});
  if(req.url==='/api/guest'){
    const base=cleanName(body.name),guestId=cleanGuestId(body.guestId)||crypto.randomUUID(),playerId='G-'+guestId;let g=db.guests[playerId];if(!g){g={playerId,guestId,displayName:`${base}_#${guestSuffix(guestId)}`,playerSave:null,createdAt:Date.now()};db.guests[playerId]=g;saveDb(db)}const player={playerId,displayName:g.displayName,accountType:'guest',role:'Player'};if(isServerBanned(db,player.playerId))return send(res,403,{error:'SERVER_BANNED'});const t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:g.playerSave||null})
  }
  if(req.url==='/api/register'){
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),confirm=String(body.confirmPassword||''),email=cleanEmail(body.email);
    if(!/^[A-Za-z0-9]{3,24}$/.test(rawId))return send(res,400,{error:'BAD_ID'});
    if(pw.length<6||pw!==confirm||!email)return send(res,400,{error:pw!==confirm?'PASSWORD_MISMATCH':(!email?'BAD_EMAIL':'BAD_REQUEST')});
    if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});
    if(Object.values(db.accounts).some(a=>String(a.email||'').toLowerCase()===email))return send(res,409,{error:'EMAIL_EXISTS'});
    const account={id,username:rawId,playerId:'A-'+crypto.randomUUID(),displayName:rawId,email,role:(OWNER_ACCOUNT_ID&&id===OWNER_ACCOUNT_ID)?'Owner':'Player',pass:hashPassword(pw),playerSave:null,createdAt:Date.now()};db.accounts[id]=account;saveDb(db);
    const player={playerId:account.playerId,displayName:rawId,accountId:id,accountType:'account',role:roleForAccount(account)},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:null,testGrants:player.role==='Owner'?['alphaWing','pixoraHat']:[]})
  }
  if(req.url==='/api/login'){
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),account=db.accounts[id];
    if(!account)return send(res,404,{error:'ACCOUNT_NOT_FOUND'});
    if(!verifyPassword(pw,account.pass))return send(res,401,{error:'INVALID_CREDENTIALS'});if(roleForAccount(account)!=='Owner'&&isServerBanned(db,account.playerId))return send(res,403,{error:'SERVER_BANNED'});
    let changed=false;if(!account.username){account.username=String(account.displayName||account.id||rawId).replace(/_#\d{4}$/,'');changed=true}if(account.displayName!==account.username){account.displayName=account.username;changed=true}if(!('playerSave' in account)){account.playerSave=null;changed=true}if(!account.role){account.role=(OWNER_ACCOUNT_ID&&id===OWNER_ACCOUNT_ID)?'Owner':'Player';changed=true}if(changed){db.accounts[id]=account;saveDb(db)}
    const player={playerId:account.playerId,displayName:account.username,accountId:id,accountType:'account',role:roleForAccount(account)},t=createSession(player);return send(res,200,{token:t,player:playerPayload(player),playerSave:account.playerSave||null,testGrants:roleForAccount(account)==='Owner'?['alphaWing','pixoraHat']:[]})
  }

  const auth=requireSession(req,res);if(!auth)return;const {token:t,session}=auth;if(session.player.role!=='Owner'&&isServerBanned(db,session.player.playerId))return send(res,403,{error:'SERVER_BANNED'});
  if(req.url==='/api/guest/convert'){
    if(session.player.accountType!=='guest')return send(res,409,{error:'ALREADY_ACCOUNT'});
    const rawId=String(body.id||'').trim(),id=cleanId(rawId),pw=String(body.password||''),confirm=String(body.confirmPassword||''),email=cleanEmail(body.email);
    if(!/^[A-Za-z0-9]{3,24}$/.test(rawId))return send(res,400,{error:'BAD_ID'});if(pw.length<6||pw!==confirm||!email)return send(res,400,{error:pw!==confirm?'PASSWORD_MISMATCH':(!email?'BAD_EMAIL':'BAD_REQUEST')});
    if(db.accounts[id])return send(res,409,{error:'ACCOUNT_EXISTS'});if(Object.values(db.accounts).some(a=>String(a.email||'').toLowerCase()===email))return send(res,409,{error:'EMAIL_EXISTS'});
    const save=sanitizePlayerSave(body.save)||getPlayerSave(db,session.player.playerId)||null,account={id,username:rawId,playerId:session.player.playerId,displayName:rawId,email,role:(OWNER_ACCOUNT_ID&&id===OWNER_ACCOUNT_ID)?'Owner':'Player',pass:hashPassword(pw),playerSave:save,createdAt:Date.now(),convertedGuest:true};db.accounts[id]=account;delete db.guests[session.player.playerId];
    session.player={playerId:account.playerId,displayName:rawId,accountId:id,accountType:'account',role:roleForAccount(account)};db.sessions[sessionKey(t)]={player:playerPayload(session.player),createdAt:session.createdAt||Date.now(),lastSeen:Date.now()};activeAccountTokens.set(id,t);saveDb(db);return send(res,200,{token:t,player:playerPayload(session.player),playerSave:save})
  }
  if(req.url==='/api/player/profile'){
    const targetId=String(body.playerId||session.player.playerId).slice(0,80);let target=sessionByPlayerId(targetId)?.session?.player||null;const acc=accountByPlayerId(db,targetId);if(!target&&acc)target={playerId:acc.playerId,displayName:acc.username||acc.displayName,accountId:acc.id,accountType:'account',role:roleForAccount(acc)};
    if(!target){const g=guestByPlayerId(db,targetId);if(g)target={playerId:g.playerId,displayName:g.displayName,accountType:'guest',role:'Player'}}if(!target)return send(res,404,{error:'PLAYER_NOT_FOUND'});const save=getPlayerSave(db,targetId);return send(res,200,{ok:true,profile:{...playerPayload(target),level:Math.max(1,Number(save?.playerLevel||1)),xp:Math.max(0,Number(save?.playerXp||0)),equipped:save?.equipped||{}}})
  }
  if(req.url==='/api/report'){
    const targetPlayerId=String(body.targetPlayerId||'').slice(0,80),reason=String(body.reason||'').trim().slice(0,240);if(!targetPlayerId||targetPlayerId===session.player.playerId)return send(res,400,{error:'BAD_REQUEST'});db.reports.push({id:randomId('CASE'),from:session.player.playerId,target:targetPlayerId,reason:reason||'Player report',at:Date.now(),world:cleanWorld(body.world)});db.reports=db.reports.slice(-2000);saveDb(db);return send(res,200,{ok:true})
  }
  if(req.url==='/api/mod/reports'){
    if(!['Moderator','Admin','Owner'].includes(String(session.player.role||'Player')))return send(res,403,{error:'MODERATOR_REQUIRED'});
    return send(res,200,{ok:true,reports:(db.reports||[]).slice(-100).reverse()})
  }
  if(req.url==='/api/mod/role'){
    if((session.player.role||'Player')!=='Owner')return send(res,403,{error:'OWNER_REQUIRED'});const target=accountByPlayerId(db,String(body.targetPlayerId||''));const role=String(body.role||'Player');if(!target||!['Player','Moderator','Admin'].includes(role))return send(res,400,{error:'BAD_REQUEST'});target.role=role;addAudit(db,session.player,'role',target.playerId,{role});saveDb(db);const live=sessionByPlayerId(target.playerId)?.session;if(live)live.player.role=role;return send(res,200,{ok:true,playerId:target.playerId,role})
  }
  if(req.url==='/api/mod/ban'){
    if((session.player.role||'Player')!=='Owner')return send(res,403,{error:'OWNER_REQUIRED'});const targetId=String(body.targetPlayerId||'').slice(0,80),known=resolveAnyKnownPlayer(db,targetId)||sessionByPlayerId(targetId)?.session?.player;if(!known)return send(res,404,{error:'PLAYER_NOT_FOUND'});const targetRole=String(known.role||'Player');if(targetRole==='Owner'||String(known.playerId)===session.player.playerId)return send(res,403,{error:'TARGET_PROTECTED'});const reason=String(body.reason||'Owner wrench ban').trim().slice(0,160)||'Owner wrench ban';db.serverBans[known.playerId]={at:Date.now(),by:session.player.playerId,byName:session.player.displayName,targetName:known.displayName||known.playerId,reason};addAudit(db,session.player,'server-ban',known.playerId,{reason,source:'wrench'});moderationAnnounce(db,session.player,`${known.displayName||known.playerId} was BANNED • ${reason}`);saveDb(db);cancelTradeFor(known.playerId,'BANNED');removePresence(known.playerId);queueEvent(known.playerId,{type:'server-ban',reason});return send(res,200,{ok:true,playerId:known.playerId})
  }
  if(req.url==='/api/friends/list'){
    const pid=session.player.playerId,fids=[...friendSet(db,pid)],incoming=(db.friendRequests||[]).filter(r=>r.status==='pending'&&r.to===pid),outgoing=(db.friendRequests||[]).filter(r=>r.status==='pending'&&r.from===pid);
    const info=id=>({playerId:id,name:knownPlayerLabel(db,id),online:!!sessionByPlayerId(id)});
    return send(res,200,{ok:true,friends:fids.map(info),incoming:incoming.map(r=>({...r,fromName:knownPlayerLabel(db,r.from)})),outgoing:outgoing.map(r=>({...r,toName:knownPlayerLabel(db,r.to)}))})
  }
  if(req.url==='/api/friends/request'){
    const from=session.player.playerId,to=String(body.targetPlayerId||'').slice(0,80);if(!to||to===from||!saveRecordByPlayerId(db,to))return send(res,400,{error:'BAD_REQUEST'});if(areFriends(db,from,to))return send(res,409,{error:'ALREADY_FRIENDS'});if((db.friendRequests||[]).some(r=>r.status==='pending'&&((r.from===from&&r.to===to)||(r.from===to&&r.to===from))))return send(res,409,{error:'FRIEND_REQUEST_PENDING'});const reqRow={id:randomId('FR'),from,to,status:'pending',at:Date.now()};db.friendRequests.push(reqRow);db.friendRequests=db.friendRequests.slice(-3000);saveDb(db);queueEvent(to,{type:'friend-request',requestId:reqRow.id,from,name:session.player.displayName});return send(res,200,{ok:true,request:reqRow})
  }
  if(req.url==='/api/friends/respond'){
    const id=String(body.requestId||''),accept=!!body.accept,r=(db.friendRequests||[]).find(x=>x.id===id&&x.to===session.player.playerId&&x.status==='pending');if(!r)return send(res,404,{error:'FRIEND_REQUEST_NOT_FOUND'});r.status=accept?'accepted':'declined';r.respondedAt=Date.now();if(accept){const a=friendSet(db,r.from),b=friendSet(db,r.to);a.add(r.to);b.add(r.from);db.friends[r.from]=[...a].slice(0,500);db.friends[r.to]=[...b].slice(0,500);syncFriendSave(db,r.from);syncFriendSave(db,r.to);queueEvent(r.from,{type:'friend-accepted',playerId:r.to,name:knownPlayerLabel(db,r.to)});queueEvent(r.to,{type:'friend-accepted',playerId:r.from,name:knownPlayerLabel(db,r.from)})}saveDb(db);return send(res,200,{ok:true,accepted:accept})
  }
  if(req.url==='/api/friends/cancel'){
    const id=String(body.requestId||''),r=(db.friendRequests||[]).find(x=>x.id===id&&x.from===session.player.playerId&&x.status==='pending');if(!r)return send(res,404,{error:'FRIEND_REQUEST_NOT_FOUND'});r.status='cancelled';r.respondedAt=Date.now();saveDb(db);return send(res,200,{ok:true})
  }
  if(req.url==='/api/friends/remove'){
    const a=session.player.playerId,b=String(body.targetPlayerId||'').slice(0,80);if(!b)return send(res,400,{error:'BAD_REQUEST'});const sa=friendSet(db,a),sb=friendSet(db,b);sa.delete(b);sb.delete(a);db.friends[a]=[...sa];db.friends[b]=[...sb];syncFriendSave(db,a);syncFriendSave(db,b);saveDb(db);queueEvent(b,{type:'friend-removed',playerId:a});return send(res,200,{ok:true})
  }
  if(req.url==='/api/trade/request'){
    const targetId=String(body.targetPlayerId||'').slice(0,80),targetSession=sessionByPlayerId(targetId)?.session;if(!targetSession||targetId===session.player.playerId)return send(res,400,{error:'PLAYER_NOT_AVAILABLE'});if(tradeByPlayer.has(session.player.playerId)||tradeByPlayer.has(targetId))return send(res,409,{error:'TRADE_BUSY'});
    const id=randomId('T'),tr={id,a:session.player.playerId,b:targetId,status:'pending',offers:{[session.player.playerId]:{},[targetId]:{}},confirmed:{[session.player.playerId]:false,[targetId]:false},finalConfirmed:{[session.player.playerId]:false,[targetId]:false},updatedAt:Date.now()};trades.set(id,tr);tradeByPlayer.set(tr.a,id);tradeByPlayer.set(tr.b,id);queueEvent(targetId,{type:'trade-request',tradeId:id,from:tr.a,name:session.player.displayName});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/accept'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||tr.b!==session.player.playerId||tr.status!=='pending')return send(res,409,{error:'TRADE_INVALID'});tr.status='active';tr.updatedAt=Date.now();queueEvent(tr.a,{type:'trade-open',tradeId:id});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/state'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||![tr.a,tr.b].includes(session.player.playerId))return send(res,404,{error:'TRADE_NOT_FOUND'});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/offer'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||tr.status!=='active'||![tr.a,tr.b].includes(session.player.playerId))return send(res,409,{error:'TRADE_INVALID'});const currentSave=getPlayerSave(db,session.player.playerId),inv=currentSave?.inventory||{};if(!currentSave)return send(res,409,{error:'SAVE_REQUIRED'});const offer={};for(const [item,raw] of Object.entries(body.offer||{}).slice(0,8)){const n=Math.max(0,Math.min(200,Math.floor(Number(raw||0))));if(!n||item==='spliceBook'||item==='bedrock'||(IOTM_TESTING&&item==='alphaWing')||item==='pixoraHat')continue;if(Number(inv[item]||0)<n)return send(res,409,{error:'ITEM_CHANGED'});offer[String(item).slice(0,40)]=n}tr.offers[session.player.playerId]=offer;tr.confirmed[tr.a]=tr.confirmed[tr.b]=false;tr.finalConfirmed[tr.a]=tr.finalConfirmed[tr.b]=false;tr.status='active';tr.updatedAt=Date.now();queueEvent(tr.a,{type:'trade-updated',tradeId:id});queueEvent(tr.b,{type:'trade-updated',tradeId:id});return send(res,200,{ok:true,trade:publicTrade(tr,db)})
  }
  if(req.url==='/api/trade/confirm'){
    const id=String(body.tradeId||tradeByPlayer.get(session.player.playerId)||''),tr=trades.get(id);if(!tr||![tr.a,tr.b].includes(session.player.playerId))return send(res,409,{error:'TRADE_INVALID'});const pid=session.player.playerId;
    if(tr.status==='active'){tr.confirmed[pid]=true;if(tr.confirmed[tr.a]&&tr.confirmed[tr.b]){tr.status='locked';tr.finalConfirmed[tr.a]=tr.finalConfirmed[tr.b]=false}tr.updatedAt=Date.now();queueEvent(tr.a,{type:'trade-updated',tradeId:id});queueEvent(tr.b,{type:'trade-updated',tradeId:id});return send(res,200,{ok:true,trade:publicTrade(tr,db)})}
    if(tr.status!=='locked')return send(res,409,{error:'TRADE_INVALID'});tr.finalConfirmed[pid]=true;if(!(tr.finalConfirmed[tr.a]&&tr.finalConfirmed[tr.b])){tr.updatedAt=Date.now();return send(res,200,{ok:true,trade:publicTrade(tr,db)})}
    const aSave=getPlayerSave(db,tr.a),bSave=getPlayerSave(db,tr.b);if(!aSave||!bSave)return send(res,409,{error:'SAVE_REQUIRED'});
    const a0={...(aSave.inventory||{})},b0={...(bSave.inventory||{})},ao=tr.offers[tr.a]||{},bo=tr.offers[tr.b]||{};
    const enough=(inv,offer)=>Object.entries(offer).every(([item,n])=>item!=='spliceBook'&&Number(inv[item]||0)>=Number(n||0));
    if(!enough(a0,ao)||!enough(b0,bo))return send(res,409,{error:'TRADE_INVENTORY_CHANGED'});
    const ai={...a0},bi={...b0};
    for(const [item,n0] of Object.entries(ao)){const n=Number(n0||0);ai[item]=Number(ai[item]||0)-n;bi[item]=Number(bi[item]||0)+n}
    for(const [item,n0] of Object.entries(bo)){const n=Number(n0||0);bi[item]=Number(bi[item]||0)-n;ai[item]=Number(ai[item]||0)+n}
    if(Object.values(ai).some(v=>Number(v)<0||Number(v)>200)||Object.values(bi).some(v=>Number(v)<0||Number(v)>200))return send(res,409,{error:'TRADE_INVENTORY_CHANGED'});
    aSave.inventory=ai;bSave.inventory=bi;aSave.savedAt=bSave.savedAt=Date.now();setPlayerSave(db,tr.a,aSave);setPlayerSave(db,tr.b,bSave);db.tradeHistory.push({id:tr.id,at:Date.now(),a:tr.a,b:tr.b,aOffer:{...ao},bOffer:{...bo}});db.tradeHistory=db.tradeHistory.slice(-5000);saveDb(db);tr.status='done';tr.updatedAt=Date.now();tradeByPlayer.delete(tr.a);tradeByPlayer.delete(tr.b);queueEvent(tr.a,{type:'trade-complete',tradeId:id,playerSave:aSave});queueEvent(tr.b,{type:'trade-complete',tradeId:id,playerSave:bSave});return send(res,200,{ok:true,trade:publicTrade(tr,db),playerSave:pid===tr.a?aSave:bSave})
  }
  if(req.url==='/api/trade/cancel'){cancelTradeFor(session.player.playerId,'CANCELLED');return send(res,200,{ok:true})}
  if(req.url==='/api/session'){
    const sk=sessionKey(t);if(db.sessions?.[sk]){db.sessions[sk].lastSeen=Date.now();saveDb(db)}
    return send(res,200,{token:t,player:playerPayload(session.player),playerSave:getPlayerSave(db,session.player.playerId),storage:storageMode,testGrants:session.player.role==='Owner'?['alphaWing','pixoraHat']:[],gemEvent:db.gemEvent||{multiplier:1,until:0},serverRestart:publicRestartPlan(),ownerBreak:!!session.player.ownerBreak})
  }
  if(req.url==='/api/player/save'){
    const save=sanitizePlayerSave(body.save);if(!save)return send(res,400,{error:'BAD_SAVE'});if(session.player.role!=='Owner'){const grants=new Set(Array.isArray(db.ownerGrantedItems?.[session.player.playerId])?db.ownerGrantedItems[session.player.playerId]:[]);if(!grants.has('bedrock'))delete save.inventory.bedrock;if(IOTM_TESTING){if(!grants.has('alphaWing')){delete save.inventory.alphaWing;if(save.equipped?.back==='alphaWing')save.equipped.back=null}if(!grants.has('pixoraHat')){delete save.inventory.pixoraHat;if(save.equipped?.hat==='pixoraHat')save.equipped.hat=null;if(save.equipped?.hair==='pixoraHat')save.equipped.hair=null}}}if(!setPlayerSave(db,session.player.playerId,save))return send(res,404,{error:'PLAYER_NOT_FOUND'});saveDb(db);return send(res,200,{ok:true,savedAt:save.savedAt})
  }
  if(req.url==='/api/player/load'){
    return send(res,200,{ok:true,playerSave:getPlayerSave(db,session.player.playerId)})
  }
  if(req.url==='/api/logout'){
    cancelTradeFor(session.player.playerId,'DISCONNECTED');removePresence(session.player.playerId);sessions.delete(t);delete db.sessions[sessionKey(t)];if(session.player.accountType==='account'&&activeAccountTokens.get(session.player.accountId)===t)activeAccountTokens.delete(session.player.accountId);saveDb(db);return send(res,200,{ok:true})
  }
  if(req.url==='/api/world/join'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});if(db.hellJail[session.player.playerId]&&world!==HELL_WORLD)return send(res,403,{error:'HELL_LOCKED',forceWorld:HELL_WORLD});if(db.bannedWorlds?.[world]&&!hasRole(session.player.role,'Moderator'))return send(res,403,{error:'WORLD_CLOSED',reason:db.bannedWorlds[world].reason||''});const state=getOrCreateWorldState(world,body.worldSnapshot),pixoraKingdomApplied=ensurePixoraKingdom(world,state),worldRecovered=maybeRecoverFreshWorldFromClient(world,state,body.worldSnapshot,session.player.playerId);if(Array.isArray(state.snapshot.worldBans)&&state.snapshot.worldBans.includes(session.player.playerId))return send(res,403,{error:'WORLD_BANNED'});for(const [w,room] of worldPresence){if(w!==world){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(w)}}const cap=canJoinWorld(world,session.player.playerId);if(!cap.ok)return send(res,409,{error:cap.error,maxWorld:MAX_WORLD_PLAYERS,maxServer:MAX_SERVER_PLAYERS});updatePresence(world,session.player,body);return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId,session.player.role),events:consumeEvents(session.player.playerId),revision:state.revision,worldSnapshot:state.snapshot,chat:(state.chat||[]).slice(-30),storage:storageMode,worldRole:worldMembership(world,session.player.playerId),gemEvent:db.gemEvent||{multiplier:1,until:0},serverRestart:publicRestartPlan(),ownerBreak:!!session.player.ownerBreak,worldRecovered,pixoraKingdomApplied})
  }
  if(req.url==='/api/world/state'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});if(db.bannedWorlds?.[world]&&!hasRole(session.player.role,'Moderator'))return send(res,403,{error:'WORLD_CLOSED',reason:db.bannedWorlds[world].reason||''});const state=getOrCreateWorldState(world,body.worldSnapshot);if(Array.isArray(state.snapshot.worldBans)&&state.snapshot.worldBans.includes(session.player.playerId))return send(res,403,{error:'WORLD_BANNED'});const cap=canJoinWorld(world,session.player.playerId);if(!cap.ok)return send(res,409,{error:cap.error,maxWorld:MAX_WORLD_PLAYERS,maxServer:MAX_SERVER_PLAYERS});updatePresence(world,session.player,body);const known=Math.max(0,Number(body.knownRevision||0));return send(res,200,{ok:true,world,players:roomView(world,session.player.playerId,session.player.role),events:consumeEvents(session.player.playerId),revision:state.revision,...(known<state.revision?{worldSnapshot:state.snapshot}:{}),chat:(state.chat||[]).slice(-30),serverTime:Date.now(),worldRole:worldMembership(world,session.player.playerId),gemEvent:db.gemEvent||{multiplier:1,until:0},serverRestart:publicRestartPlan(),ownerBreak:!!session.player.ownerBreak})
  }
  if(req.url==='/api/world/action'){
    const world=cleanWorld(body.world);if(!world)return send(res,400,{error:'BAD_WORLD'});if(db.hellJail[session.player.playerId]&&world!==HELL_WORLD)return send(res,403,{error:'HELL_LOCKED',forceWorld:HELL_WORLD});if(db.bannedWorlds?.[world]&&!hasRole(session.player.role,'Moderator'))return send(res,403,{error:'WORLD_CLOSED'});const state=getOrCreateWorldState(world,null),result=applyWorldAction(state,body.action,session,world);if(result.accepted&&(result.knockback!==true&&result.blocked!==true))persistWorld(world,state);return send(res,result.accepted?200:409,{ok:result.accepted,world,revision:state.revision,actionId:String(body.actionId||'').slice(0,80),...(result.accepted?result:{error:'ACTION_REJECTED'})})
  }
  if(req.url==='/api/world/chat'){
    const world=cleanWorld(body.world),raw=String(body.text||'').trim().replace(/\s+/g,' ');if(raw.length>180)return send(res,400,{error:'CHAT_TOO_LONG'});const text=raw.slice(0,180);if(!world||!text)return send(res,400,{error:'BAD_REQUEST'});if(db.hellJail[session.player.playerId]&&world!==HELL_WORLD)return send(res,403,{error:'HELL_LOCKED',forceWorld:HELL_WORLD});if(db.bannedWorlds?.[world]&&!hasRole(session.player.role,'Moderator'))return send(res,403,{error:'WORLD_CLOSED'});const state=getOrCreateWorldState(world,null);
    if(text.startsWith('/')){
      const command=runChatCommand({raw:text,world,session,db});
      if(command.ok&&command.history){const m={id:randomId('SYS'),playerId:'',name:String(command.historyName||'SYSTEM').slice(0,32),text:String(command.message||'').slice(0,700),at:Date.now(),system:true};state.chat=(state.chat||[]).concat(m).slice(-30);persistWorld(world,state)}
      return send(res,command.ok?200:403,{ok:command.ok,chat:state.chat||[],command,...(!command.ok?{error:'COMMAND_DENIED'}:{})})
    }
    const mute=isMuted(db,session.player.playerId);if(mute)return send(res,403,{error:'MUTED',until:mute.until||0,reason:mute.reason||''});
    const slow=Math.max(0,Number(db.worldSlowmode?.[world]||0));if(slow&&!hasRole(session.player.role,'Moderator')){const key=world+'|'+session.player.playerId,last=Number(chatCooldowns.get(key)||0),wait=slow*1000-(Date.now()-last);if(wait>0)return send(res,429,{error:'SLOWMODE',waitMs:wait});chatCooldowns.set(key,Date.now())}
    const msg={id:randomId('C'),playerId:session.player.playerId,name:session.player.displayName,text:text.slice(0,120),at:Date.now()};state.chat=(state.chat||[]).concat(msg).slice(-30);persistWorld(world,state);return send(res,200,{ok:true,chat:state.chat})
  }
  if(req.url==='/api/world/leave'){
    const world=cleanWorld(body.world),room=worldPresence.get(world);if(room){room.delete(session.player.playerId);if(!room.size)worldPresence.delete(world)}return send(res,200,{ok:true})
  }
  return send(res,404,{error:'NOT_FOUND'})
}

function staticFile(req,res){
  let url=req.url.split('?')[0];if(url==='/')url='/index.html';const file=path.normalize(path.join(ROOT,url));if(!file.startsWith(ROOT))return send(res,403,{error:'FORBIDDEN'});
  fs.readFile(file,(err,data)=>{if(err){res.writeHead(200,{'Content-Type':'text/plain; charset=utf-8'});return res.end(`Pixora Server Build 15.0.6 is live | storage=${storageMode}`)}const ext=path.extname(file),type=ext==='.html'?'text/html; charset=utf-8':ext==='.js'?'application/javascript':'application/octet-stream';res.writeHead(200,{'Content-Type':type});res.end(data)})
}
const server=http.createServer((req,res)=>{if(req.url.startsWith('/api/'))return api(req,res);return staticFile(req,res)});

async function shutdown(){try{flushAllWorldStates()}catch(_){}try{await persistQueue}catch(_){}try{await pgPool?.end()}catch(_){}process.exit(0)}
process.on('SIGTERM',shutdown);process.on('SIGINT',shutdown);
initStorage().then(()=>server.listen(PORT,()=>console.log(`Pixora Build 15.0.6 server running on port ${PORT}`))).catch(e=>{console.error(e);process.exit(1)});
