import http from 'node:http';
import crypto from 'node:crypto';
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {isIP} from 'node:net';
import {createInterface} from 'node:readline/promises';

export const VERSION='0.1.0';
const ROOT=path.dirname(fileURLToPath(import.meta.url));
const SOURCE_ORIGIN='https://phim.nguonc.com';
const UA='Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36';
const TIMEOUT=8000, JSON_LIMIT=400000, PLAYLIST_LIMIT=2000000, SAMPLE_LIMIT=4096;
export class ProbeError extends Error { constructor(code){super(code);this.code=code;} }
const fail=code=>{throw new ProbeError(code)};
const ms=()=>performance.now();
const elapsed=t=>Math.round(ms()-t);
const host=u=>new URL(u).hostname;
export function validateTarget(value){
  let u;try{u=new URL(value)}catch{fail('invalid_url')}
  const h=u.hostname.toLowerCase();
  if(u.protocol!=='https:'||u.username||u.password||u.hash||(u.port&&u.port!=='443')||!h.includes('.')||isIP(h)||h.startsWith('[')||/(^|\.)(localhost|local|internal|test|invalid)$/.test(h))fail('unsafe_target');
  return u;
}
export function validateEmbed(value){
  const u=validateTarget(value);
  if(!/(^|\.)streamc\.xyz$/.test(u.hostname)||u.pathname!=='/embed.php'||!/^[a-f0-9]{32}$/i.test(u.searchParams.get('hash')||''))fail('invalid_embed');
  return u;
}
export const payload=()=>({action:'bootstrap',referrer:SOURCE_ORIGIN+'/',frame_origins:[SOURCE_ORIGIN],request_grant:true,playlist_format:'hls',pretty_url:true,path_chunks:true,bootstrap_format:'aesgcm-v1'});
export function mediaHeaders(embed){const u=validateEmbed(embed);return {'User-Agent':UA,Referer:u.href,Origin:u.origin,Accept:'*/*'};}
function errorCode(e){return e instanceof ProbeError?e.code:e?.name==='AbortError'||e?.name==='TimeoutError'?'timeout':String(e?.cause?.code||e?.code||'network_error').replace(/[^A-Za-z0-9_-]/g,'').slice(0,80);}

// Signed URLs and upstream response bodies never enter public logs/reports.
export async function requestBytes(url,{fetchImpl=fetch,timeoutMs=TIMEOUT,limit=JSON_LIMIT,sample=false,method='GET',headers={},body}={}){
  validateTarget(url);const start=ms(),controller=new AbortController();
  const timer=setTimeout(()=>controller.abort(),timeoutMs);
  let reader;
  try{
    const response=await fetchImpl(url,{method,headers,body,signal:controller.signal,redirect:'manual'});
    if(response.status>=300&&response.status<400)fail('redirect_requires_review');
    const result={status:response.status,contentType:response.headers.get('content-type')||'',contentRange:response.headers.get('content-range')||null,server:response.headers.get('server')||null,bytes:0};
    if(!response.ok){await response.body?.cancel();return {...result,ms:elapsed(start),data:Buffer.alloc(0)};}
    reader=response.body?.getReader();const chunks=[];
    if(reader)while(true){
      const part=await reader.read();if(part.done)break;
      const available=limit-result.bytes;
      if(part.value.byteLength>available){
        if(!sample)fail('body_too_large');
        chunks.push(Buffer.from(part.value.subarray(0,available)));result.bytes=limit;await reader.cancel();break;
      }
      chunks.push(Buffer.from(part.value));result.bytes+=part.value.byteLength;
      if(sample&&result.bytes>=limit){await reader.cancel();break;}
    }
    return {...result,ms:elapsed(start),data:Buffer.concat(chunks)};
  }catch(e){throw new ProbeError(errorCode(e))}finally{clearTimeout(timer);if(reader)await reader.cancel().catch(()=>{});}
}
function safeStep(r){return {status:r.status,ms:r.ms,bytes:r.bytes,contentType:r.contentType,contentRange:r.contentRange,server:r.server};}
function requireOk(r,stage){if(r.status<200||r.status>=300)fail(stage+'_http_'+r.status);}
export function expiresMilliseconds(value){
  if(value===undefined||value===null||value==='')return null;
  const n=Number(value);if(Number.isFinite(n)&&n>0)return n<1e12?n*1000:n;
  const t=Date.parse(value);return Number.isFinite(t)?t:null;
}
export function openEnvelope(input,embedUrl,now=Date.now()){
  const embed=validateEmbed(embedUrl),envelope=input?.format==='aesgcm-v1'?input:input?.envelope;
  if(input?.turnstileEnabled||input?.issue==='turnstile_response')fail('turnstile_required');
  if(envelope?.format!=='aesgcm-v1'||!/^[a-f0-9]{24}$/i.test(envelope.iv||'')||typeof envelope.data!=='string'||envelope.data.length>JSON_LIMIT||!/^[A-Za-z0-9+/]+={0,2}$/.test(envelope.data)||envelope.data.length%4)fail('invalid_envelope');
  const context=Buffer.from('stream-bootstrap-v1\n'+embedUrl),key=crypto.createHash('sha256').update(context).digest(),data=Buffer.from(envelope.data,'base64');
  if(data.length<=16)fail('invalid_ciphertext');
  let opened;try{const decipher=crypto.createDecipheriv('aes-256-gcm',key,Buffer.from(envelope.iv,'hex'));decipher.setAAD(context);decipher.setAuthTag(data.subarray(-16));opened=JSON.parse(Buffer.concat([decipher.update(data.subarray(0,-16)),decipher.final()]).toString('utf8'));}catch{fail('envelope_auth_or_json_failed')}
  if(opened?.turnstileEnabled||opened?.issue==='turnstile_response')fail('turnstile_required');
  if(opened?.api!==embedUrl||!/^[a-f0-9]{32}$/i.test(opened?.video||''))fail('bootstrap_identity_mismatch');
  if(String(opened?.preissued?.playlistFormat||'hls').toLowerCase()!=='hls')fail('unsupported_playlist_format');
  const u=validateTarget(opened?.preissued?.playlist);
  if(u.origin!==embed.origin)fail('playlist_origin_mismatch');
  const expiresAt=expiresMilliseconds(opened.preissued.expiresAt);
  if(expiresAt!==null&&expiresAt<=now+10000)fail('grant_expired_or_too_short');
  return {embedUrl,playlistUrl:u.href,expiresAt,issuedAt:now};
}
export async function bootstrap(embedUrl,steps,options={}){
  validateEmbed(embedUrl);
  const post=async()=>{
    const t=ms();let r;
    try{r=await requestBytes(embedUrl,{...options,method:'POST',headers:{...mediaHeaders(embedUrl),'Content-Type':'application/json','Accept-Language':'vi-VN,vi;q=0.9,en-US;q=0.8,en;q=0.7'},body:JSON.stringify(payload())});steps.push({stage:'bootstrap_post',...safeStep(r)});requireOk(r,'bootstrap');
      let data;try{data=JSON.parse(r.data.toString('utf8'))}catch{fail('bootstrap_not_json')}
      return data;
    }catch(e){if(!r)steps.push({stage:'bootstrap_post',ms:elapsed(t),error:errorCode(e)});throw e;}
  };
  let envelope;
  try{envelope=await post()}catch(e){
    if(errorCode(e)==='turnstile_required')throw e;
    const t=ms();let r;
    try{r=await requestBytes(embedUrl,{...options,headers:{'User-Agent':UA,Referer:SOURCE_ORIGIN+'/',Accept:'text/html'}});steps.push({stage:'embed_get_fallback',...safeStep(r)});requireOk(r,'embed');
      if(/cf-turnstile|challenges\.cloudflare\.com|turnstileEnabled\s*[:=]\s*true/i.test(r.data.toString('utf8')))fail('turnstile_required');
    }catch(getError){if(!r)steps.push({stage:'embed_get_fallback',ms:elapsed(t),error:errorCode(getError)});throw getError;}
    envelope=await post();
  }
  const t=ms();try{const grant=openEnvelope(envelope,embedUrl);steps.push({stage:'decrypt',ms:elapsed(t),status:'PASS',expiresAt:grant.expiresAt?new Date(grant.expiresAt).toISOString():null});return grant;}catch(e){steps.push({stage:'decrypt',ms:elapsed(t),status:'FAIL',error:errorCode(e)});throw e;}
}
export function parsePlaylist(text,baseUrl){
  const clean=text.replace(/^\uFEFF/,'');if(!/^#EXTM3U(?:\r?\n|$)/.test(clean))fail('playlist_not_hls');
  if(/#ENC-AESGCM|#EXT-X-B65/.test(clean))fail('encrypted_playlist_not_plain_hls');
  const lines=clean.split(/\r?\n/).map(x=>x.trim()),variants=[];
  for(let i=0;i<lines.length;i++)if(lines[i].startsWith('#EXT-X-STREAM-INF:')){
    const bw=Number(/(?:[:,])BANDWIDTH=(\d+)/.exec(lines[i])?.[1]||0);
    let j=i+1;while(j<lines.length&&(!lines[j]||lines[j].startsWith('#')))j++;
    if(j>=lines.length)fail('master_missing_variant');
    variants.push({bandwidth:bw,url:validateTarget(new URL(lines[j],baseUrl).href).href});
  }
  if(variants.length){variants.sort((a,b)=>b.bandwidth-a.bandwidth);return {kind:'master',variant:variants[0].url,variantCount:variants.length};}
  let keyUrl=null,keyMethod=null,byteRange=null,pending=false;
  for(const line of lines){
    if(line.startsWith('#EXT-X-KEY:')){keyMethod=/METHOD=([^,]+)/.exec(line)?.[1]||null;keyUrl=keyMethod==='NONE'?null:/URI="([^"]+)"/.exec(line)?.[1]||null;if(keyMethod!=='NONE'&&!keyUrl)fail('key_uri_missing');}
    if(line.startsWith('#EXT-X-BYTERANGE:'))byteRange=line.slice(17);
    if(line.startsWith('#EXTINF:'))pending=true;
    if(pending&&line&&!line.startsWith('#')){
      const segmentUrl=validateTarget(new URL(line,baseUrl).href).href;
      let rangeStart=0,rangeEnd=SAMPLE_LIMIT-1;
      if(byteRange){const m=/^(\d+)(?:@(\d+))?$/.exec(byteRange);if(!m||Number(m[1])<1)fail('invalid_byterange');rangeStart=Number(m[2]||0);rangeEnd=rangeStart+Math.min(Number(m[1]),SAMPLE_LIMIT)-1;}
      return {kind:'media',segmentUrl,keyUrl:keyUrl?validateTarget(new URL(keyUrl,baseUrl).href).href:null,keyMethod,range:'bytes='+rangeStart+'-'+rangeEnd,segmentCount:lines.filter(x=>x.startsWith('#EXTINF:')).length,endlist:lines.includes('#EXT-X-ENDLIST')};
    }
  }
  fail('playlist_missing_segments');
}
export async function inspectGrant(grant,steps,options={}){
  if(grant.expiresAt!==null&&grant.expiresAt!==undefined&&grant.expiresAt<=Date.now()+10000)fail('grant_expired_or_too_short');
  const headers=mediaHeaders(grant.embedUrl);let current=grant.playlistUrl,media=null;
  for(let depth=0;depth<4;depth++){
    const t=ms();let r;
    try{r=await requestBytes(current,{...options,headers,limit:PLAYLIST_LIMIT});steps.push({stage:depth?'playlist_child':'playlist',host:host(current),...safeStep(r)});requireOk(r,'playlist');media=parsePlaylist(r.data.toString('utf8'),current);}catch(e){if(!r)steps.push({stage:depth?'playlist_child':'playlist',host:host(current),ms:elapsed(t),error:errorCode(e)});throw e;}
    if(media.kind==='media')break;
    if(depth===3)fail('master_depth_exceeded');current=media.variant;
  }
  const info={segmentCount:media.segmentCount,endlist:media.endlist,segmentHost:host(media.segmentUrl),keyMethod:media.keyMethod||'NONE'};
  if(media.keyUrl){const r=await requestBytes(media.keyUrl,{...options,headers,limit:1024});steps.push({stage:'hls_key',host:host(media.keyUrl),...safeStep(r)});requireOk(r,'key');if(media.keyMethod==='AES-128'&&r.bytes!==16)fail('invalid_aes128_key_length');}
  const r=await requestBytes(media.segmentUrl,{...options,headers:{...headers,Range:media.range},limit:SAMPLE_LIMIT,sample:true});
  steps.push({stage:'segment_sample',host:host(media.segmentUrl),requestedRange:media.range,...safeStep(r)});requireOk(r,'segment');
  if(!r.bytes||/^\s*(?:<!doctype\s+html|<html\b)/i.test(r.data.toString('utf8',0,150)))fail('segment_empty_or_html');
  info.segmentSampleBytes=r.bytes;info.rangeAccepted=r.status===206;
  if(options.compareHeaders){
    const t=ms();try{
      const control=await requestBytes(media.segmentUrl,{...options,headers:{'User-Agent':UA,Accept:'*/*',Range:media.range},limit:SAMPLE_LIMIT,sample:true});
      steps.push({stage:'segment_without_referer_origin_control',host:host(media.segmentUrl),...safeStep(control)});
      info.noHeaderControl={status:control.status,bytes:control.bytes,htmlResponse:/^\s*(?:<!doctype\s+html|<html\b)/i.test(control.data.toString('utf8',0,150))};
    }catch(e){steps.push({stage:'segment_without_referer_origin_control',ms:elapsed(t),error:errorCode(e)});info.noHeaderControl={error:errorCode(e)};}
  }
  return info;
}
export async function refreshFixture(fixture,options={}){
  const t=ms();try{
    const r=await requestBytes(SOURCE_ORIGIN+'/api/film/'+encodeURIComponent(fixture.slug),{...options,headers:{'User-Agent':UA,Accept:'application/json'}});requireOk(r,'detail');
    let data;try{data=JSON.parse(r.data.toString('utf8'))}catch{fail('detail_not_json')}
    const movie=data?.movie;if(movie?.slug!==fixture.slug||!Array.isArray(movie.episodes))fail('detail_identity_or_schema_mismatch');
    const sources=[];for(const srv of movie.episodes)for(const item of srv.items||[])if(item.slug===fixture.episodeSlug&&item.embed){try{validateEmbed(item.embed);sources.push({server:srv.server_name||'Server',embedUrl:item.embed})}catch{}}
    if(!sources.length)fail('exact_episode_source_missing');
    const chosen=sources.find(x=>x.server===fixture.sources[0]?.server);if(!chosen)fail('exact_server_source_missing');
    return {fixture:{...fixture,sources:[chosen]},evidence:{status:'PASS',ms:elapsed(t),embedChanged:chosen.embedUrl!==fixture.sources[0].embedUrl,checkedAt:new Date().toISOString()}};
  }catch(e){return {fixture,evidence:{status:'PARTIAL',ms:elapsed(t),error:errorCode(e),usingSnapshot:true}};}
}
export function summarize(results){
  const pass=results.filter(r=>r.status==='PASS').length;
  const accessible=results.filter(r=>r.status==='PASS'||r.status==='PARTIAL').length;
  return {status:pass===results.length&&pass>0?'PASS':accessible>0?'PARTIAL':'FAIL',total:results.length,pass,partial:accessible-pass,fail:results.length-accessible,playbackVerified:false,crossNetworkGrantVerified:false,discoveryBenchmarkVerified:false};
}
export async function runSuite(fixtures,{rounds=1,refresh=true,fetchImpl=fetch,timeoutMs=TIMEOUT,onProgress=()=>{},environment='local'}={}){
  if(!Number.isInteger(rounds)||rounds<1||rounds>3)fail('invalid_rounds');
  const report={schema:'nguonc-stremio-probe-report/v1',version:VERSION,runId:crypto.randomUUID(),startedAt:new Date().toISOString(),environment,instanceUptimeSeconds:Math.round(process.uptime()),node:process.version,snapshotSource:fixtures.source,snapshotSha256:fixtures.sourceSha256||null,refreshEnabled:refresh,rounds,preflight:[],results:[],notes:['HTTP access only; Stremio playback, seek and continuous viewing have not been verified.','Timings exclude hosting spin-up before this request reaches the running process.','No live title search, TMDB call, ad stripping or video-segment proxy endpoint.']};
  const grants=[];const options={fetchImpl,timeoutMs};let items=fixtures.items;
  if(refresh){items=[];for(const item of fixtures.items){onProgress('Kiểm tra nguồn hiện tại: '+item.title);const fresh=await refreshFixture(item,options);items.push(fresh.fixture);report.preflight.push({id:item.id,...fresh.evidence});}}
  const freshIds=new Set(report.preflight.filter(x=>x.status==='PASS').map(x=>x.id));
  for(let round=1;round<=rounds;round++)for(const item of items){
    onProgress('Vòng '+round+'/'+rounds+': '+item.title);const t=ms(),steps=[];
    const result={id:item.id,title:item.title,slug:item.slug,episodeSlug:item.episodeSlug,round,embedHost:host(item.sources[0].embedUrl),sourceEvidence:freshIds.has(item.id)?'live-detail':'snapshot',steps};
    try{const grant=await bootstrap(item.sources[0].embedUrl,steps,options);const discoveryMs=elapsed(t);const inspection=await inspectGrant(grant,steps,options);
      Object.assign(result,{status:grant.expiresAt===null?'PARTIAL':'PASS',discoveryMs,inspection,expiryKnown:grant.expiresAt!==null});
      if(grant.expiresAt===null)result.warning='grant_expiry_unknown';
      grants.push({id:item.id,title:item.title,...grant});
    }catch(e){Object.assign(result,{status:'FAIL',error:errorCode(e)});}
    result.totalMs=elapsed(t);report.results.push(result);
    onProgress(item.title+': '+result.status+(result.error?' ('+result.error+')':''));
  }
  report.finishedAt=new Date().toISOString();report.summary=summarize(report.results);
  if(refresh&&report.preflight.some(x=>x.status!=='PASS'))report.notes.push('Some current source records could not be verified; snapshot-based failures do not prove current cloud access is impossible.');
  return {report,grants};
}
export async function checkSharedGrants(grants,options={}){
  const results=[];
  for(const grant of grants){const t=ms(),steps=[],result={id:grant.id,title:grant.title,steps};try{result.inspection=await inspectGrant(grant,steps,options);result.status='PASS';}catch(e){result.status='FAIL';result.error=errorCode(e);}result.totalMs=elapsed(t);results.push(result);}
  return {schema:'nguonc-stremio-device-report/v1',version:VERSION,createdAt:new Date().toISOString(),results,summary:{...summarize(results),crossNetworkGrantVerified:false},notes:['Grant was issued by remote resolver and fetched on this device. Distinct public egress IPs are not measured automatically.','PASS confirms bounded HTTP reads, not Stremio player playback.']};
}
function readable(report){
  const rows=report.results.map(r=>'| '+r.title+' | '+(r.round||'-')+' | '+r.status+' | '+(r.discoveryMs??'-')+' | '+r.totalMs+' | '+(r.error||r.warning||'')+' |');
  return '# NguonC Stremio Probe '+VERSION+'\n\nKết quả: '+report.summary.status+'\n\n| Nội dung | Vòng | Kết quả | Lấy quyền (ms) | Toàn phép thử (ms) | Lỗi/ghi chú |\n| --- | --- | --- | --- | --- | --- |\n'+rows.join('\n')+'\n\n'+report.notes.join('\n\n')+'\n';
}
export async function saveReport(report,out=path.join(ROOT,'reports')){
  await fs.mkdir(out,{recursive:true});const stem='nguonc-'+(report.schema.includes('device')?'device':'resolver')+'-'+new Date().toISOString().replace(/[:.]/g,'-');
  const file=path.join(out,stem+'.json');await fs.writeFile(file,JSON.stringify(report,null,2)+'\n');await fs.writeFile(path.join(out,stem+'.md'),readable(report));return file;
}
const json=(res,status,data)=>{res.writeHead(status,{'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});res.end(JSON.stringify(data));};
async function bodyJson(req){let size=0;const chunks=[];for await(const chunk of req){size+=chunk.length;if(size>2048)fail('request_too_large');chunks.push(chunk);}try{return JSON.parse(Buffer.concat(chunks).toString()||'{}')}catch{fail('invalid_request_json')}}
export function createProbeServer(fixtures,{accessKey,fetchImpl=fetch,timeoutMs=TIMEOUT}={}){
  if(typeof accessKey!=='string'||accessKey.length<16||accessKey.length>256)fail('TEST_ACCESS_KEY_requires_16_to_256_characters');
  const keyHash=crypto.createHash('sha256').update(accessKey).digest(),runs=new Map();let busy=false,lastStart=0;
  const authorized=req=>{const value=String(req.headers.authorization||'');if(value.length>1024)return false;return crypto.timingSafeEqual(crypto.createHash('sha256').update(value.replace(/^Bearer /,'')).digest(),keyHash)&&value.startsWith('Bearer ');};
  const server=http.createServer(async(req,res)=>{
    try{
      const u=new URL(req.url,'http://localhost');
      if(u.pathname==='/health'&&req.method==='GET')return json(res,200,{ok:true,version:VERSION});
      if(u.pathname==='/'&&req.method==='GET'){const html=await fs.readFile(path.join(ROOT,'index.html'));res.writeHead(200,{'Content-Type':'text/html; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Referrer-Policy':'no-referrer','Content-Security-Policy':"default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'; form-action 'self'"});return res.end(html);}
      if(!authorized(req))return json(res,401,{error:'access_key_required'});
      for(const [id,run] of runs)if(Date.now()-run.createdAt>20*60*1000&&!run.running)runs.delete(id);
      if(u.pathname==='/api/run'&&req.method==='POST'){
        if(busy||Date.now()-lastStart<10000)return json(res,429,{error:'run_busy_or_cooldown'});
        const args=await bodyJson(req);const rounds=args.rounds??1;if(!Number.isInteger(rounds)||rounds<1||rounds>3)return json(res,400,{error:'invalid_rounds'});
        if(args.refresh!==undefined&&typeof args.refresh!=='boolean')return json(res,400,{error:'invalid_refresh'});
        while(runs.size>=5){const oldest=[...runs].find(([,r])=>!r.running);if(!oldest)break;runs.delete(oldest[0]);}
        const id=crypto.randomUUID(),run={createdAt:Date.now(),running:true,progress:[],report:null,grants:[]};runs.set(id,run);busy=true;lastStart=Date.now();
        json(res,202,{runId:id});
        runSuite(fixtures,{rounds,refresh:args.refresh!==false,environment:process.env.RENDER?'render':'server',fetchImpl,timeoutMs,onProgress:line=>run.progress.push(line)}).then(result=>{run.report=result.report;run.report.remoteRunId=id;run.grants=result.grants;}).catch(e=>{run.error=errorCode(e)}).finally(()=>{run.running=false;busy=false;});return;
      }
      const m=u.pathname.match(/^\/api\/runs\/([a-f0-9-]{36})(?:\/(report|grants))?$/);
      if(m&&req.method==='GET'){
        const run=runs.get(m[1]);if(!run)return json(res,404,{error:'run_missing_or_restarted'});
        if(m[2]==='report'){if(!run.report)return json(res,409,{error:run.running?'run_in_progress':'run_failed'});return json(res,200,run.report);}
        if(m[2]==='grants'){
          if(run.running)return json(res,409,{error:'run_in_progress'});
          const usable=run.grants.filter(g=>Date.now()-g.issuedAt<10*60*1000&&(g.expiresAt===null?Date.now()-g.issuedAt<60000:g.expiresAt>Date.now()+15000));
          return json(res,200,{runId:m[1],grants:usable});
        }
        return json(res,200,{runId:m[1],running:run.running,progress:run.progress,error:run.error,summary:run.report?.summary});
      }
      return json(res,404,{error:'not_found'});
    }catch(e){return json(res,400,{error:errorCode(e)});}
  });
  server.requestTimeout=15000;server.headersTimeout=10000;return server;
}
async function remoteJson(base,route,key,{method='GET',data,timeoutMs=TIMEOUT}={}){
  const r=await requestBytes(base+route,{timeoutMs,method,headers:{Authorization:'Bearer '+key,'Content-Type':'application/json'},body:data?JSON.stringify(data):undefined,limit:JSON_LIMIT});requireOk(r,'remote');try{return JSON.parse(r.data.toString('utf8'))}catch{fail('remote_not_json')}
}
async function deviceMode(){
  const rl=createInterface({input:process.stdin,output:process.stdout});let base,key;
  try{base=(await rl.question('Dán địa chỉ dịch vụ kiểm tra Render (https://...onrender.com): ')).trim();key=(await rl.question('Nhập TEST_ACCESS_KEY của dịch vụ kiểm tra: ')).trim();}finally{rl.close();}
  const u=validateTarget(base);if(u.pathname!=='/'||u.search)fail('enter_origin_only');base=u.origin;
  console.log('Đang đánh thức dịch vụ và chạy một vòng kiểm tra máy chủ...');const t=ms();
  const started=await remoteJson(base,'/api/run',key,{method:'POST',data:{rounds:1,refresh:true},timeoutMs:90000});const requestMs=elapsed(t);
  const deadline=Date.now()+240000;let status;
  do{await new Promise(r=>setTimeout(r,1500));status=await remoteJson(base,'/api/runs/'+started.runId,key);console.log(status.progress.at(-1)||'Đang chờ...');if(Date.now()>deadline)fail('remote_run_deadline');}while(status.running);
  if(status.error)fail(status.error);
  const serverReport=await remoteJson(base,'/api/runs/'+started.runId+'/report',key);serverReport.clientStartRequestMs=requestMs;serverReport.notes.push('clientStartRequestMs includes network, possible hosting wake-up and run creation; it does not isolate wake-up latency.');console.log('Đã lưu báo cáo máy chủ: '+await saveReport(serverReport));
  const share=await remoteJson(base,'/api/runs/'+started.runId+'/grants',key);
  if(!share.grants.length){console.log('Máy chủ chưa có quyền phát dùng được. Dừng kiểm tra thiết bị tại đây.');return 2;}
  const report=await checkSharedGrants(share.grants,{compareHeaders:true});report.remoteRunId=started.runId;
  console.log('Đã lưu báo cáo thiết bị: '+await saveReport(report));console.log('KẾT QUẢ THIẾT BỊ: '+report.summary.status);return report.summary.status==='PASS'?0:2;
}
async function main(){
  const fixtures=JSON.parse(await fs.readFile(path.join(ROOT,'fixtures.json'),'utf8'));
  if(process.argv.includes('--serve')){
    const key=process.env.TEST_ACCESS_KEY;if(!key)fail('set_TEST_ACCESS_KEY_before_server_start');
    const server=createProbeServer(fixtures,{accessKey:key});server.listen(Number(process.env.PORT)||10000,'0.0.0.0',()=>console.log('NguonC Stremio Probe '+VERSION+' ready. This is a diagnostic service, not a Stremio addon.'));return;
  }
  if(process.argv.includes('--device')){process.exitCode=await deviceMode();return;}
  const at=process.argv.indexOf('--rounds'),rounds=at>=0?Number(process.argv[at+1]):1;
  const report=(await runSuite(fixtures,{rounds,refresh:!process.argv.includes('--snapshot-only'),environment:'local',onProgress:line=>console.log(line)})).report;
  console.log('BÁO CÁO: '+await saveReport(report));console.log('KẾT QUẢ HTTP: '+report.summary.status);process.exitCode=report.summary.status==='PASS'?0:2;
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url))main().catch(e=>{console.error('LỖI: '+errorCode(e));process.exitCode=1;});
