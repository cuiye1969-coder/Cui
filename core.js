(function(root){
'use strict';
const levels=['A1','A2','B1','B2'],DAY=86400000;
const fresh=()=>({version:1,senses:{},units:{},mistakes:{},favorites:[],grammarFavorites:[],days:{},settings:{dailyMinutes:30,wordLevels:['A1'],wordCount:20,wordMode:'both',reviewHour:4,profileName:'小八',profileAvatar:'学'} ,lastUnit:'A1.1-01'});
const dayKey=(date=new Date())=>[date.getFullYear(),String(date.getMonth()+1).padStart(2,'0'),String(date.getDate()).padStart(2,'0')].join('-');
const shuffle=(a,rng=Math.random)=>{a=[...a];for(let i=a.length-1;i>0;i--){let j=Math.floor(rng()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;};
const normalize=s=>String(s).trim().normalize('NFC').replace(/\s+/g,' ').replace(/[.!?。！？]+$/,'').toLocaleLowerCase('de');
const searchFold=s=>normalize(s).replace(/ä/g,'ae').replace(/ö/g,'oe').replace(/ü/g,'ue').replace(/ß/g,'ss');
const editDistance=(a,b)=>{a=[...a];b=[...b];let prev=Array.from({length:b.length+1},(_,i)=>i);for(let i=0;i<a.length;i++){const next=[i+1];for(let j=0;j<b.length;j++)next[j+1]=Math.min(next[j]+1,prev[j+1]+1,prev[j]+(a[i]===b[j]?0:1));prev=next;}return prev[b.length];};
function searchRank(word,query){
 const raw=normalize(query),q=searchFold(query);if(!q)return 0;
 const fold=x=>searchFold(x),lemma=[word.lemma,word.id,word.article?word.article+' '+word.lemma:''].filter(Boolean).map(fold),forms=[...(word.present||[]),word.past,word.participle,word.plural,word.comparative,word.superlative,...Object.values(word.conjugation||{}).flat(),...(word.sourceForms||[]).map(f=>f.form)].filter(Boolean).map(fold),meanings=word.senses.flatMap(s=>[s.zh,s.pattern]).filter(Boolean).map(fold),examples=word.senses.map(s=>s.example).filter(Boolean).map(fold);
 if(lemma.includes(q))return 0;
 if(forms.includes(q))return 1;
 const prefix=(xs,base)=>{const hits=xs.filter(x=>x.startsWith(q));return hits.length?base+Math.min(...hits.map(x=>(x.length-q.length)/Math.max(1,x.length))):Infinity;};
 let score=Math.min(prefix(lemma,10),prefix(forms,20));if(Number.isFinite(score))return score;
 const inside=(xs,base)=>{const hits=xs.map(x=>x.indexOf(q)).filter(i=>i>=0);return hits.length?base+Math.min(...hits):Infinity;};
 score=Math.min(inside(lemma,30),inside(forms,40),inside(meanings,50),inside(examples,60));if(Number.isFinite(score))return score;
 if(/[^a-zäöüß]/i.test(raw)||q.length<2)return Infinity;
 const pool=[...lemma,...forms].filter(x=>x.length);let similarity=0;for(const x of pool){const target=x.length>q.length+4?x.slice(0,q.length+4):x;similarity=Math.max(similarity,1-editDistance(q,target)/Math.max(q.length,target.length));}
 const threshold=q.length<=3?.6:q.length<=5?.5:.42;return similarity>=threshold?100+(1-similarity)*100:Infinity;
}
function rankWords(words,query){const q=normalize(query);if(!q)return [...words];const ranked=words.map((word,index)=>({word,index,score:searchRank(word,q)})).filter(x=>Number.isFinite(x.score));const exactLemma=ranked.filter(x=>x.score===0),exactForm=ranked.filter(x=>x.score===1),chosen=exactLemma.length?exactLemma:exactForm.length?exactForm:ranked;return chosen.sort((a,b)=>a.score-b.score||a.word.lemma.localeCompare(b.word.lemma,'de')||a.index-b.index).map(x=>x.word);}
function makeCore(data){
 const words=Object.fromEntries(data.words.map(w=>[w.id,w])),units=Object.fromEntries(data.units.map(u=>[u.id,u])),senses={};
 data.words.forEach(w=>w.senses.forEach(s=>senses[s.id]={...s,word:w}));
 function focus(u){return u.focus.flatMap(id=>words[id].senses.filter(s=>levels.indexOf(s.level)<=levels.indexOf(u.level)).map(s=>s.id));}
 function passed(u,state){return state.units[u.id]?.passed===true||(state.units[u.id]?.score??0)>=85;}
 function course(state){let count=0;for(const u of data.units){if(!passed(u,state))break;count++;}return {count,current:data.units[count]||null,passed:data.units.filter(u=>passed(u,state)).length};}
 function progress(u,state){const ids=focus(u),mastered=ids.filter(id=>state.senses[id]?.status==='mastered').length,ratio=ids.length?mastered/ids.length:1,quiz=state.units[u.id]?.score??null,errors=Object.values(state.mistakes).filter(m=>m.unit===u.id&&!m.resolved).length,complete=passed(u,state);return {mastered,total:ids.length,ratio,quiz,errors,complete,ready:complete&&ratio>=.8&&errors===0};}
 function due(state,now=Date.now()){return Object.entries(state.senses).filter(([id,s])=>senses[id]&&s.status&&s.due<=now).sort((a,b)=>(['unknown','familiar','mastered'].indexOf(a[1].status)-['unknown','familiar','mastered'].indexOf(b[1].status))||a[1].due-b[1].due).map(([id])=>id);}
 function nextReview(state,days=1,now=Date.now()){const d=new Date(now);d.setDate(d.getDate()+Math.max(1,days));d.setHours(state.settings.reviewHour??4,0,0,0);return d.getTime();}
 function setReviewHour(state,hour,now=Date.now()){if(!Number.isInteger(hour)||hour<0||hour>23)throw Error('请选择 0–23 点');state.settings.reviewHour=hour;for(const s of Object.values(state.senses)){if(s.due>now&&s.status!=='unknown'){const d=new Date(s.due);d.setHours(hour,0,0,0);s.due=d.getTime();}}}
 function rate(state,id,status){if(!Object.hasOwn(senses,id)||!['unknown','familiar','mastered'].includes(status))throw Error('无效的辅助标记');const s=state.senses[id]??={};s.selfMark=status;return s;}
 const normZh=x=>normalize(x).replace(/[\s，,、；;：:]/g,'');
 function accepted(id,direction){const s=senses[id];if(!s)throw Error('未知义项');if(direction==='zh-de')return [...new Set([s.word.lemma,...(s.germanAnswers||[]),...(s.word.article?[s.word.article+' '+s.word.lemma]:[])])];return [...new Set([s.zh,...(s.answers||[]),...s.zh.replace(/[（(][^）)]*[）)]/g,'').split(/[；;、，,]/)].map(x=>x.trim()).filter(Boolean))];}
 function checkAnswer(id,direction,answer){const fn=direction==='de-zh'?normZh:normalize;return !!fn(answer)&&accepted(id,direction).some(x=>fn(x)===fn(answer));}
 function practice(state,id,direction,answer,hinted=false,now=Date.now()){
  if(!Object.hasOwn(senses,id)||!['de-zh','zh-de'].includes(direction))throw Error('无效练习');
  const correct=checkAnswer(id,direction,answer),ok=correct&&!hinted,s=state.senses[id]??={};s.practice??={};
  const p=s.practice[direction]??={attempts:0,correct:0,streak:0,credits:0,lastCredit:0};p.attempts++;p.last=now;
  if(ok){p.correct++;p.streak++;if(!p.credits||now-p.lastCredit>=20*3600000){p.credits=Math.min(6,(p.credits||0)+1);p.lastCredit=now;}}
  else{p.streak=0;p.credits=Math.max(0,(p.credits||0)-1);}
  const a=s.practice['de-zh']?.credits||0,b=s.practice['zh-de']?.credits||0;
  s.proficiency=Math.round((Math.min(3,a)+Math.min(3,b))/6*100);
  s.status=!ok?'unknown':a>=3&&b>=3?'mastered':'familiar';
  s.last=now;s.due=ok?nextReview(state,Math.min(30,2**Math.min(a,b)),now):now+10*60000;
  return {correct,ok,hinted,proficiency:s.proficiency,status:s.status};
 }
 function bank(u){const qs=u.examples.map((e,i)=>({...e,id:u.id+'-g'+i,unit:u.id,kind:e.kind||(i%2?'input':'choice'),word:null,source:'grammar'}));u.focus.forEach((id,i)=>{const w=words[id],s=w.senses.filter(s=>levels.indexOf(s.level)<=levels.indexOf(u.level)&&s.example&&s.translation).at(-1);if(!s)return;const others=[...new Set(data.words.filter(x=>x.id!==id&&x.pos===w.pos).map(x=>x.senses[0].zh).filter(x=>x!==s.zh))],choices=others.slice(i,i+3).length===3?others.slice(i,i+3):others.slice(0,3);if(choices.length<3)return;qs.push({id:u.id+'-v'+i,unit:u.id,kind:'choice',prompt:s.example+'\n句中「'+w.lemma+'」的含义是？',answer:s.zh,choices,translation:s.translation,explanation:s.pattern||'结合词条义项与语境判断。',word:id,source:'vocabulary'});});return qs;}
 const questions=Object.fromEntries(data.units.flatMap(bank).map(q=>[q.id,q]));
 function grade(state,u,qs,answers,review=false,now=Date.now()){let correct=0;const results=qs.map(q=>{const ok=normalize(answers[q.id]||'')===normalize(q.answer);if(ok)correct++;if(!ok)state.mistakes[q.id]={unit:q.unit,resolved:false,last:now,count:(state.mistakes[q.id]?.count||0)+1};else if(review&&state.mistakes[q.id]){state.mistakes[q.id].resolved=true;state.mistakes[q.id].reviewed=now;}return {id:q.id,ok};});const score=qs.length?correct/qs.length*100:0;if(!review&&u){const prev=state.units[u.id]||{};state.units[u.id]={...prev,score,passed:passed(u,state)||score>=85,best:Math.max(prev.best||prev.score||0,score),attempts:(prev.attempts||0)+1,lastQuiz:now};}return {score,correct,total:qs.length,results};}
 function remaining(u,state){const p=progress(u,state);if(p.complete)return 0;return (state.units[u.id]?.read?0:u.minutes)+(p.quiz===null?12:10);}
 function pace(state,now=new Date()){const ds=[];for(let i=0;i<7;i++){const d=new Date(now);d.setDate(d.getDate()-i);ds.push(state.days[dayKey(d)]?.total||0);}const active=ds.filter(x=>x>=60);return active.length>=3?{minutes:ds.reduce((a,b)=>a+b,0)/60/7,basis:'最近 7 个自然日平均',observed:true}:{minutes:state.settings.dailyMinutes,basis:'每日目标（尚无 3 天有效记录）',observed:false};}
 function estimate(us,state){const mins=us.reduce((n,u)=>n+remaining(u,state),0),p=pace(state),days=mins/Math.max(1,p.minutes);return {minutes:mins,low:mins?Math.max(1,Math.ceil(days*.8)):0,high:mins?Math.max(1,Math.ceil(days*1.4)):0,...p,remainingMinutes:mins};}
 function validate(input){if(!input||input.version!==1||typeof input!=='object')throw Error('不支持的备份版本');const out=fresh();const finite=x=>typeof x==='number'&&Number.isFinite(x)&&x>=0;
 for(const [id,s] of Object.entries(input.senses||{})){if(!Object.hasOwn(senses,id)||!s||typeof s!=='object')continue;const n={focus:!!s.focus,note:typeof s.note==='string'?s.note.slice(0,2000):''};const mark=s.selfMark||(!s.practice?s.status:null);if(['unknown','familiar','mastered'].includes(mark))n.selfMark=mark;
  if(s.practice&&typeof s.practice==='object'){n.practice={};for(const dir of ['de-zh','zh-de']){const p=s.practice[dir];if(!p)continue;n.practice[dir]={};for(const k of ['attempts','correct','streak','credits','lastCredit','last'])n.practice[dir][k]=finite(p[k])?p[k]:0;n.practice[dir].credits=Math.min(6,n.practice[dir].credits);}
   const a=n.practice['de-zh']?.credits||0,b=n.practice['zh-de']?.credits||0;n.proficiency=Math.round((Math.min(3,a)+Math.min(3,b))/6*100);n.status=s.status==='unknown'?'unknown':a>=3&&b>=3?'mastered':'familiar';n.due=finite(s.due)?s.due:0;n.last=finite(s.last)?s.last:0;
  }else if(s.status){n.status='unknown';n.due=0;n.last=finite(s.last)?s.last:0;}out.senses[id]=n;}
 for(const [id,u] of Object.entries(input.units||{})){if(!Object.hasOwn(units,id)||!u)continue;out.units[id]={read:!!u.read,seconds:finite(u.seconds)?u.seconds:0,passed:u.passed===true||(u.score||0)>=85};if(finite(u.score)&&u.score<=100)out.units[id].score=u.score;if(finite(u.best)&&u.best<=100)out.units[id].best=u.best;if(finite(u.attempts))out.units[id].attempts=u.attempts;}
 for(const [id,m] of Object.entries(input.mistakes||{})){if(!Object.hasOwn(questions,id)||!m)continue;out.mistakes[id]={unit:questions[id].unit,resolved:!!m.resolved,last:finite(m.last)?m.last:0,count:finite(m.count)?m.count:1};}
 for(const [d,v] of Object.entries(input.days||{})){if(!/^\d{4}-\d{2}-\d{2}$/.test(d)||!v)continue;out.days[d]={};for(const k of ['total','grammar','words','quiz','review'])out.days[d][k]=finite(v[k])?Math.min(v[k],86400):0;}
 out.favorites=Array.isArray(input.favorites)?[...new Set(input.favorites.filter(id=>words[id]))]:[];out.grammarFavorites=Array.isArray(input.grammarFavorites)?[...new Set(input.grammarFavorites.filter(id=>units[id]))]:[];
 out.settings.dailyMinutes=Math.max(5,Math.min(300,Number(input.settings?.dailyMinutes)||30));if(units[input.lastUnit])out.lastUnit=input.lastUnit;
 const ls=input.settings?.wordLevels;if(Array.isArray(ls)&&ls.some(l=>levels.includes(l)))out.settings.wordLevels=[...new Set(ls.filter(l=>levels.includes(l)))];if([10,20,30,50].includes(input.settings?.wordCount))out.settings.wordCount=input.settings.wordCount;if(['both','de-zh','zh-de'].includes(input.settings?.wordMode))out.settings.wordMode=input.settings.wordMode;if(Number.isInteger(input.settings?.reviewHour)&&input.settings.reviewHour>=0&&input.settings.reviewHour<=23)out.settings.reviewHour=input.settings.reviewHour;if(typeof input.settings?.profileName==='string')out.settings.profileName=input.settings.profileName.trim().slice(0,30)||'小八';if(typeof input.settings?.profileAvatar==='string'&&['学','八','德','☆','●','☀'].includes(input.settings.profileAvatar))out.settings.profileAvatar=input.settings.profileAvatar;if(typeof input.settings?.profileAvatarData==='string'&&input.settings.profileAvatarData.startsWith('data:image/')&&input.settings.profileAvatarData.length<=1400000)out.settings.profileAvatarData=input.settings.profileAvatarData;return out;}
 return {words,units,senses,focus,progress,passed,course,due,nextReview,setReviewHour,rate,practice,checkAnswer,accepted,bank,questions,grade,remaining,pace,estimate,validate};
}
root.WortwegCore={makeCore,fresh,dayKey,shuffle,normalize,searchFold,searchRank,rankWords,levels};
})(typeof window==='undefined'?globalThis:window);
