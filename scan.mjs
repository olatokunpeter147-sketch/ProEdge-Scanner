/* ProEdge Scanner v3: runs on GitHub Actions and sends BUY/SELL alerts to Telegram.
   Pure price action: double top/bottom, head & shoulders, structure break & retest, support/resistance zones, fair value gaps.
   The engine below is identical to the one inside ProEdge_v3.html, so the app and the scanner always agree. */

/* ======== PRICE-ACTION ENGINE (same as ProEdge_v3.html) ======== */
const TF = {
  '5m':  {ms:300000,   htf:'15m'},
  '15m': {ms:900000,   htf:'1h'},
  '1h':  {ms:3600000,  htf:'4h'},
  '4h':  {ms:14400000, htf:'1d'},
  '1d':  {ms:86400000, htf:null}
};
const THRESH = 65;          // minimum score for a signal
const isNum = v => typeof v === 'number' && isFinite(v);
const last = a => a[a.length-1];
function dec(p){ const a=Math.abs(p); return a>=1000?2:a>=100?3:a>=10?4:a>=1?5:6; }
function fmt(p){ return isNum(p) ? p.toFixed(dec(p)) : '—'; }

/* ---------- data parsers ---------- */
function parseBinance(j){
  if(!Array.isArray(j)) throw new Error('bad Binance reply');
  return j.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]}));
}
function parseBybit(j){
  if(!j || j.retCode!==0 || !j.result || !Array.isArray(j.result.list)) throw new Error('bad Bybit reply');
  return j.result.list.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})).reverse();
}
function parseOKX(j){
  if(!j || j.code!=='0' || !Array.isArray(j.data)) throw new Error('bad OKX reply');
  return j.data.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})).reverse();
}
function parseYahoo(j){
  const r = j && j.chart && j.chart.result && j.chart.result[0];
  if(!r || !r.timestamp || !r.indicators || !r.indicators.quote || !r.indicators.quote[0]) throw new Error('bad Yahoo reply');
  const q = r.indicators.quote[0], out=[];
  for(let i=0;i<r.timestamp.length;i++){
    if(isNum(q.open[i]) && isNum(q.high[i]) && isNum(q.low[i]) && isNum(q.close[i]))
      out.push({t:r.timestamp[i]*1000,o:q.open[i],h:q.high[i],l:q.low[i],c:q.close[i],v:q.volume&&isNum(q.volume[i])?q.volume[i]:0});
  }
  return out;
}
function parseDeriv(j){
  if(!j || !Array.isArray(j.candles)) throw new Error('bad Deriv reply');
  return j.candles.map(k=>({t:+k.epoch*1000,o:+k.open,h:+k.high,l:+k.low,c:+k.close,v:0}));
}
function parseTD(j){
  if(!j || j.status==='error') throw new Error((j&&j.message)||'bad Twelve Data reply');
  if(!Array.isArray(j.values)) throw new Error('bad Twelve Data reply');
  return j.values.map(k=>({t:Date.parse(String(k.datetime).replace(' ','T')+(String(k.datetime).length>10?'Z':'T00:00:00Z')),o:+k.open,h:+k.high,l:+k.low,c:+k.close,v:+(k.volume||0)}));
}
function clean(cs){
  const m = new Map();
  for(const k of cs){
    if(isNum(k.t)&&isNum(k.o)&&isNum(k.h)&&isNum(k.l)&&isNum(k.c)&&k.h>=k.l&&k.h>=Math.max(k.o,k.c)-1e-12&&k.l<=Math.min(k.o,k.c)+1e-12) m.set(k.t,k);
  }
  return [...m.values()].sort((a,b)=>a.t-b.t);
}
function resample(cs, ms){
  const out=[]; let cur=null;
  for(const k of cs){
    const b=Math.floor(k.t/ms)*ms;
    if(!cur || cur.t!==b){ if(cur) out.push(cur); cur={t:b,o:k.o,h:k.h,l:k.l,c:k.c,v:k.v}; }
    else { cur.h=Math.max(cur.h,k.h); cur.l=Math.min(cur.l,k.l); cur.c=k.c; cur.v+=k.v; }
  }
  if(cur) out.push(cur);
  return out;
}

/* ---------- volatility (used only to measure distances) ---------- */
function atrCalc(h,l,c,n=14){
  const out=new Array(c.length).fill(NaN);
  if(c.length<n) return out;
  const tr=[h[0]-l[0]];
  for(let i=1;i<c.length;i++) tr.push(Math.max(h[i]-l[i],Math.abs(h[i]-c[i-1]),Math.abs(l[i]-c[i-1])));
  let s=0; for(let i=0;i<n;i++) s+=tr[i];
  let a=s/n; out[n-1]=a;
  for(let i=n;i<tr.length;i++){ a=(a*(n-1)+tr[i])/n; out[i]=a; }
  return out;
}
// mirror the market upside-down so that every bullish detector also gives the bearish one
function negate(cs){ return cs.map(k=>({t:k.t,o:-k.o,h:-k.l,l:-k.h,c:-k.c,v:k.v})); }

/* ---------- swings, structure, zones, fair value gaps ---------- */
function pivots(h,l,k){
  const out=[];
  for(let i=k;i<h.length-k;i++){
    let isH=true,isL=true;
    for(let j=1;j<=k;j++){
      if(h[i-j]>=h[i]||h[i+j]>h[i]) isH=false;
      if(l[i-j]<=l[i]||l[i+j]<l[i]) isL=false;
    }
    if(isH) out.push({i,p:h[i],type:'H'});
    if(isL) out.push({i,p:l[i],type:'L'});
  }
  return out.sort((a,b)=>a.i-b.i);
}
// swings that alternate high/low and each move at least minATR from the previous one
function zigzag(h,l,atr,fb,k,minATR){
  const raw=pivots(h,l,k), out=[];
  for(const pv of raw){
    const prev=out[out.length-1];
    if(!prev){ out.push(pv); continue; }
    if(pv.type===prev.type){
      if(pv.type==='H' ? pv.p>prev.p : pv.p<prev.p) out[out.length-1]=pv;
      continue;
    }
    const a=isNum(atr[pv.i])?atr[pv.i]:fb;
    if(Math.abs(pv.p-prev.p)>=minATR*a) out.push(pv);
  }
  for(let q=0;q<out.length;q++){
    const ref=q>0?out[q-1]:out[q+1];
    out[q].leg=ref?Math.abs(out[q].p-ref.p):0;
  }
  return out;
}
function structure(sw,close,A){
  const H=sw.filter(s=>s.type==='H'), L=sw.filter(s=>s.type==='L');
  if(H.length<2||L.length<2) return {dir:0,broken:false,label:'Not enough structure yet',rangeHigh:NaN,rangeLow:NaN};
  const h1=H[H.length-2],h2=H[H.length-1],l1=L[L.length-2],l2=L[L.length-1],tol=0.15*A;
  const hh=h2.p>h1.p+tol, lh=h2.p<h1.p-tol, hl=l2.p>l1.p+tol, ll=l2.p<l1.p-tol;
  let dir=0, broken=false, label='Ranging market';
  if(hh&&hl){ dir=1; label='Bullish trend (higher highs, higher lows)'; }
  else if(lh&&ll){ dir=-1; label='Bearish trend (lower highs, lower lows)'; }
  if(dir===1 && close<l2.p-0.1*A){ dir=0; broken=true; label='Bullish structure broken (possible reversal)'; }
  else if(dir===-1 && close>h2.p+0.1*A){ dir=0; broken=true; label='Bearish structure broken (possible reversal)'; }
  return {dir,broken,label,rangeHigh:Math.max(h1.p,h2.p),rangeLow:Math.min(l1.p,l2.p)};
}
// support/resistance zones = clusters of swing points at about the same price
function buildZones(sw,A){
  const pts=sw.map(s=>({p:s.p,i:s.i,leg:s.leg||0})).sort((a,b)=>a.p-b.p);
  const groups=[]; let cur=null;
  for(const pt of pts){
    if(cur && pt.p-cur.maxP<=0.5*A && pt.p-cur.minP<=1.0*A){ cur.pts.push(pt); cur.maxP=pt.p; }
    else { if(cur) groups.push(cur); cur={pts:[pt],minP:pt.p,maxP:pt.p}; }
  }
  if(cur) groups.push(cur);
  const pad=0.12*A;
  return groups.map(g=>{
    const touches=g.pts.length, maxLeg=Math.max(...g.pts.map(x=>x.leg));
    return {bottom:g.minP-pad,top:g.maxP+pad,touches,lastI:Math.max(...g.pts.map(x=>x.i)),major:touches>=2||maxLeg>=3*A};
  });
}
function findFVGs(o,h,l,c,atr,lookback){
  const N=h.length, start=Math.max(2,N-lookback), res=[];
  for(let i=start;i<N;i++){
    const a=atr[i]; if(!isNum(a)) continue;
    const minGap=a*0.25;
    let z=null;
    if(l[i]-h[i-2]>=minGap && c[i-1]>o[i-1]) z={type:'bull',top:l[i],bottom:h[i-2],i};
    else if(l[i-2]-h[i]>=minGap && c[i-1]<o[i-1]) z={type:'bear',top:l[i-2],bottom:h[i],i};
    if(!z) continue;
    let filled=false;
    for(let q=i+1;q<N;q++){
      if(z.type==='bull' && l[q]<=z.bottom){ filled=true; break; }
      if(z.type==='bear' && h[q]>=z.top){ filled=true; break; }
    }
    if(!filled) res.push(z);
  }
  return res;
}

/* ---------- every LONG setup on the last closed candle (the bearish ones come from the mirrored market) ---------- */
function longSetups(cs,htfDir,sg){
  const N=cs.length, j=N-1;
  const o=cs.map(k=>k.o), h=cs.map(k=>k.h), l=cs.map(k=>k.l), c=cs.map(k=>k.c);
  const atr=atrCalc(h,l,c,14), A=atr[j];
  if(!(A>0)) return {setups:[],ctx:null};
  const px=v=>fmt(sg*v);
  const dw=sg>0?'bullish':'bearish', ow=sg>0?'bearish':'bullish';
  const side=sg>0?'below':'above';
  const sw=zigzag(h,l,atr,A,3,1.2);
  const st=structure(sw,c[j],A);
  const zones=buildZones(sw.filter(s=>s.i>=N-250),A);
  const fvgs=findFVGs(o,h,l,c,atr,120);
  const highs=sw.filter(s=>s.type==='H'), lows=sw.filter(s=>s.type==='L');
  const NM={
    bos: sg>0?'Bullish structure break & retest':'Bearish structure break & retest',
    db:  sg>0?'Double bottom':'Double top',
    hs:  sg>0?'Inverse head & shoulders':'Head & shoulders',
    zone:sg>0?'Support zone rejection':'Resistance zone rejection'
  };
  const rngJ=Math.max(h[j]-l[j],1e-12);
  const lowWick=(Math.min(o[j],c[j])-l[j])/rngJ;
  const raw=[];

  function finish(kind,base,entry,sl,level,draw,notes,bonus){
    const risk=entry-sl;
    let score=base+(bonus||0);
    const blocks=[], nts=notes.slice();
    if(kind==='bos'||kind==='zone'){
      if(st.dir===1){ score+=(kind==='bos'?16:14); nts.push('Market structure is '+dw+' (trade goes with the trend)'); }
      else if(st.dir===0){ score+=(kind==='bos'?6:8); nts.push(st.broken?'The previous '+ow+' structure has just broken':'Market is ranging'); }
      else blocks.push('Market structure is '+ow+', so this would be a counter-trend trade.');
    }
    if(htfDir===1){ score+=12; nts.push('Higher timeframe trend is '+dw); }
    else if(htfDir===0){ score+=4; }
    else blocks.push('Higher timeframe trend is '+ow+', against this trade.');
    if(kind==='bos'){
      const zc=zones.find(z=>z.touches>=2&&level>=z.bottom-0.3*A&&level<=z.top+0.3*A);
      if(zc){ score+=8; nts.push('The broken level is a strong zone ('+zc.touches+' touches)'); }
    }
    const demand=fvgs.find(f=>f.type==='bull'&&f.top<=entry+0.1*A&&f.top>=entry-1.5*A);
    if(demand){ score+=6; nts.push('Unfilled '+dw+' fair value gap just '+side+' price'); }
    const supply=fvgs.find(f=>f.type==='bear'&&f.bottom>=entry-0.1*A&&f.bottom<=entry+1.5*risk);
    if(supply){ score-=8; nts.push('An unfilled '+ow+' fair value gap ahead is a headwind'); }
    if(risk<0.7*A) blocks.push('Stop loss would be too tight ('+(risk/A).toFixed(1)+' ATR).');
    if(risk>3.5*A) blocks.push('Stop loss would be too wide ('+(risk/A).toFixed(1)+' ATR).');
    const over=zones.filter(z=>z.major&&z.bottom>entry+0.2*A).sort((a,b)=>a.bottom-b.bottom)[0];
    if(over){
      const d=over.bottom-entry;
      if(d<1.5*risk) blocks.push((sg>0?'Resistance':'Support')+' zone near '+px(over.bottom)+' is only '+(d/A).toFixed(1)+' ATR away, not enough room for the targets.');
    }
    raw.push({kind,name:NM[kind],score:Math.round(score),notes:nts,blocks,entry,sl,risk,level,draw});
  }

  /* 1) structure break + retest: price closes through a swing high, comes back, touches it and holds */
  {
    let best=null;
    for(const s of highs){
      if(s.i<N-100) continue;
      let b=-1;
      for(let q=s.i+1;q<N;q++){ if(c[q]>s.p+0.15*A){ b=q; break; } }
      if(b<0||b>=j||j-b>40) continue;
      if(!(c[b]>o[b] && ((c[b]-o[b])>=0.45*A || (c[b]-s.p)>=0.35*A))) continue;
      let r=-1;
      for(let q=b+1;q<N;q++){
        if(c[q]<s.p-0.3*A){ r=-2; break; }
        if(l[q]<=s.p+0.25*A){ r=q; break; }
      }
      if(r!==j) continue;
      if(!(c[j]>s.p && l[j]>=s.p-0.5*A)) continue;
      if(!(c[j]>o[j] || lowWick>=0.4)) continue;
      if(!best||s.p>best.s.p) best={s,b};
    }
    if(best){
      const s=best.s, b=best.b;
      const entry=c[j], sl=Math.min(l[j],s.p)-0.35*A;
      let bonus=0;
      if((c[b]-o[b])>=0.8*A) bonus+=4;
      if(lowWick>=0.4) bonus+=4;
      finish('bos',50,entry,sl,s.p,
        {lines:[{i1:s.i,p1:s.p,i2:j,p2:s.p}],points:[{i:b,p:c[b]},{i:j,p:l[j]}]},
        ['Price broke '+px(s.p)+' and came back to retest it'],bonus);
    }
  }

  /* 2) double bottom: two equal lows, then a close above the neckline */
  if(lows.length>=2){
    const L2=lows[lows.length-1], L1=lows[lows.length-2];
    const P=highs.filter(s=>s.i>L1.i&&s.i<L2.i).sort((a,b)=>b.p-a.p)[0];
    const bf=highs.filter(s=>s.i<L1.i).slice(-1)[0];
    if(P&&bf){
      const lowMin=Math.min(L1.p,L2.p), lowAvg=(L1.p+L2.p)/2, height=P.p-lowAvg, spacing=L2.i-L1.i;
      if(Math.abs(L1.p-L2.p)<=0.45*A && height>=1.5*A && spacing>=6 && spacing<=100 && bf.p-L1.p>=2*A && j-L2.i<=45){
        let minAfter=Infinity, br=-1;
        for(let q=L2.i+1;q<N;q++){ minAfter=Math.min(minAfter,l[q]); if(br<0&&c[q]>P.p+0.1*A) br=q; }
        if(br>=j-1 && c[j]>P.p+0.1*A && c[j]-P.p<=1.0*A && minAfter>=lowMin-0.3*A){
          const entry=c[j];
          const sl=Math.max(lowMin-0.3*A, P.p-Math.min(Math.max(0.5*height,0.8*A),2.5*A));
          let bonus=0;
          if(Math.abs(L1.p-L2.p)<=0.2*A) bonus+=6;
          if(height>=2.5*A) bonus+=6;
          if((P.p+height-entry)>=1.5*(entry-sl)) bonus+=6;
          finish('db',58,entry,sl,lowMin,
            {lines:[{i1:P.i,p1:P.p,i2:j,p2:P.p}],points:[{i:L1.i,p:L1.p},{i:L2.i,p:L2.p}]},
            [NM.db+' near '+px(lowAvg)+', neckline '+px(P.p)+' broken'],bonus);
        }
      }
    }
  }

  /* 3) inverse head & shoulders: lower middle low, matching shoulders, close above the neckline */
  if(lows.length>=3){
    const RS=lows[lows.length-1], HD=lows[lows.length-2], LS=lows[lows.length-3];
    const T1=highs.filter(s=>s.i>LS.i&&s.i<HD.i).sort((a,b)=>b.p-a.p)[0];
    const T2=highs.filter(s=>s.i>HD.i&&s.i<RS.i).sort((a,b)=>b.p-a.p)[0];
    const bf=highs.filter(s=>s.i<LS.i).slice(-1)[0];
    if(T1&&T2&&bf){
      const neckAvg=(T1.p+T2.p)/2, height=neckAvg-HD.p;
      const nl=i=>T1.p+(T2.p-T1.p)*(i-T1.i)/(T2.i-T1.i);
      const ratio=(HD.i-LS.i)/Math.max(1,RS.i-HD.i);
      if(HD.p<LS.p-0.5*A && HD.p<RS.p-0.5*A && Math.abs(LS.p-RS.p)<=0.35*height && height>=1.5*A &&
         neckAvg-RS.p>=0.8*A && ratio>=0.4 && ratio<=2.5 && RS.i-LS.i<=150 && bf.p-LS.p>=1.5*A &&
         Math.abs(T2.p-T1.p)<=0.6*height && j-RS.i<=45){
        let minAfter=Infinity, br=-1;
        for(let q=RS.i+1;q<N;q++){ minAfter=Math.min(minAfter,l[q]); if(br<0&&c[q]>nl(q)+0.1*A) br=q; }
        if(br>=j-1 && c[j]>nl(j)+0.1*A && c[j]-nl(j)<=1.0*A && minAfter>=RS.p-0.3*A){
          const entry=c[j];
          const sl=Math.max(RS.p-0.3*A, nl(j)-Math.min(Math.max(0.5*height,0.8*A),2.5*A));
          let bonus=0;
          if(Math.abs(LS.p-RS.p)<=0.2*height) bonus+=6;
          if(Math.abs(T2.p-T1.p)<=0.2*height) bonus+=4;
          if((nl(j)+height-entry)>=1.5*(entry-sl)) bonus+=6;
          finish('hs',62,entry,sl,HD.p,
            {lines:[{i1:T1.i,p1:T1.p,i2:j,p2:nl(j)}],points:[{i:LS.i,p:LS.p},{i:HD.i,p:HD.p},{i:RS.i,p:RS.p}]},
            [NM.hs+', head near '+px(HD.p)+', neckline broken'],bonus);
        }
      }
    }
  }

  /* 4) support-zone rejection: price dips into a proven zone and closes back out of it */
  {
    let best=null;
    for(const z of zones){
      if(z.touches<2||z.lastI>j-4) continue;
      if(!(l[j]<=z.top+0.1*A && l[j]>=z.bottom-0.8*A)) continue;
      if(!(c[j]>=z.top && c[j]>o[j])) continue;
      let came=false;
      for(let q=Math.max(0,j-14);q<j;q++){ if(h[q]>z.top+0.5*A){ came=true; break; } }
      if(!came) continue;
      const eng=j>0&&c[j-1]<o[j-1]&&c[j]>=o[j-1]&&o[j]<=c[j-1];
      if(!(lowWick>=0.4||eng)) continue;
      if(!best||z.touches>best.touches) best=z;
    }
    if(best){
      const entry=c[j], sl=Math.min(l[j],best.bottom)-0.35*A;
      let bonus=0;
      if(best.touches>=3) bonus+=8;
      if(lowWick>=0.5) bonus+=4;
      finish('zone',48,entry,sl,best.bottom,
        {zone:{bottom:best.bottom,top:best.top},points:[{i:j,p:l[j]}]},
        [(sg>0?'Support':'Resistance')+' zone '+(sg>0?px(best.bottom)+' - '+px(best.top):px(best.top)+' - '+px(best.bottom))+' ('+best.touches+' touches) held and price closed back out of it'],bonus);
    }
  }

  return {setups:raw,ctx:{A,sw,st,zones,fvgs}};
}
// bring a setup found in the mirrored market back to real prices
function unm(s,sg){
  const m=v=>sg*v;
  const d=s.draw||{};
  return Object.assign({},s,{
    dir:sg,entry:m(s.entry),sl:m(s.sl),level:m(s.level),
    draw:{
      lines:(d.lines||[]).map(x=>({i1:x.i1,p1:m(x.p1),i2:x.i2,p2:m(x.p2)})),
      points:(d.points||[]).map(x=>({i:x.i,p:m(x.p)})),
      zone:d.zone?(sg>0?{bottom:d.zone.bottom,top:d.zone.top}:{bottom:-d.zone.top,top:-d.zone.bottom}):null
    }
  });
}

/* ---------- higher timeframe: just its market structure ---------- */
function htfTrend(cs){
  if(!cs||cs.length<80) return null;
  const x=cs.length>400?cs.slice(-400):cs;
  const h=x.map(k=>k.h), l=x.map(k=>k.l), c=x.map(k=>k.c);
  const atr=atrCalc(h,l,c,14), A=last(atr);
  if(!(A>0)) return null;
  const sw=zigzag(h,l,atr,A,3,1.2), st=structure(sw,last(c),A);
  return {dir:st.dir,label:st.dir>0?'Bullish':st.dir<0?'Bearish':'Ranging',detail:st.label};
}

/* ---------- main analysis: closed candles only ---------- */
function analyze(p){
  let cs=p.candles;
  if(cs.length>400) cs=cs.slice(-400);
  const N=cs.length;
  if(N<90) return {error:'Not enough candles ('+N+'). Need at least 90.'};
  const j=N-1;
  const o=cs.map(k=>k.o), h=cs.map(k=>k.h), l=cs.map(k=>k.l), c=cs.map(k=>k.c);
  const ht=htfTrend(p.htf), htfDir=ht?ht.dir:0;
  const Lr=longSetups(cs,htfDir,1);
  if(!Lr.ctx) return {error:'Price data looks flat (ATR is zero). The market may be closed.'};
  const Sr=longSetups(negate(cs),-htfDir,-1);
  const A=Lr.ctx.A;
  const price=isNum(p.live)?p.live:c[j];
  const all=[...Lr.setups.map(s=>unm(s,1)), ...Sr.setups.map(s=>unm(s,-1))];

  const ageMs=p.now-(cs[j].t+p.ms), stale=ageMs>3*p.ms;
  const gates=[];
  if(stale) gates.push('Data looks stale (last closed candle is '+Math.round(ageMs/60000)+' min old). The market may be closed.');

  const good=all.filter(s=>!s.blocks.length&&s.score>=THRESH).sort((a,b)=>b.score-a.score);
  let pick=null;
  if(good.length){
    pick=good[0];
    const rival=good.find(s=>s.dir!==pick.dir&&s.score>pick.score-10);
    if(rival){ gates.push('A buy setup and a sell setup are both present. Conflicting, so no trade.'); pick=null; }
  } else {
    const cand=all.slice().sort((a,b)=>b.score-a.score)[0];
    if(cand){
      cand.blocks.forEach(b=>gates.push(cand.name+': '+b));
      if(!cand.blocks.length) gates.push(cand.name+' found, but its score ('+cand.score+') is below the '+THRESH+' needed for a signal.');
    } else gates.push('No pattern, retest or zone reaction on the last closed candle.');
  }
  if(pick&&Math.abs(price-pick.entry)>0.5*A){ gates.push('Price has already moved '+(Math.abs(price-pick.entry)/A).toFixed(1)+' ATR away from the setup candle.'); pick=null; }
  if(stale) pick=null;

  const signal=pick?(pick.dir>0?'BUY':'SELL'):'NO TRADE';
  const direction=pick?pick.dir:0;
  let plan=null;
  if(pick){
    const entry=price, risk=Math.abs(entry-pick.sl);
    plan={entry,sl:pick.sl,tp1:entry+direction*risk*1.5,tp2:entry+direction*risk*2.5,risk,slPct:risk/entry*100};
  }
  const score=pick?pick.score:(all.length?all.slice().sort((a,b)=>b.score-a.score)[0].score:0);

  // context shown to the user (real, un-mirrored prices)
  const zonesD=Lr.ctx.zones.map(z=>{
    const inside=price>=z.bottom&&price<=z.top;
    const type=inside?'inside':(z.top<price?'support':'resistance');
    const dist=inside?0:(type==='support'?price-z.top:z.bottom-price);
    return {type,bottom:z.bottom,top:z.top,touches:z.touches,dist:dist/A};
  }).sort((a,b)=>a.dist-b.dist).slice(0,8);
  const fvgsD=Lr.ctx.fvgs.map(f=>({type:f.type,top:f.top,bottom:f.bottom,i:f.i,
    d:(price>f.top?price-f.top:(price<f.bottom?f.bottom-price:0))/A})).sort((a,b)=>a.d-b.d).slice(0,4);
  const W=80, s0=Math.max(0,N-W);
  const dr=pick?pick.draw:null;
  const chart={o:o.slice(s0),h:h.slice(s0),l:l.slice(s0),c:c.slice(s0),zones:zonesD,
    fvgs:fvgsD.map(f=>({type:f.type,top:f.top,bottom:f.bottom,i:f.i-s0})),
    draw:dr?{lines:dr.lines.map(x=>({i1:x.i1-s0,p1:x.p1,i2:x.i2-s0,p2:x.p2})),points:dr.points.map(x=>({i:x.i-s0,p:x.p})),zone:dr.zone}:null};
  const st=Lr.ctx.st;
  return {symbol:p.symbol,tf:p.tf,market:p.market,price,lastT:cs[j].t,ageMs,stale,atr:A,
    trend:{dir:st.dir,label:st.label,rangeHigh:st.rangeHigh,rangeLow:st.rangeLow},
    htf:ht?{dir:ht.dir,label:ht.label,tf:p.htfTf}:null,
    signal,direction,score,grade:pick?(pick.score>=80?'Strong':'Moderate'):'',
    setup:pick?{name:pick.name,kind:pick.kind,notes:pick.notes}:null,
    gates,plan,zones:zonesD,fvgs:fvgsD,chart};
}

/* ---------- backtest: replay history candle by candle, exactly as the live bot would have seen it ---------- */
function simulateTrade(cs,t,dir,sl,tp1,maxBars){
  const entry=cs[t].c, risk=Math.abs(entry-sl);
  if(!(risk>0)) return null;
  const end=Math.min(cs.length-1,t+maxBars);
  if(end<=t) return null;
  for(let j=t+1;j<=end;j++){
    const hitSL=dir>0?cs[j].l<=sl:cs[j].h>=sl;
    const hitTP=dir>0?cs[j].h>=tp1:cs[j].l<=tp1;
    if(hitSL) return {outcome:'SL',R:-1,bars:j-t};            // if both happen in one candle, assume the stop came first (worst case)
    if(hitTP) return {outcome:'TP',R:Math.abs(tp1-entry)/risk,bars:j-t};
  }
  return {outcome:end-t>=maxBars?'TIMEOUT':'OPEN',R:(cs[end].c-entry)*dir/risk,bars:end-t};
}
function backtest(cs,htfCs,tf,market,symbol,opts){
  const o=Object.assign({start:120,maxBars:48,gap:8},opts||{});
  const tfo=TF[tf], ms=tfo.ms, hms=tfo.htf?TF[tfo.htf].ms:0;
  const trades=[]; let lastDir=0,lastT=-1e9;
  const from=Math.max(100,Math.min(o.start,cs.length-70));
  for(let t=from;t<cs.length-1;t++){
    const now=cs[t].t+ms+20000;
    const hs=htfCs?htfCs.filter(k=>k.t+hms<=now):null;
    const r=analyze({candles:cs.slice(Math.max(0,t+1-400),t+1),live:cs[t].c,htf:hs,htfTf:tfo.htf,ms,now,market,symbol,tf});
    if(r.error||r.signal==='NO TRADE'||!r.plan) continue;
    if(r.direction===lastDir && t-lastT<=o.gap) continue;     // same rule as the live scanner: no repeat of the same signal within 8 candles
    lastDir=r.direction; lastT=t;
    const s=simulateTrade(cs,t,r.direction,r.plan.sl,r.plan.tp1,o.maxBars);
    if(!s) continue;
    trades.push({t:cs[t].t,dir:r.direction,entry:r.plan.entry,sl:r.plan.sl,tp1:r.plan.tp1,score:r.score,setup:r.setup.name,outcome:s.outcome,R:s.R,bars:s.bars});
  }
  return trades;
}
function btStats(trades){
  const w=trades.filter(x=>x.outcome==='TP').length, l=trades.filter(x=>x.outcome==='SL').length, o=trades.length-w-l;
  const totR=trades.reduce((a,x)=>a+x.R,0);
  return {n:trades.length,w,l,o,wr:(w+l)?w/(w+l)*100:null,avgR:trades.length?totR/trades.length:0,totR};
}

/* ================================================================
   Scanner part: data loading, Telegram alerts, de-duplication
   ================================================================ */
import fs from 'node:fs';

const TOKEN = process.env.TELEGRAM_BOT_TOKEN || '';
const CHAT = process.env.TELEGRAM_CHAT_ID || '';
const TDKEY = process.env.TWELVEDATA_KEY || '';
const TEST_MODE = String(process.env.TEST_MODE || '') === 'true';
const TIMEFRAMES = (process.env.TIMEFRAMES || '15m,1h,4h').split(',').map(s => s.trim()).filter(x => TF[x]);
const MARKETS = (process.env.MARKETS || 'forex,crypto,synth').split(',').map(s => s.trim());
const STATE_FILE = 'state.json';
const SETTLE_MS = 20000;      // wait after a candle closes before reading it
const REPEAT_CANDLES = 8;     // never repeat the same signal within this many candles
const RETRY_MS = 15 * 60000;  // after a data failure, wait before retrying that pair

const FOREX = [
  {s:'XAUUSD',n:'Gold (XAU/USD)',dv:'frxXAUUSD',y:['XAUUSD=X','GC=F'],td:'XAU/USD'},
  {s:'XAGUSD',n:'Silver (XAG/USD)',dv:'frxXAGUSD',y:['XAGUSD=X','SI=F'],td:'XAG/USD'},
  {s:'EURUSD',n:'EUR/USD',dv:'frxEURUSD',y:['EURUSD=X'],td:'EUR/USD'},
  {s:'GBPUSD',n:'GBP/USD',dv:'frxGBPUSD',y:['GBPUSD=X'],td:'GBP/USD'},
  {s:'USDJPY',n:'USD/JPY',dv:'frxUSDJPY',y:['JPY=X'],td:'USD/JPY'},
  {s:'AUDUSD',n:'AUD/USD',dv:'frxAUDUSD',y:['AUDUSD=X'],td:'AUD/USD'},
  {s:'NZDUSD',n:'NZD/USD',dv:'frxNZDUSD',y:['NZDUSD=X'],td:'NZD/USD'},
  {s:'USDCAD',n:'USD/CAD',dv:'frxUSDCAD',y:['CAD=X'],td:'USD/CAD'},
  {s:'USDCHF',n:'USD/CHF',dv:'frxUSDCHF',y:['CHF=X'],td:'USD/CHF'},
  {s:'EURNZD',n:'EUR/NZD',dv:'frxEURNZD',y:['EURNZD=X'],td:'EUR/NZD'},
  {s:'EURGBP',n:'EUR/GBP',dv:'frxEURGBP',y:['EURGBP=X'],td:'EUR/GBP'},
  {s:'EURJPY',n:'EUR/JPY',dv:'frxEURJPY',y:['EURJPY=X'],td:'EUR/JPY'},
  {s:'GBPJPY',n:'GBP/JPY',dv:'frxGBPJPY',y:['GBPJPY=X'],td:'GBP/JPY'},
  {s:'AUDJPY',n:'AUD/JPY',dv:'frxAUDJPY',y:['AUDJPY=X'],td:'AUD/JPY'}
];
const CRYPTO = [
  {s:'BTCUSDT',n:'BTC/USD',dv:'cryBTCUSD'},
  {s:'ETHUSDT',n:'ETH/USD',dv:'cryETHUSD'},
  {s:'SOLUSDT',n:'SOL/USD'},
  {s:'XRPUSDT',n:'XRP/USD'},
  {s:'LTCUSDT',n:'LTC/USD',dv:'cryLTCUSD'}
];
const SYNTH = [
  {s:'R_10',n:'Volatility 10'},{s:'R_25',n:'Volatility 25'},{s:'R_75',n:'Volatility 75'},
  {s:'R_100',n:'Volatility 100'},{s:'stpRNG',n:'Step Index'}
];
const LISTS = {forex: FOREX, crypto: CRYPTO, synth: SYNTH};
const nameOf = (mk, s) => ((LISTS[mk] || []).find(x => x.s === s) || {n: s}).n;
const BYBIT = {'5m':'5','15m':'15','1h':'60','4h':'240','1d':'D'};
const OKX = {'5m':'5m','15m':'15m','1h':'1H','4h':'4H','1d':'1D'};
const TDI = {'5m':'5min','15m':'15min','1h':'1h','4h':'4h','1d':'1day'};
const YAHOO = {
  '5m':{iv:'5m',range:'5d'}, '15m':{iv:'15m',range:'10d'}, '1h':{iv:'60m',range:'1mo'},
  '4h':{iv:'60m',range:'3mo',rs:14400000}, '1d':{iv:'1d',range:'2y'}
};
const DERIV_GRAN = {'5m':300,'15m':900,'1h':3600,'4h':14400,'1d':86400};
const UA = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36';

/* ---------- network helpers ---------- */
async function getJSON(url, ms = 10000, headers = {}) {
  const r = await fetch(url, {signal: AbortSignal.timeout(ms), headers});
  if (!r.ok) throw new Error('HTTP ' + r.status);
  return r.json();
}

function derivCandles(symbol, tf, count) {
  return new Promise((resolve, reject) => {
    let ws = null, done = false, timer = null;
    const fin = (fn, v) => { if (done) return; done = true; clearTimeout(timer); try { ws && ws.close(); } catch (e) {} fn(v); };
    timer = setTimeout(() => fin(reject, new Error('timeout')), 14000);
    try { ws = new WebSocket('wss://ws.derivws.com/websockets/v3?app_id=1089'); } catch (e) { return fin(reject, e); }
    ws.addEventListener('open', () => ws.send(JSON.stringify({
      ticks_history: symbol, adjust_start_time: 1, count: count || 500, end: 'latest', style: 'candles', granularity: DERIV_GRAN[tf]
    })));
    ws.addEventListener('message', ev => {
      let j; try { j = JSON.parse(ev.data); } catch (e) { return; }
      if (j.error) return fin(reject, new Error(j.error.message || 'Deriv error'));
      if (j.candles) { try { fin(resolve, clean(parseDeriv(j))); } catch (e) { fin(reject, e); } }
    });
    ws.addEventListener('error', () => fin(reject, new Error('connection failed')));
    ws.addEventListener('close', () => fin(reject, new Error('connection closed')));
  });
}

async function getCandles(market, symbol, tf) {
  const errs = [];
  const item = (LISTS[market] || []).find(x => x.s === symbol) || {};
  const viaDeriv = async sym => {
    const cs = await derivCandles(sym, tf, 500);
    if (cs.length < 90) throw new Error('too few candles (' + cs.length + ')');
    return {candles: cs, source: 'Deriv'};
  };
  if (market === 'synth') return viaDeriv(symbol);
  if (market === 'forex') {
    try { return await viaDeriv(item.dv); } catch (e) { errs.push('Deriv: ' + e.message); }
    if (TDKEY) {
      try {
        const u = `https://api.twelvedata.com/time_series?symbol=${encodeURIComponent(item.td)}&interval=${TDI[tf]}&outputsize=500&order=asc&timezone=UTC&apikey=${encodeURIComponent(TDKEY)}`;
        const cs = clean(parseTD(await getJSON(u, 10000)));
        if (cs.length >= 90) return {candles: cs, source: 'Twelve Data'};
        errs.push('TwelveData: too few candles');
      } catch (e) { errs.push('TwelveData: ' + e.message); }
    }
    const y = YAHOO[tf];
    for (const tk of item.y) {
      for (const host of ['query1', 'query2']) {
        try {
          const u = `https://${host}.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(tk)}?interval=${y.iv}&range=${y.range}&includePrePost=false`;
          let cs = clean(parseYahoo(await getJSON(u, 10000, {'User-Agent': UA, 'Accept': 'application/json'})));
          if (y.rs) cs = resample(cs, y.rs);
          if (cs.length >= 90) return {candles: cs, source: 'Yahoo ' + tk};
          errs.push('Yahoo ' + tk + ': too few candles');
        } catch (e) { errs.push('Yahoo ' + tk + ' ' + host + ': ' + e.message); }
      }
    }
    throw new Error(errs.join(' | '));
  }
  // crypto: GitHub's servers are in the US where binance.com is blocked, so the mirror and OKX come first
  const q = base => `${base}?symbol=${symbol}&interval=${tf}&limit=500`;
  const ex = [
    ['Binance mirror', q('https://data-api.binance.vision/api/v3/klines'), parseBinance],
    ['OKX', `https://www.okx.com/api/v5/market/candles?instId=${symbol.replace('USDT', '-USDT')}&bar=${OKX[tf]}&limit=300`, parseOKX],
    ['Bybit', `https://api.bybit.com/v5/market/kline?category=spot&symbol=${symbol}&interval=${BYBIT[tf]}&limit=500`, parseBybit],
    ['Binance', q('https://api.binance.com/api/v3/klines'), parseBinance]
  ];
  for (const [name, url, parse] of ex) {
    try {
      const cs = clean(parse(await getJSON(url, 9000, {'User-Agent': UA})));
      if (cs.length >= 90) return {candles: cs, source: name};
      errs.push(name + ': too few candles');
    } catch (e) { errs.push(name + ': ' + e.message); }
  }
  if (item.dv) {
    try { return await viaDeriv(item.dv); } catch (e) { errs.push('Deriv: ' + e.message); }
  }
  throw new Error(errs.join(' | '));
}

// one download per pair+timeframe per run (a 15m job and a 1h job share the same 1h candles)
const cache = new Map();
function cached(mk, symbol, tf) {
  const k = mk + '|' + symbol + '|' + tf;
  if (!cache.has(k)) cache.set(k, getCandles(mk, symbol, tf));
  return cache.get(k);
}

async function analyzeJob(j) {
  const tfo = TF[j.tf];
  const [main, htf] = await Promise.all([
    cached(j.mk, j.symbol, j.tf),
    tfo.htf ? cached(j.mk, j.symbol, tfo.htf).catch(() => null) : Promise.resolve(null)
  ]);
  const now = Date.now();
  const closed = main.candles.filter(k => k.t + tfo.ms <= now);
  const live = main.candles.length ? last(main.candles).c : null;
  let htfClosed = null;
  if (htf) { const hm = TF[tfo.htf].ms; htfClosed = htf.candles.filter(k => k.t + hm <= now); }
  const r = analyze({candles: closed, live, htf: htfClosed, htfTf: tfo.htf, ms: tfo.ms, now, market: j.mk, symbol: j.symbol, tf: j.tf});
  if (!r.error) r.source = main.source;
  return r;
}

/* ---------- state ---------- */
function loadState() {
  try {
    const s = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    return {done: s.done || {}, alerts: s.alerts || {}, retry: s.retry || {}};
  } catch (e) { return {done: {}, alerts: {}, retry: {}}; }
}
function saveState(s) { fs.writeFileSync(STATE_FILE, JSON.stringify(s, null, 1)); }

/* ---------- Telegram ---------- */
async function tg(text) {
  if (!TOKEN || !CHAT) { console.log('[no Telegram secrets, printing instead]\n' + text + '\n'); return false; }
  try {
    const r = await fetch(`https://api.telegram.org/bot${TOKEN}/sendMessage`, {
      method: 'POST', headers: {'content-type': 'application/json'},
      body: JSON.stringify({chat_id: CHAT, text, disable_web_page_preview: true}),
      signal: AbortSignal.timeout(15000)
    });
    if (!r.ok) { console.log('Telegram error', r.status, await r.text()); return false; }
    return true;
  } catch (e) { console.log('Telegram error', e.message); return false; }
}

const wat = t => new Date(t).toLocaleString('en-GB', {timeZone: 'Africa/Lagos', day: '2-digit', month: 'short', hour: '2-digit', minute: '2-digit', hour12: false}) + ' WAT';

function buildMessage(j, r) {
  const p = r.plan, d = r.direction;
  const ahead = r.zones.filter(z => z.type === (d > 0 ? 'resistance' : 'support')).sort((a, b) => a.dist - b.dist)[0];
  const lines = [
    (d > 0 ? '🟢 BUY' : '🔴 SELL') + '  ' + nameOf(j.mk, j.symbol) + ' · ' + j.tf,
    'Setup: ' + r.setup.name,
    'Strength: ' + r.grade + ' (score ' + r.score + '/100)',
    '',
    'Entry: ' + fmt(p.entry),
    'Stop loss: ' + fmt(p.sl) + ' (' + p.slPct.toFixed(2) + '%)',
    'TP1: ' + fmt(p.tp1) + ' (1.5R)',
    'TP2: ' + fmt(p.tp2) + ' (2.5R)',
    '',
    'Why:',
    ...r.setup.notes.slice(0, 4).map(n => '• ' + n),
    '',
    'Market: ' + r.trend.label,
    r.htf ? 'Higher TF (' + r.htf.tf + '): ' + r.htf.label : 'Higher TF: n/a',
    ahead ? 'Next ' + (d > 0 ? 'resistance' : 'support') + ' zone: ' + fmt(ahead.bottom) + ' - ' + fmt(ahead.top) + ' (' + ahead.dist.toFixed(1) + ' ATR away)' : 'No ' + (d > 0 ? 'resistance' : 'support') + ' zone ahead in view',
    'Candle closed: ' + wat(r.lastT + TF[j.tf].ms),
    '',
    'Not financial advice. Risk 1% or less per trade, always use the stop loss.'
  ];
  return lines.join('\n');
}

const maxAgeMs = tf => Math.min(TF[tf].ms * 0.9, 25 * 60000);
const forexClosed = now => { const d = new Date(now), day = d.getUTCDay(), h = d.getUTCHours(); return day === 6 || (day === 5 && h >= 22) || (day === 0 && h < 22); };

/* ---------- main ---------- */
async function main() {
  if (TEST_MODE) {
    const ok = await tg('✅ ProEdge scanner is connected.\nYou will get a message here when a BUY or SELL setup appears.');
    console.log(ok ? 'Test message sent.' : 'Test message NOT sent. Check the TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID secrets.');
    return;
  }
  const state = loadState();
  const now = Date.now();
  const jobs = [];
  for (const mk of MARKETS) {
    if (!LISTS[mk]) continue;
    if (mk === 'forex' && forexClosed(now)) { console.log('Forex and metals market closed, skipping.'); continue; }
    for (const item of LISTS[mk]) for (const tf of TIMEFRAMES) {
      const symbol = item.s, ms = TF[tf].ms, boundary = Math.floor(now / ms) * ms, key = mk + '|' + symbol + '|' + tf;
      if (state.done[key] === boundary) continue;      // already analysed this candle
      if (now - boundary < SETTLE_MS) continue;        // candle only just closed, wait a moment
      if (state.retry[key] && now < state.retry[key]) continue;
      jobs.push({mk, symbol, tf, key, boundary});
    }
  }
  console.log('Pairs to analyse this run: ' + jobs.length);
  let i = 0, sent = 0, errors = 0, signals = 0;
  const worker = async () => {
    while (i < jobs.length) {
      const j = jobs[i++];
      try {
        const r = await analyzeJob(j);
        delete state.retry[j.key];
        state.done[j.key] = j.boundary;
        if (r.error) { console.log('· ' + j.key + ': ' + r.error); continue; }
        if (r.signal === 'NO TRADE') continue;
        signals++;
        if (r.ageMs > maxAgeMs(j.tf)) { console.log('· ' + j.key + ': ' + r.signal + ' but candle is old, skipped'); continue; }
        const prev = state.alerts[j.key];
        if (prev && prev.signal === r.signal && (r.lastT - prev.t) <= REPEAT_CANDLES * TF[j.tf].ms) continue;
        if (await tg(buildMessage(j, r))) { state.alerts[j.key] = {signal: r.signal, t: r.lastT}; sent++; console.log('✓ alert sent: ' + j.key + ' ' + r.signal + ' (' + r.setup.name + ')'); }
      } catch (e) {
        errors++; state.retry[j.key] = Date.now() + RETRY_MS;
        console.log('✗ ' + j.key + ': ' + String(e.message).slice(0, 300));
      }
    }
  };
  await Promise.all(Array.from({length: 3}, worker));
  saveState(state);
  console.log(`Done. analysed=${jobs.length} signals=${signals} alerts_sent=${sent} errors=${errors}`);
}

export const done = main().catch(e => { console.error(e); process.exitCode = 1; });
