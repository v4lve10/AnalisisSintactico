const $=id=>document.getElementById(id);
const esc=s=>s.replace(/[&<>]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;'}[c]));
const KW=new Set(['if','else','while','for','return','print','int','float','string','bool','var','let','true','false']);
const TYPES=['int','float','string','bool','var','let'];
const STARTS=new Set(['if','while','for','return','print',...TYPES]);

/* ---------- Análisis léxico ---------- */
function lex(src){
  const toks=[],errs=[];let i=0,l=1,c=1;
  const adv=n=>{for(let k=0;k<n;k++){if(src[i]==='\n'){l++;c=1}else c++;i++}};
  while(i<src.length){
    const ch=src[i];
    if(/\s/.test(ch)){adv(1);continue}
    if(src.startsWith('//',i)){while(i<src.length&&src[i]!=='\n')adv(1);continue}
    const st={line:l,col:c},rest=src.slice(i);let m;
    const push=type=>{toks.push({type,v:m[0],len:m[0].length,...st});adv(m[0].length)};
    if(m=/^[A-Za-z_]\w*/.exec(rest))push(KW.has(m[0])?'kw':'id');
    else if(m=/^\d+(\.\d+)?/.exec(rest))push('num');
    else if(ch==='"'){m=/^"[^"\n]*"/.exec(rest);if(m)push('str');else{errs.push({...st,len:rest.split('\n')[0].length,msg:'Cadena de texto sin cerrar',exp:'una comilla de cierre «"»',found:'el fin de la línea'});adv(rest.split('\n')[0].length)}}
    else if(m=/^(==|!=|<=|>=|&&|\|\||[+\-*\/%<>=!])/.exec(rest))push('op');
    else if('(){}[];,'.includes(ch)){m=[ch];push('p')}
    else{errs.push({...st,len:1,msg:`Carácter no reconocido «${ch}»`,exp:'un símbolo válido del lenguaje',found:`«${ch}»`});adv(1)}
  }
  return{toks,errs,end:{line:l,col:c}};
}

/* ---------- Análisis sintáctico (descenso recursivo con recuperación) ---------- */
function parse(toks,end){
  let p=0;const errs=[];
  const eof={type:'eof',v:'',line:end.line,col:end.col,len:1};
  const cur=()=>toks[p]||eof;
  const is=v=>{const t=cur();return t.v===v&&t.type!=='str'&&t.type!=='eof'};
  const nd=(l,c=[])=>({l,c}),lf=(k,v)=>nd(`${k}: ${v}`);
  const show=t=>t.type==='eof'?'el fin del código':`«${t.v}»`;
  const err=(at,msg,exp,fnd)=>{throw{line:at.line,col:at.col,len:at.len||1,msg,exp,found:show(fnd||at)}};
  function expect(v,msg,open){
    if(is(v))return toks[p++];
    const c=cur();let m=msg||`Falta «${v}»`;
    if(open)m=`Falta «${v}» para cerrar el «${open.v}» abierto en la línea ${open.line}, columna ${open.col}`;
    if(v===';'&&p>0){const pr=toks[p-1];err({line:pr.line,col:pr.col+pr.len,len:1},m+' al final de la instrucción',`«;»`,c)}
    err(c,m,`«${v}»`,c);
  }
  const LV=[['||'],['&&'],['==','!='],['<','>','<=','>='],['+','-'],['*','/','%']];
  function bin(i){
    if(i===LV.length)return unary();
    let n=bin(i+1);
    while(cur().type==='op'&&LV[i].includes(cur().v)){const o=toks[p++];n=nd('Op '+o.v,[n,bin(i+1)])}
    return n;
  }
  const expr=()=>bin(0);
  function unary(){
    if(cur().type==='op'&&(is('!')||is('-'))){const o=toks[p++];return nd('Unario '+o.v,[unary()])}
    return primary();
  }
  function args(){
    const a=[];
    if(!is(')')){a.push(expr());while(is(',')){p++;a.push(expr())}}
    return nd('Argumentos',a);
  }
  function primary(){
    const t=cur();
    if(t.type==='num')return p++,lf('NUM',t.v);
    if(t.type==='str')return p++,lf('CADENA',t.v);
    if(t.type==='kw'&&(t.v==='true'||t.v==='false'))return p++,lf('BOOL',t.v);
    if(t.type==='id'){
      p++;
      if(is('(')){const o=toks[p++];const a=args();expect(')',null,o);return nd('Llamada',[lf('ID',t.v),a])}
      return lf('ID',t.v);
    }
    if(is('(')){const o=toks[p++];const e=expr();expect(')',null,o);return nd('Paréntesis',[e])}
    if(t.type==='op')err(t,`Operador «${t.v}» inesperado: aquí debía ir un operando, no un operador`,'un número, identificador, cadena o «(»');
    if(t.type==='eof')err(t,'La expresión está incompleta: el código termina antes de tiempo','un operando (número, identificador, cadena o «(»)');
    err(t,`Expresión incompleta o inválida: se encontró ${show(t)} donde debía haber un operando`,'un número, identificador, cadena, «true»/«false» o «(»');
  }
  function decl(){
    const t=toks[p++],id=cur();
    if(id.type!=='id')err(id,`Después del tipo «${t.v}» debe ir el nombre de la variable`,'un identificador');
    p++;
    const ch=[lf('tipo',t.v),lf('ID',id.v)];
    if(is('=')){p++;ch.push(nd('Inicialización',[expr()]))}
    return nd('Declaración',ch);
  }
  function assign(){
    const id=toks[p++];expect('=');
    return nd('Asignación',[lf('ID',id.v),expr()]);
  }
  function simple(){
    const t=cur();
    if(t.type==='kw'&&TYPES.includes(t.v))return decl();
    if(t.type==='id'&&toks[p+1]&&toks[p+1].v==='=')return assign();
    err(t,'La inicialización/actualización del «for» debe ser una declaración o asignación','una declaración o asignación');
  }
  function cond(k){
    p++;
    const o=expect('(',`Falta «(» después de «${k}»`);
    const e=expr();
    expect(')',null,o);
    return e;
  }
  function block(){
    const o=toks[p++],ch=[];
    while(!is('}')&&cur().type!=='eof')safe(()=>ch.push(stmt()));
    if(cur().type==='eof')err(cur(),`Falta «}» para cerrar el bloque abierto en la línea ${o.line}, columna ${o.col}`,'«}»');
    p++;
    return nd('Bloque',ch);
  }
  function stmt(){
    const t=cur();
    if(is('{'))return block();
    if(t.type==='kw'){
      if(TYPES.includes(t.v)){const d=decl();expect(';');return d}
      if(t.v==='if'){const c=cond('if'),th=stmt(),ch=[nd('Condición',[c]),nd('Entonces',[th])];
        if(is('else')){p++;ch.push(nd('Sino',[stmt()]))}return nd('If',ch)}
      if(t.v==='while'){const c=cond('while');return nd('While',[nd('Condición',[c]),nd('Cuerpo',[stmt()])])}
      if(t.v==='for'){
        p++;const o=expect('(','Falta «(» después de «for»');
        const a=simple();expect(';','Falta «;» después de la inicialización del «for»');
        const b=expr();expect(';','Falta «;» después de la condición del «for»');
        const c=simple();expect(')',null,o);
        return nd('For',[nd('Inicio',[a]),nd('Condición',[b]),nd('Paso',[c]),nd('Cuerpo',[stmt()])]);
      }
      if(t.v==='print'){p++;const o=expect('(','Falta «(» después de «print»');const a=args();expect(')',null,o);expect(';');return nd('Print',[a])}
      if(t.v==='return'){p++;const ch=is(';')?[]:[expr()];expect(';');return nd('Return',ch)}
      if(t.v==='else')err(t,'«else» sin un «if» correspondiente','una instrucción');
    }
    if(t.type==='id'){
      const n=toks[p+1];
      if(n&&n.v==='='&&n.type==='op'){const a=assign();expect(';');return a}
      if(n&&n.v==='('){const e=expr();expect(';');return nd('Llamada',e.c)}
      err(n||eof,`Después del identificador «${t.v}» debe ir «=» (asignación) o «(» (llamada)`,'«=» o «(»');
    }
    if(t.v==='}')err(t,'Llave de cierre «}» sin una llave de apertura correspondiente','el inicio de una instrucción');
    if(t.v===')')err(t,'Paréntesis de cierre «)» sin un «(» correspondiente','el inicio de una instrucción');
    err(t,`${show(t)} no puede iniciar una instrucción`,'una declaración, asignación, if, while, for, print, return o bloque');
  }
  function sync(){
    while(cur().type!=='eof'){
      if(is(';')){p++;return}
      if(is('}'))return;
      if(cur().type==='kw'&&STARTS.has(cur().v))return;
      p++;
    }
  }
  function safe(f){
    const s=p;
    try{f()}catch(e){if(!e.msg)throw e;errs.push(e);sync();if(p===s)p++}
  }
  const prog=[];
  while(cur().type!=='eof')safe(()=>prog.push(stmt()));
  return{tree:nd('Programa',prog),errs};
}

/* ---------- Árbol SVG ---------- */
function drawTree(root){
  const all=[];let lx=0;
  (function lay(n,d){
    n.d=d;
    if(!n.c.length)n.x=lx++;
    else{n.c.forEach(c=>lay(c,d+1));n.x=(n.c[0].x+n.c[n.c.length-1].x)/2}
    all.push(n);
  })(root,0);
  const W=118,H=62,maxD=Math.max(...all.map(n=>n.d));
  const wd=n=>Math.max(44,n.l.length*6.7+14);
  let s='';
  const X=n=>n.x*W+W/2,Y=n=>n.d*H+24;
  all.forEach(n=>n.c.forEach(c=>s+=`<line x1="${X(n)}" y1="${Y(n)+12}" x2="${X(c)}" y2="${Y(c)-12}"/>`));
  all.forEach(n=>{const w=wd(n);s+=`<g class="${n.c.length?'n':'l'}"><rect x="${X(n)-w/2}" y="${Y(n)-12}" width="${w}" height="24" rx="5"/><text x="${X(n)}" y="${Y(n)+4}">${esc(n.l)}</text></g>`});
  return`<div class="tree"><svg width="${Math.max(lx,1)*W}" height="${(maxD+1)*H}" role="img" aria-label="Árbol de sintaxis">${s}</svg></div>`;
}

/* ---------- Interfaz ---------- */
function codeView(src,errs){
  const lines=src.split('\n');
  return'<div class="code" id="codeview">'+lines.map((ln,i)=>{
    const es=errs.filter(e=>e.line===i+1).sort((a,b)=>a.col-b.col);
    let h='',pos=0,text=ln;
    es.forEach(e=>{
      const a=Math.max(e.col-1,pos);
      if(a>text.length)text=text.padEnd(a,' ');
      const b=Math.max(a+(e.len||1),a+1);
      if(b>text.length)text=text.padEnd(b,' ');
      h+=esc(text.slice(pos,a))+`<mark>${esc(text.slice(a,b))}</mark>`;pos=b;
    });


    
    h+=esc(text.slice(pos));
    return`<div class="ln${es.length?' hit':''}" id="L${i+1}"><i>${i+1}</i><span>${h}</span></div>`;
  }).join('')+'</div>';
}
function run(){
  const src=$('src').value,out=$('out');
  if(!src.trim()){out.innerHTML='<h2>Resultado</h2><div class="status warn">No hay código para analizar. Escribe o carga un archivo.</div>';return}
  const L=lex(src),P=parse(L.toks,L.end);
  const errs=[...L.errs.map(e=>({...e,kind:'Léxico'})),...P.errs.map(e=>({...e,kind:'Sintáctico'}))].sort((a,b)=>a.line-b.line||a.col-b.col);
  const lines=src.split('\n');
  let h='<h2>Resultado</h2>';
  if(errs.length){
    h+=`<div class="status bad">El código tiene ${errs.length} error${errs.length>1?'es':''}. No se puede generar el árbol de sintaxis.</div>`;
    h+=errs.map(e=>{
      const ln=lines[e.line-1]||'';
      const mark=' '.repeat(Math.max(e.col-1,0))+'^'.repeat(Math.max(e.len||1,1));
      return`<div class="err" data-l="${e.line}"><b>Error ${e.kind.toLowerCase()} · línea ${e.line}, columna ${e.col}</b><div>${esc(e.msg)}.</div><small>Se esperaba: ${esc(e.exp)}. Se encontró: ${esc(e.found)}.</small><code>${esc(ln)}\n${esc(mark)}</code></div>`;
    }).join('');
  }else{
    h+='<div class="status ok">Análisis completo: el código no tiene errores sintácticos.</div>';
  }
  h+='<h2>Código analizado</h2>'+codeView(src,errs);
  if(!errs.length)h+='<h2>Árbol de sintaxis</h2>'+drawTree(P.tree);
  out.innerHTML=h;
  out.querySelectorAll('.err').forEach(el=>el.onclick=()=>{
    const t=$('L'+el.dataset.l);if(t)t.scrollIntoView({block:'center',behavior:'smooth'});
    $('src').focus();
  });
}
$('go').onclick=run;
$('clr').onclick=()=>{$('src').value='';$('out').innerHTML='<h2>Resultado</h2><div class="status warn">Aún no hay análisis. Escribe o carga código y pulsa «Analizar».</div>'};
$('src').addEventListener('keydown',e=>{if(e.key==='Enter'&&(e.ctrlKey||e.metaKey)){e.preventDefault();run()}});
$('file').onchange=e=>{
  const f=e.target.files[0];if(!f)return;
  const r=new FileReader();r.onload=()=>{$('src').value=r.result;run()};r.readAsText(f);e.target.value='';
};
