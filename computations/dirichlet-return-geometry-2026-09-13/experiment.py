import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import fold as f
P=json.loads(Path('parameters.json').read_text());SPEC=json.loads(Path('spec.json').read_text())
DEAD=float(os.environ['CAMPAIGN_DEADLINE'])

def data(q,direction,dps):
 m.mp.dps=dps;prec='70' if dps==50 else ('120' if dps==100 else '180')
 params=P[str(q)][prec] if q else P[prec]
 raw,pieces=f.evaluator(q,direction,params)
 def get(t):
  if time.monotonic()>DEAD-6:raise TimeoutError('whole family deadline')
  if not 2<t<178:raise ValueError('height outside admitted domain')
  return raw(t)
 return get,pieces,params

def scan(job):
 q,direction,lo,hi,n=job;start=time.monotonic();get,_,_=data(q,direction,50)
 out=dict(q=q,direction=direction,interval=[lo,hi],n=n,grid=[],candidates=[],errors=[])
 try:
  grid=[m.mpf(lo)+(m.mpf(hi)-m.mpf(lo))*j/n for j in range(n+1)];vals=[]
  for t in grid:
   v=get(t);vals.append(v);out['grid'].append(dict(t=str(t),**f.encoded(v,40)))
  for name in ['kappa_prime','F_tt']:
   observable=lambda v:v['F'][2] if name=='F_tt' else v[name]
   for j in range(n):
    if observable(vals[j])*observable(vals[j+1])>=0:continue
    try:
     t=m.findroot(lambda t:observable(get(t)),(grid[j],grid[j+1]),solver='anderson',tol=m.mpf('1e-34'),maxsteps=55)
     v=get(t)
     if not grid[j]<=t<=grid[j+1]:raise ValueError('root left bracket')
     admit=bool(0<v['kappa']<1 and v['lam']>0 and v['positivity_bound']<1 and max(abs(z) for z in v['F'][:2])<m.mpf('1e-25'))
     out['candidates'].append(dict(q=q,direction=direction,monitor=name,t=str(t),admitted=admit,**f.encoded(v,50)))
    except Exception as ex:out['errors'].append(dict(monitor=name,bracket=[str(grid[j]),str(grid[j+1])],error=str(ex)[:160]))
 except Exception as ex:out['error']=str(ex)[:180]
 out['seconds']=time.monotonic()-start;return out

def refine(job):
 r,dps=job;start=time.monotonic();get,pieces,params=data(r['q'],r['direction'],dps)
 out={k:r[k] for k in ['q','direction','monitor']};out['dps']=dps
 try:
  obs=lambda v:v['F'][2] if r['monitor']=='F_tt' else v['kappa_prime'];t0=m.mpf(r['t'])
  t=m.findroot(lambda t:obs(get(t)),(t0-m.mpf('1e-6'),t0+m.mpf('1e-6')),tol=m.mpf(10)**(-dps+14),maxsteps=30)
  if abs(t-t0)>m.mpf('.01'):raise ValueError('refinement changed candidate')
  v=get(t);lam=v['lam'];kap=v['kappa']
  def second(x):
   X,D,W=pieces(x);return X[2]+lam*D[2]+kap*lam*lam*W[2]
  v['F_ttt']=m.diff(second,t)+(-m.pi/4+m.mpf('1.75')*t/(1+t*t))*v['F'][2]
  out.update(t=m.nstr(t,dps),**f.encoded(v,dps))
 except Exception as ex:out['error']=str(ex)[:160]
 out['seconds']=time.monotonic()-start;return out

def source(job):
 row,offset=job;start=time.monotonic();q=row['q'];_,_,params=data(q,row['direction'],190)
 out=f.integral_check((row,params,offset));t=m.mpf(row['t'])+m.mpf(offset);lam=m.mpf(row['lam']);kap=m.mpf(row['kappa'])
 hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']]
 aa,bb=map(m.mpf,row['direction']);nn=m.sqrt(aa*aa+bb*bb);aa/=nn;bb/=nn
 def integrand(x):
  y=m.exp(2*x)
  if q==0:mu=m.exp(x/2)*sum(2*m.pi*(2*m.pi*n**4*y*y-3*n*n*y)*m.exp(-m.pi*n*n*y) for n in range(1,17))
  else:
   parity=1 if q==4 else 0;mu=2*m.exp((parity+m.mpf('.5'))*x)*sum(f.c.CHARS[q][n%q]*n**parity*m.exp(-m.pi*n*n*y/q) for n in range(1,41) if f.c.CHARS[q][n%q])
  h=[sum(v*m.cos(k*x) for k,v in hh.items()) for hh in hs]
  return 2*x**3*mu*(1+lam*(aa*h[0]+bb*h[1])+kap*lam*lam*aa*bb*h[2])*m.sin(t*x)
 actual=m.quad(integrand,[0,.25,.5,.75,1,1.5,2,3,4]);get,pieces,_=data(q,row['direction'],190)
 def second(x):
  X,D,W=pieces(x);return X[2]+lam*D[2]+kap*lam*lam*W[2]
 expected=m.diff(second,t)+(-m.pi/4+m.mpf('1.75')*t/(1+t*t))*second(t)
 scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
 out['F_ttt_integral']=m.nstr(actual/scale,100);out['F_ttt_error']=m.nstr(abs(actual/scale-expected),100)
 out['seconds']=time.monotonic()-start;return out

if __name__=='__main__':
 start=time.monotonic();rows=[];jobs=[]
 for region in SPEC['regions']:
  lo,hi=map(m.mpf,region['interval']);count=region['cells']
  for j in range(count):jobs.append((SPEC['q'],region['direction'],str(lo+(hi-lo)*j/count),str(lo+(hi-lo)*(j+1)/count)))
 with ProcessPoolExecutor(max_workers=14) as pool,open('screen.jsonl','w',buffering=1) as out:
  for stage,n in enumerate([8,16]):
   if stage and max(r['seconds'] for r in rows)*2*max(1,len(jobs)/14)>(DEAD-time.monotonic())*.4:
    Path('pilot.json').write_text(json.dumps(dict(fine_admitted=False)));break
   for fut in as_completed([pool.submit(scan,j+(n,)) for j in jobs]):
    r=fut.result();rows.append(r);out.write(json.dumps(r)+'\n');print('cell',r['interval'],n,'candidates',len(r['candidates']),r.get('error'),flush=True)
   if stage==0:Path('pilot.json').write_text(json.dumps(dict(coarse_seconds=time.monotonic()-start,fine_admitted=True)))
  candidates={}
  for r in rows:
   for c in r['candidates']:
    if c['admitted']:candidates[(tuple(c['direction']),round(float(c['t']),7))]=c
  selected=sorted(candidates.values(),key=lambda r:r['t'])[:12]
  Path('selection.json').write_text(json.dumps(dict(total=len(candidates),selected=selected,cap=12)))
  refs=[]
  with open('validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(refine,(r,dps)) for r in selected for dps in [100,160]]):
    r=fut.result();refs.append(r);out.write(json.dumps(r)+'\n');print('refined',r.get('t','')[:16],r.get('dps'),r.get('error'),flush=True)
  with open('source-validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(source,(r,off)) for r in refs if r.get('dps')==160 and 'error' not in r for off in ['0','.125']]):
    r=fut.result();out.write(json.dumps(r)+'\n');print('source',r['t'][:16],r['offset'],flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,cells=len(rows),candidates=len(candidates),selected=len(selected))))
