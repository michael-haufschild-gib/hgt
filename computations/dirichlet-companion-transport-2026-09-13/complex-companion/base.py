import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import fold as f
import analytic as a
SPEC=json.loads(Path('spec.json').read_text());P=json.loads(Path('parameters.json').read_text())
DEAD=float(os.environ['CAMPAIGN_DEADLINE'])
def setup(dps):
 m.mp.dps=dps;params=P['5']['70' if dps==50 else '120' if dps==100 else '180']
 data,pieces=f.evaluator(5,[-1,1],params)
 hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']]
 aa=-1/m.sqrt(2);bb=-aa
 def F(z,lam,kap):
  if time.monotonic()>DEAD-6:raise TimeoutError('family deadline')
  if not 2<m.re(z)<36 or abs(m.im(z))>3:raise ValueError('root left finite domain')
  weights={0:m.mpf(1)}
  for h,c in zip(hs,[lam*aa,lam*bb,kap*lam*lam*aa*bb]):
   for k,v in h.items():
    for kk in [k,-k]:weights[kk]=weights.get(kk,0)+c*v/2
  return m.exp(m.pi*z/4)*sum(v*a.carrier(z+k,5) for k,v in weights.items() if v)
 return data,F,params
def chart(job):
 offset,n=job;start=time.monotonic();data,F,_=setup(50)
 tc=m.mpf(SPEC['triple']['t']);lo=tc+m.mpf(offset);end=m.mpf(SPEC['boundaries'][-1]['t']);entry=m.mpf(SPEC['boundaries'][0]['t'])
 grid=sorted(set([lo+(end-lo)*j/n for j in range(n+1)]+[entry]));z=tc-2*m.mpf(offset)
 row=dict(offset=offset,n=n,points=[],endpoints=[])
 try:
  for t in grid:
   v=data(t);lam,kap=v['lam'],v['kappa']
   if not 0<lam<m.mpf('.08') or not 0<kap<m.mpf('1.4') or not v['positivity_bound']<1:raise ValueError('chart left admitted source region')
   z1=m.findroot(lambda x:F(x,lam,kap)/(x-t)**2,(z,z+m.mpf('1e-4')),tol=m.mpf('1e-38'),maxsteps=20)
   if abs(z1-t)<m.mpf('1e-4') or abs(z1-z)>m.mpf('.35') or abs(z1.imag)>m.mpf('1e-25'):raise ValueError('companion separation/jump/reality check')
   z=m.re(z1);point=dict(chart_t=str(t),lam=str(lam),kappa=str(kap),t=str(z),residual=str(abs(F(z,lam,kap))),separation=str(abs(z-t)),bound=str(v['positivity_bound']))
   row['points'].append(point)
   if t==entry or t==end:row['endpoints'].append(dict(which='entry' if t==entry else 'return',**point))
   Path('partial-chart-'+offset+'-'+str(n)+'.json').write_text(json.dumps(row))
  row['complete']=True
 except Exception as ex:row['error']=str(ex)[:220]
 row['seconds']=time.monotonic()-start;return row
def ancestry(job):
 point,n=job;start=time.monotonic();_,F,_=setup(50);z=m.mpf(point['t']);lam0=m.mpf(point['lam']);r=m.mpf(1);step=1/m.mpf(n);maximum=step
 row=dict(which=point['which'],n=n,seed=point,points=[])
 try:
  for attempt in range(250):
   row['points'].append(dict(ratio=str(r),t=a.enc(z),residual=str(abs(F(z,r*lam0,1)))))
   if r==0:row['complete']=True;break
   rr=max(0,r-step)
   try:
    zz=m.findroot(lambda t:F(t,rr*lam0,1),(z,z+m.mpf('1e-4')),tol=m.mpf('1e-39'),maxsteps=18)
    if abs(zz-z)>m.mpf('.25') or abs(zz.imag)>m.mpf('1e-20'):raise ValueError('companion ancestry jump/nonreal')
   except (ValueError,ZeroDivisionError):
    step/=2
    if step<m.mpf('1e-6'):raise ValueError('unresolved companion ancestry collision')
    continue
   r,z=rr,m.re(zz);step=min(maximum,step*m.mpf('1.25'))
   Path('partial-ancestry-'+point['which']+'-'+str(n)+'.json').write_text(json.dumps(row))
  row['t']=str(z);row['final_ratio']=str(r)
 except Exception as ex:row['error']=str(ex)[:220]
 row['seconds']=time.monotonic()-start;return row
def refine(job):
 row,dps=job;start=time.monotonic();_,F,_=setup(dps)
 out=dict(row=row,dps=dps)
 try:
  lam=m.mpf(row['lam']);kap=m.mpf(row['kappa']);z=m.mpf(row['t'])
  z=m.findroot(lambda t:F(t,lam,kap),(z,z+m.mpf('1e-8')),tol=m.mpf(10)**(-dps+12),maxsteps=20)
  out.update(t=a.enc(z),residual=str(abs(F(z,lam,kap))),shift=str(abs(z-m.mpf(row['t']))))
 except Exception as ex:out['error']=str(ex)[:220]
 out['seconds']=time.monotonic()-start;return out
def source(row):
 start=time.monotonic();_,F,params=setup(190);lam=m.mpf(row['row']['lam']);kap=m.mpf(row['row']['kappa']);z=a.dec(row['t'])
 hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']];aa=-1/m.sqrt(2);bb=-aa
 def kernel(x):
  y=m.exp(2*x);return 2*m.exp(x/2)*sum(f.c.CHARS[5][n%5]*m.exp(-m.pi*n*n*y/5) for n in range(1,41) if f.c.CHARS[5][n%5])
 def mult(x):
  h=[sum(v*m.cos(k*x) for k,v in hh.items()) for hh in hs];return 1+lam*(aa*h[0]+bb*h[1])+kap*lam*lam*aa*bb*h[2]
 checks=[]
 for off in [m.mpf(0),m.mpf('.125')]:
  t=z+off
  val=2*m.quad(lambda x:kernel(x)*mult(x)*m.cos(t*x),[0,.25,.5,.75,1,1.5,2,3,4])*m.exp(m.pi*t/4)
  checks.append(dict(offset=str(off),derivative=0,error=str(abs(val-F(t,lam,kap))),value=a.enc(val)))
  derivative=-2*m.quad(lambda x:x*kernel(x)*mult(x)*m.sin(t*x),[0,.25,.5,.75,1,1.5,2,3,4])*m.exp(m.pi*t/4)
  expected=m.diff(lambda u:F(u,lam,kap),t)-m.pi*F(t,lam,kap)/4
  checks.append(dict(offset=str(off),derivative=1,error=str(abs(derivative-expected)),value=a.enc(derivative)))
 return dict(row=row,checks=checks,seconds=time.monotonic()-start)
if __name__=='__main__':
 start=time.monotonic();tracks=[];anc=[];refs=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('chart.jsonl','w',buffering=1) as out:
  for n in [40,80]:
   if n==80:
    estimate=max(r['seconds'] for r in tracks)*2
    admit=estimate<(DEAD-time.monotonic())*.45
    Path('pilot.json').write_text(json.dumps(dict(fine_estimate=estimate,fine_admitted=admit)))
    if not admit:break
   for fut in as_completed([pool.submit(chart,(off,n)) for off in ['.01','.02']]):
    r=fut.result();tracks.append(r);out.write(json.dumps(r)+'\n');print('chart',r['offset'],n,r.get('complete'),r.get('error'),flush=True)
  endpoints={}
  for row in tracks:
   if row.get('complete'):
    for pt in row['endpoints']:endpoints[pt['which']]=pt
  with open('ancestry.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(ancestry,(pt,n)) for pt in endpoints.values() for n in [40,80]]):
    r=fut.result();anc.append(r);out.write(json.dumps(r)+'\n');print('ancestry',r['which'],r['n'],r.get('complete'),r.get('error'),flush=True)
  targets=list(endpoints.values())
  for r in anc:
   if r.get('complete') and r['n']==80:targets.append(dict(which=r['which']+'-original',t=r['t'],lam='0',kappa='1'))
  with open('validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(refine,(r,dps)) for r in targets for dps in [100,160]]):
    r=fut.result();refs.append(r);out.write(json.dumps(r)+'\n');print('refine',r['row']['which'],r['dps'],r.get('error'),flush=True)
  with open('source-validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(source,r) for r in refs if r['dps']==160 and 'error' not in r and not r['row']['which'].endswith('original')]):out.write(json.dumps(fut.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,charts=len(tracks),ancestries=len(anc),refinements=len(refs))))
