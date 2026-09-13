import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import fold as f
P=json.loads(Path('parameters.json').read_text());DEAD=float(os.environ['CAMPAIGN_DEADLINE'])
def solve(job):
 t1,t2,dps=job;start=time.monotonic();m.mp.dps=dps;pp=P['5']['70' if dps==50 else '120' if dps==100 else '180'];get,_=f.evaluator(5,[-1,1],pp)
 def data(x):
  if time.monotonic()>DEAD-5:raise TimeoutError('shared family deadline')
  if not 16<x<21:raise ValueError('outside finite solve region')
  return get(x)
 def eq(x,y):
  a,b=data(x),data(y);return a['lam']-b['lam'],a['kappa']-b['kappa']
 def jac(x,y):
  a,b=data(x),data(y);return m.matrix([[a['lambda_prime'],-b['lambda_prime']],[a['kappa_prime'],-b['kappa_prime']]])
 out=dict(seed=[t1,t2],dps=dps)
 try:
  x,y=m.findroot(eq,(m.mpf(t1),m.mpf(t2)),J=jac,tol=m.mpf(10)**(-dps+12),maxsteps=25)
  a,b=data(x),data(y)
  if not m.mpf('19.9')<x<m.mpf('20.3') or not 17<y<m.mpf('18.5'):raise ValueError('intersection left brackets')
  if not 0<a['lam']<m.mpf('.08') or not 0<a['kappa']<m.mpf('1.4') or not a['positivity_bound']<1:raise ValueError('source outside admission')
  out.update(t1=str(x),t2=str(y),q=5,direction=[-1,1],lam=str(a['lam']),kappa=str(a['kappa']),bound=str(a['positivity_bound']),first=f.encoded(a,dps),second=f.encoded(b,dps),residual=str(max(abs(v) for v in eq(x,y))),chart_jacobian=str(m.det(jac(x,y))))
 except Exception as ex:out['error']=str(ex)[:250]
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 start=time.monotonic();screens=[];refs=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('screen.jsonl','w',buffering=1) as out:
  for fut in as_completed([pool.submit(solve,(x,y,50)) for x,y in [('20.06','17.7'),('20.07','17.9'),('20.05','17.6'),('20.08','18.0')]]):
   r=fut.result();screens.append(r);out.write(json.dumps(r)+'\n');print('screen',r.get('t1'),r.get('t2'),r.get('error'),flush=True)
  found={}
  for r in screens:
   if 'error' not in r:found[(round(float(r['t1']),7),round(float(r['t2']),7))]=r
  with open('validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(solve,(r['t1'],r['t2'],d)) for r in found.values() for d in [100,160]]):
    r=fut.result();refs.append(r);out.write(json.dumps(r)+'\n');print('validate',r['dps'],r.get('error'),flush=True)
  jobs=[]
  for r in refs:
   if r['dps']==160 and 'error' not in r:
    for t in [r['t1'],r['t2']]:
     row=dict(r,t=t)
     for off in ['0','.125']:jobs.append((row,P['5']['180'],off))
  with open('source-validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(f.integral_check,j) for j in jobs]):out.write(json.dumps(fut.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,candidates=len(found))))
