import json,time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import base as b
import analytic as a
import fold as f
NODE=json.loads(Path('node.json').read_text())

def track(job):
 off,n=job;start=time.monotonic();get,F,params=b.setup(50);u=m.mpf(NODE['t1']);v=m.mpf(NODE['t2']);node=get(u)
 _,parts=f.evaluator(5,[-1,1],params);X,D,W=parts(v);lam,kap=node['lam'],node['kappa']
 Fl=D[0]+2*kap*lam*W[0];Fk=lam*lam*W[0];Fzz=X[2]+lam*D[2]+kap*lam*lam*W[2]
 coefficient=-2*(Fl*node['lambda_prime']+Fk*node['kappa_prime'])/Fzz
 lo=u+m.mpf(off);end=m.mpf(b.SPEC['boundaries'][-1]['t']);entry=m.mpf(b.SPEC['boundaries'][0]['t'])
 grid=sorted(set([lo+(end-lo)*j/n for j in range(n+1)]+[entry]));z=v+m.sqrt(coefficient*m.mpf(off));previous=None
 row=dict(offset=off,n=n,coefficient=str(coefficient),points=[],endpoints=[])
 try:
  for t in grid:
   data=get(t);lam,kap=data['lam'],data['kappa'];predict=z if previous is None else z+(z-previous[1])*(t-oldt)/(oldt-previous[0])
   zz=m.findroot(lambda x:F(x,lam,kap)/(x-t)**2,(predict,predict+m.mpf('1e-4')),tol=m.mpf('1e-38'),maxsteps=20)
   if abs(zz-t)<m.mpf('1e-4') or abs(zz-z)>m.mpf('.4') or abs(zz-predict)>m.mpf('.4'):raise ValueError('root switch/jump check')
   if row['points']:previous=(oldt,z)
   oldt=t;z=zz;point=dict(chart_t=str(t),lam=str(lam),kappa=str(kap),t=a.enc(z),residual=str(abs(F(z,lam,kap))),bound=str(data['positivity_bound']))
   row['points'].append(point)
   if t==entry or t==end:row['endpoints'].append(dict(which='entry' if t==entry else 'return',**point))
   Path('partial-'+off+'-'+str(n)+'.json').write_text(json.dumps(row))
  row['complete']=True
 except Exception as ex:row['error']=str(ex)[:220]
 row['seconds']=time.monotonic()-start;return row

def refine(job):
 row,dps=job;start=time.monotonic();get,F,_=b.setup(dps);data=get(m.mpf(row['chart_t']));lam,kap=data['lam'],data['kappa'];z=a.dec(row['t']);out=dict(dps=dps)
 try:
  zz=m.findroot(lambda x:F(x,lam,kap),(z,z+m.mpf('1e-8')),tol=m.mpf(10)**(-dps+12),maxsteps=20)
  out.update(row=dict(row,lam=str(lam),kappa=str(kap)),t=a.enc(zz),shift=str(abs(zz-z)),residual=str(abs(F(zz,lam,kap))))
 except Exception as ex:out.update(row=row,error=str(ex)[:200])
 out['seconds']=time.monotonic()-start;return out

if __name__=='__main__':
 start=time.monotonic();tracks=[];refs=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('tracks.jsonl','w',buffering=1) as out:
  for fut in as_completed([pool.submit(track,(off,n)) for off in ['.0001','.0002'] for n in [32,64]]):
   r=fut.result();tracks.append(r);out.write(json.dumps(r)+'\n');print('track',r['offset'],r['n'],r.get('complete'),r.get('error'),flush=True)
  chosen={}
  for r in tracks:
   if r.get('complete'):
    for pt in r['endpoints']:chosen[pt['which']]=pt
  with open('validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(refine,(r,d)) for r in chosen.values() for d in [100,160]]):
    r=fut.result();refs.append(r);out.write(json.dumps(r)+'\n');print('refine',r['row']['which'],r['dps'],r.get('error'),flush=True)
  with open('source-validation.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(b.source,r) for r in refs if r['dps']==160 and 'error' not in r]):out.write(json.dumps(fut.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,tracks=len(tracks),complete=sum(bool(r.get('complete')) for r in tracks))))
