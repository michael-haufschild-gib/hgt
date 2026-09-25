import json,os,time,copy
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import analytic as a
import earlier as e

POINTS=json.loads(Path('points.json').read_text())
DEAD=float(os.environ['CAMPAIGN_DEADLINE'])

def collision(seed,t0,l0,dps):
 start=time.monotonic();m.mp.dps=dps;q=seed.get('q',0)
 e.c.CURRENT_Q=q;e.d.xi_jets=e.c.carrier_jets if q else e.ORIGINAL
 prec='70' if dps==50 else ('120' if dps==100 else '180')
 params=e.P[str(q)][prec] if q else e.P[prec]
 fun=e.k.setup(seed['direction'],params);kap=m.mpf(seed['interaction'])
 def get(t,l):
  if time.monotonic()>DEAD-6:raise TimeoutError('family deadline')
  return fun(t,l,kap)
 t,l=m.findroot(lambda t,l:tuple(get(t,l)[0][:2]),(m.mpf(t0),m.mpf(l0)),J=lambda t,l:get(t,l)[1],tol=m.mpf(10)**(-dps+12),maxsteps=18)
 F,J,Fk,bound=get(t,l)
 return dict(seed=seed,t=m.nstr(t,dps),lam=m.nstr(l,dps),dps=dps,kappa=str(seed['interaction']),residual=m.nstr(max(abs(z) for z in F[:2]),dps),Ftt=m.nstr(F[2],dps),Fl=m.nstr(J[0,1],dps),positive_bound=m.nstr(bound,dps),seconds=time.monotonic()-start)

def track(job):
 idx,way,scale=job;start=time.monotonic();p=POINTS[idx];seed=p['seed'];F,params=a.make(seed,50)
 l0=m.mpf(seed['lam'])*m.mpf(p['fraction']);r=m.mpf(1);z=a.dec(p['precision'][-1]['t'])
 target=m.mpf(0) if way=='back' else m.mpf('1.6');sign=-1 if way=='back' else 1
 step=m.mpf('.025')/scale;maxstep=step;prev=None
 row=dict(index=idx,seed=seed,way=way,resolution=scale,witness_lambda=str(l0),points=[])
 key='%s-%s-%s'%(idx,way,scale)
 try:
  for attempt in range(150):
   row['points'].append(dict(ratio=str(r),t=a.enc(z),residual=m.nstr(abs(F(z,r*l0)),20)))
   Path('partial-'+key+'.json').write_text(json.dumps(row))
   if r==target:row['endpoint_reached']=True;break
   rn=max(target,r-step) if sign<0 else min(target,r+step)
   predictor=z if prev is None else z+(z-prev[1])*(rn-r)/(r-prev[0])
   try:
    zn=m.findroot(lambda t:F(t,rn*l0),(predictor,predictor+m.mpf('1e-5')),tol=m.mpf('1e-39'),maxsteps=18)
    if zn.imag<0:zn=m.conj(zn)
    if abs(zn-z)>m.mpf('.4') or abs(zn-predictor)>m.mpf('.3'):raise ValueError('continuation jump')
    if abs(zn.imag)<m.mpf('1e-7') or abs(z.imag)<m.mpf('.02'):
     candidate=collision(seed,str(z.real),str((r+rn)*l0/2),50)
     lc=m.mpf(candidate['lam']);tc=m.mpf(candidate['t'])
     if min(r,rn)*l0-m.mpf('1e-12')<=lc<=max(r,rn)*l0+m.mpf('1e-12') and abs(tc-z.real)<m.mpf('.4'):
      row['collision']=candidate;row['bracket']=[str(min(r,rn)*l0),str(max(r,rn)*l0)];break
     if abs(zn.imag)<m.mpf('1e-7'):raise ValueError('real root without attached collision')
   except (ValueError,ZeroDivisionError):
    step/=2
    if step<m.mpf('2e-6'):raise ValueError('minimum step; no boundary identification')
    continue
   prev=(r,z);r,z=rn,zn;step=min(maxstep,step*m.mpf('1.25'))
  row['last_ratio']=str(r);row['last_t']=a.enc(z)
 except Exception as ex:row['error']=str(ex)[:200]
 row['seconds']=time.monotonic()-start;return row

def refine(job):
 row,dps=job;out=dict(index=row['index'],way=row['way'],resolution=row['resolution'])
 try:out.update(collision(row['seed'],row['collision']['t'],row['collision']['lam'],dps))
 except Exception as ex:out['error']=str(ex)[:160]
 return out

if __name__=='__main__':
 start=time.monotonic();rows=[]
 jobs=[(i,w,res) for i in range(len(POINTS)) for w in ['back','forward'] for res in [1,2]]
 with ProcessPoolExecutor(max_workers=14) as pool,open('tracks.jsonl','w',buffering=1) as f:
  pilot=[j for j in jobs if j[2]==1];remaining=[j for j in jobs if j[2]==2]
  for fut in as_completed([pool.submit(track,j) for j in pilot]):
   r=fut.result();rows.append(r);f.write(json.dumps(r)+'\n');print('track',r['index'],r['way'],r['resolution'],r.get('collision',{}).get('lam'),r.get('error'),flush=True)
  estimate=max(r['seconds'] for r in rows)*2*max(1,len(remaining)/14)
  admit=estimate<(DEAD-time.monotonic())*.45
  Path('pilot.json').write_text(json.dumps(dict(remaining_estimate=estimate,admit_fine_tracks=admit)))
  if admit:
   for fut in as_completed([pool.submit(track,j) for j in remaining]):
    r=fut.result();rows.append(r);f.write(json.dumps(r)+'\n');print('track',r['index'],r['way'],r['resolution'],r.get('collision',{}).get('lam'),r.get('error'),flush=True)
  # Refine each distinct reached boundary once; finer tracks independently test attachment.
  chosen={}
  for r in rows:
   if 'collision' in r:chosen[(r['index'],r['way'])]=r
  refined=[]
  with open('validation.jsonl','w',buffering=1) as v:
   for fut in as_completed([pool.submit(refine,(r,dps)) for r in chosen.values() for dps in [100,160]]):
    r=fut.result();refined.append(r);v.write(json.dumps(r)+'\n')
  with open('source-validation.jsonl','w',buffering=1) as v:
   for fut in as_completed([pool.submit(e.source,r) for r in refined if r.get('dps')==160 and 'error' not in r]):
    r=fut.result();v.write(json.dumps(r)+'\n');print('source',r['row']['index'],r['row']['way'],flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,tracks=len(rows),attached=sum('collision' in r for r in rows),errors=sum('error' in r for r in rows))))
