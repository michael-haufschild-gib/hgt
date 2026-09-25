import json,time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import matrix_source as e

def cell(job):
 x0,x1,y0,y1=map(m.mpf,job);start=time.monotonic();m.mp.dps=50;out=dict(box=job,contours=[],roots=[])
 try:
  for n in [24,48]:
   corners=[m.mpc(x0,y0),m.mpc(x1,y0),m.mpc(x1,y1),m.mpc(x0,y1)];zs=[corners[j]+m.mpf(k)/n*(corners[(j+1)%4]-corners[j]) for j in range(4) for k in range(n)];vals=[e.det(z) for z in zs];phi=[m.arg(vals[(j+1)%len(vals)]/v) for j,v in enumerate(vals)]
   out['contours'].append(dict(n=n,winding=str(sum(phi)/(2*m.pi)),max_phase=str(max(map(abs,phi))),samples=[dict(rho=e.a.cstr(z),det=e.a.cstr(v)) for z,v in zip(zs,vals)]))
  if float(out['contours'][-1]['winding'])>.5:
   for fx,fy in [(.5,.5),(.2,.2),(.8,.8),(.2,.8),(.8,.2)]:
    z=m.mpc(x0+(x1-x0)*fx,y0+(y1-y0)*fy)
    try:
     r=m.findroot(e.det,(z,z+.0001),tol=m.mpf('1e-40'),maxsteps=80)
     if .01<r.real<.99 and .1<r.imag<8 and not any(abs(r-e.a.cc(v))<m.mpf('1e-20') for v in out['roots']):out['roots'].append(e.a.cstr(r))
    except Exception as ex:out.setdefault('failures',[]).append(str(ex)[:100])
 except Exception as ex:out['error']=str(ex)[:160]
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 start=time.monotonic();xs=['.01','.255','.5','.745','.99'];ys=['.1','1','2','3','4','5','6','7','8'];rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('cells.jsonl','w',buffering=1) as out:
  for f in as_completed([pool.submit(cell,(xs[i],xs[i+1],ys[j],ys[j+1])) for i in range(4) for j in range(8)]):
   r=f.result();rows.append(r);out.write(json.dumps(r)+'\n')
   if r['roots']:print('candidate',r['roots'],flush=True)
  roots=[]
  for r in rows:
   for z in r['roots']:
    if not any(abs(e.a.cc(z)-e.a.cc(v))<m.mpf('1e-15') for v in roots):roots.append(z)
  with open('validation.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(e.validate,r) for r in roots[:4]]):r=f.result();out.write(json.dumps(r)+'\n');print('validation',r['seed'],r.get('error'),flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,cells=len(rows),candidates=roots)))
