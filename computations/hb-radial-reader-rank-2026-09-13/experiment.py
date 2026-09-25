import json,time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import radial as a

def matrix(z):return m.matrix([[a.value(z,b,r) for b in [False,True]] for r in [False,True]])
def det(z):return m.det(matrix(z))
def contour(lo,hi,n):
 zs=a.perimeter(lo,hi,n);vv=[det(z) for z in zs];phase=[m.arg(vv[(j+1)%len(vv)]/v) for j,v in enumerate(vv)]
 return dict(n=n,winding=str(sum(phase)/(2*m.pi)),max_phase=str(max(map(abs,phase))),samples=[dict(rho=a.cstr(z),det=a.cstr(v)) for z,v in zip(zs,vv)])
def scan(job):
 lo,hi=job;start=time.monotonic();m.mp.dps=50;out=dict(lo=lo,hi=hi,contours=[],roots=[])
 try:
  out['contours']=[contour(lo,hi,n) for n in [24,48]]
  if float(out['contours'][-1]['winding'])>.5:
   for frac in ['.1','.3','.5','.7','.9']:
    z=m.mpc('.5',m.mpf(lo)+m.mpf(frac)*(m.mpf(hi)-m.mpf(lo)))
    try:
     root=m.findroot(det,(z,z+.001),tol=m.mpf('1e-39'),maxsteps=40)
     if .01<root.real<.99 and m.mpf(lo)<root.imag<m.mpf(hi) and not any(abs(root-a.cc(r))<m.mpf('1e-20') for r in out['roots']):out['roots'].append(a.cstr(root))
    except Exception:pass
 except Exception as e:out['error']=str(e)[:150]
 out['seconds']=time.monotonic()-start;return out

def series_matrix(z):
 out=m.matrix(2)
 for r in range(2):
  for b in range(2):
   w,s,c0,c1=a.pars(z,bool(b),bool(r));j2,_=a.jacobi_series(2,w,s);j4,_=a.jacobi_series(4,w,s);out[r,b]=(c0*j2+c1*j4)/m.beta(3,w+1)
 return out

def validate(seed):
 start=time.monotonic();out=dict(seed=seed,precision=[])
 try:
  for d in [50,100,160]:
   m.mp.dps=d;z=a.cc(seed);z=m.findroot(det,(z,z+m.mpf('1e-6')),tol=m.mpf(10)**(-d+10),maxsteps=35);seed=a.cstr(z);M=matrix(z)
   out['precision'].append(dict(dps=d,rho=seed,det=a.cstr(m.det(M)),entries=[[a.cstr(M[r,b]) for b in range(2)] for r in range(2)]))
  m.mp.dps=190;z=a.cc(seed);M=series_matrix(z);H=matrix(z);v=m.matrix([-M[0,1],M[0,0]]);v/=m.sqrt(sum(abs(x)**2 for x in v));res=M*v
  third=[]
  for b in [False,True]:
   w=-m.mpf('1.5')+z/4;s=z-2 if b else -z-1;third.append(a.norm_ws(w,s))
  anchor=z+m.mpf('.001');D=series_matrix(anchor)-matrix(anchor)
  out.update(independent_det=a.cstr(m.det(M)),entry_disagreement=str(max(abs(M[r,b]-H[r,b]) for r in range(2) for b in range(2))),null_vector=[a.cstr(x) for x in v],null_residual=str(max(map(abs,res))),third_reader_response=a.cstr(sum(third[i]*v[i] for i in range(2))),anchor_disagreement=str(max(abs(D[r,b]) for r in range(2) for b in range(2))),derivative=a.cstr(m.diff(det,z)))
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 start=time.monotonic();m.mp.dps=50;z=m.mpc('.3','4');M=matrix(z);P=m.matrix([[1,2],[0,1]]);Q=m.matrix([[1,0],[-1,1]])
 Path('pilot.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,det=a.cstr(m.det(M)),basis_error=str(abs(m.det(P*M*Q)-m.det(M))),real_degeneracy=str(abs(det(m.mpf('.5')))))))
 jobs=[('.1','8')]+[(str(k),str(k+8)) for k in range(8,80,8)];rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('scan.jsonl','w',buffering=1) as out:
  for f in as_completed([pool.submit(scan,j) for j in jobs]):
   r=f.result();rows.append(r);out.write(json.dumps(r)+'\n');print('tile',r['lo'],'roots',len(r['roots']),r.get('error'),flush=True)
  roots=[z for r in sorted(rows,key=lambda r:float(r['lo'])) for z in r['roots']][:4]
  with open('validation.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(validate,z) for z in roots]):r=f.result();out.write(json.dumps(r)+'\n');print('validated',r['seed'],r.get('error'),flush=True)
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,tiles=len(rows),candidates=len(roots))))
