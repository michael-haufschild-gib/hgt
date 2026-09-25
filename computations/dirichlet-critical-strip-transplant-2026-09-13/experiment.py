import json,time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import inverse_source as a
SEED=json.loads(Path('seed.json').read_text());CACHE={}
def third(kind,d):
 key=(kind,d)
 if key in CACHE:return CACHE[key]
 p,h=a.params(d)
 if kind=='product':hh={int(k):m.mpf(v) for k,v in p['h12'].items()}
 else:
  hh={}
  for x,c in h[0].items():
   for y,v in h[0].items():
    for k in [x+y,abs(x-y)]:hh[k]=hh.get(k,0)+c*v/2
  def moment(k):return m.re(a.carrierjet(m.mpf(k))[0]),-m.re(m.diff(lambda t:a.carrierjet(t)[1],m.mpf(k)))
  mm={k:moment(k) for k in set(hh)|{0,4}};A=m.matrix([[mm[k][j] for k in [0,4]] for j in [0,1]]);rhs=m.matrix([m.fsum(c*mm[k][j] for k,c in hh.items()) for j in [0,1]]);comp=m.lu_solve(A,rhs)
  for k,c in zip([0,4],comp):hh[k]=hh.get(k,0)-c
  norm=m.fsum(abs(c) for c in hh.values());hh={k:c/norm for k,c in hh.items()}
 CACHE[key]=hh;return hh

def basis(t,kind,d):
 if time.monotonic()>a.DEAD-8:raise TimeoutError('whole family deadline')
 if not (0<m.re(t)<a.SPEC['max_real'] and 0<m.im(t)<9):raise ValueError('outside frozen domain')
 _,hs=a.params(d);hs=hs+[third(kind,d)];ks={0}
 for h in hs:
  for k in h:ks.update([k,-k])
 X={k:a.carrierjet(t+k) for k in ks};scale=m.exp(m.pi*t/4)
 return [[scale*x for x in X[0]]]+[[scale*m.fsum(c*(X[k][j]+X[-k][j])/2 for k,c in h.items()) for j in [0,1]] for h in hs]
def inverse(x,y,kind,d):
 v=basis(m.mpc(x,y),kind,d);A=m.matrix([[v[k][0].real for k in [1,2,3]],[v[k][0].imag for k in [1,2,3]],[v[k][1].real for k in [1,2,3]]]);abc=m.lu_solve(A,m.matrix([-v[0][0].real,-v[0][0].imag,-v[0][1].real]));ft=v[0][1]+m.fsum(abc[k]*v[k+1][1] for k in range(3));return abc,ft,v,m.det(A)
def solvepoint(x,y,kind,d):
 root=m.findroot(lambda xx:inverse(xx,y,kind,d)[1].imag,(x,x+m.mpf('1e-5')),tol=m.mpf(10)**(-d+12),maxsteps=18);abc,ft,v,det=inverse(root,y,kind,d);bound=abs(abc[0])+abs(abc[1])+abs(abc[2])*sum(map(abs,third(kind,d).values()));F=v[0][0]+m.fsum(abc[k]*v[k+1][0] for k in range(3))
 return dict(t=[str(root),str(y)],coefficients=list(map(str,abc)),bound=str(bound),F=a.a.enc(F),Ft=a.a.enc(ft),unfolding_determinant=str(det))
def track(job):
 kind,target,step=job;start=time.monotonic();m.mp.dps=50;x=m.mpf(SEED['t'][0]);y=m.mpf(SEED['t'][1]);target=m.mpf(target);step=m.mpf(step);maximum=step;out=dict(kind=kind,target=str(target),step=str(step),points=[])
 try:
  while y>target:
   nxt=max(target,y-step)
   try:
    p=solvepoint(x,nxt,kind,50);xn=m.mpf(p['t'][0])
    if abs(xn-x)>m.mpf('.6'):raise ValueError('branch jump')
    if m.mpf(p['bound'])>=m.mpf('.8'):raise RuntimeError('positive multiplier bound exceeded')
   except (ValueError,ZeroDivisionError):
    step/=2
    if step<m.mpf('1e-4'):raise ValueError('minimum step; path unresolved')
    continue
   out['points'].append(p);x,y=xn,nxt;step=min(maximum,step*m.mpf('1.25'));Path('partial-'+kind+'-'+out['target']+'-'+out['step']+'.json').write_text(json.dumps(out))
  out['endpoint']=out['points'][-1];out['complete']=True
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out

def refine(job):
 row,d=job;start=time.monotonic();m.mp.dps=d;out=dict(kind=row['kind'],target=row['target'],dps=d)
 try:
  out.update(solvepoint(m.mpf(row['endpoint']['t'][0]),m.mpf(row['target']),row['kind'],d));coeff=list(map(m.mpf,out['coefficients']));t=m.mpc(*out['t']);out['Ftt']=a.a.enc(m.diff(lambda z:m.fsum(c*v[1] for c,v in zip([1]+coeff,basis(z,row['kind'],d))),t));out['third']={str(k):str(v) for k,v in third(row['kind'],d).items()}
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out

def source(row):
 start=time.monotonic();m.mp.dps=190;t=a.a.dec(row['t']);co=list(map(m.mpf,row['coefficients']));_,hs=a.params(160);hs +=[{int(k):m.mpf(v) for k,v in row['third'].items()}]
 def kernel(x):
  u=m.exp(2*x)
  if a.Q==0:return m.exp(x/2)*m.fsum(2*m.pi*(2*m.pi*n**4*u*u-3*n*n*u)*m.exp(-m.pi*n*n*u) for n in range(1,31))
  chi=[0,1,-1,-1,1];return 2*m.exp(x/2)*m.fsum(chi[n%5]*m.exp(-m.pi*n*n*u/5) for n in range(1,41))
 def mul(x):return 1+m.fsum(c*m.fsum(v*m.cos(k*x) for k,v in h.items()) for c,h in zip(co,hs))
 out=dict(row=row)
 try:
  pts=[m.mpf(j)/16 for j in range(65)];F=2*m.quad(lambda x:kernel(x)*mul(x)*m.cos(t*x),pts);Ft=-2*m.quad(lambda x:x*kernel(x)*mul(x)*m.sin(t*x),pts);z=t+m.mpf('.01');anchor=2*m.quad(lambda x:kernel(x)*mul(x)*m.cos(z*x),pts);expected=m.fsum(c*v[0] for c,v in zip([1]+co,basis(z,row['kind'],160)))
  out.update(F_scaled=a.a.enc(m.exp(m.pi*t/4)*F),Ft_scaled=a.a.enc(m.exp(m.pi*t/4)*Ft),anchor_difference=a.a.enc(m.exp(m.pi*z/4)*anchor-expected))
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 start=time.monotonic();rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('tracks.jsonl','w',buffering=1) as out:
  for f in as_completed([pool.submit(track,(kind,target,step)) for kind in ['product','square'] for target in ['.25','.125'] for step in ['.08','.04']]):
   r=f.result();rows.append(r);out.write(json.dumps(r)+'\n');print('track',r['kind'],r['target'],r['step'],r.get('complete'),r.get('error'),flush=True)
  chosen={}
  for r in rows:
   if r.get('complete'):chosen[(r['kind'],r['target'])]=r
  refined=[]
  with open('validation.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(refine,(r,d)) for r in chosen.values() for d in [100,160]]):r=f.result();refined.append(r);out.write(json.dumps(r)+'\n')
  with open('source-validation.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(source,r) for r in refined if r['dps']==160 and 'error' not in r]):r=f.result();out.write(json.dumps(r)+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,tracks=len(rows),complete=sum(bool(r.get('complete')) for r in rows))))
