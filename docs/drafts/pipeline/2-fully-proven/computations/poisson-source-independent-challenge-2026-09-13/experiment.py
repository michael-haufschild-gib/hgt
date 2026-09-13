import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
from functools import lru_cache
DEAD=float(os.environ['CAMPAIGN_DEADLINE'])
def enc(z):return [str(m.re(z)),str(m.im(z))]
def legendre(n):
 out=[]
 for j in range(1,n//2+1):
  z=m.cos(m.pi*(j-m.mpf('.25'))/(n+m.mpf('.5')))
  for it in range(30):
   p0=m.mpf(1);p1=z
   for k in range(2,n+1):p0,p1=p1,((2*k-1)*z*p1-(k-1)*p0)/k
   dp=n*(z*p1-p0)/(z*z-1);step=p1/dp;z-=step
   if abs(step)<m.mpf('1e-185'):break
  w=2/((1-z*z)*dp*dp);out +=[(z,w),(-z,w)]
 return sorted(out)
def run(arg):
 row,n,panels=arg;start=time.monotonic();m.mp.dps=190;q=41;a=list(map(m.mpf,row['a']));t=m.mpc(row['row']['T'],str(row['row']['y']));z=t+m.mpf('.01');J=Jp=Ja=m.mpc(0)
 nodes=legendre(n)
 for j in range(panels):
  if time.monotonic()>DEAD-10:raise TimeoutError('whole challenge deadline')
  left=m.mpf(5)*j/panels;right=m.mpf(5)*(j+1)/panels
  for node,w in nodes:
   x=(left+right)/2+(right-left)*node/2;c=m.pi*m.exp(2*x)/q
   nmax=int(m.ceil(m.sqrt((190*m.log(10)+40)/c)))
   kernel=2*m.exp(x/2)*m.fsum(a[k%q]*m.exp(-c*k*k) for k in range(1,nmax+1));weight=w*(right-left)/2*kernel
   J+=weight*m.cos(t*x);Jp-=weight*x*m.sin(t*x);Ja+=weight*m.cos(z*x)
 F=a[0]/2-(m.mpf('.25')+t*t)*J;Ft=-2*t*J-(m.mpf('.25')+t*t)*Jp;Fa=a[0]/2-(m.mpf('.25')+z*z)*Ja
 def hurwitz(tt):
  s=m.mpf('.5')+1j*tt
  return s*(s-1)/2*m.exp(-s*m.log(q*m.pi)/2+m.loggamma(s/2))*m.fsum(a[r%q]*m.zeta(s,m.mpf(r)/q) for r in range(1,q+1))
 scale=m.exp(m.pi*m.re(t)/4)
 return {'T':row['row']['T'],'y':row['row']['y'],'n':n,'panels':panels,'F_scaled':enc(F*scale),'Ft_scaled':enc(Ft*scale),'anchor_difference_scaled':enc((Fa-hurwitz(z))*scale),'seconds':time.monotonic()-start,'dps':190,'x_cutoff':5}
if __name__=='__main__':
 rows=[r for r in map(json.loads,Path('candidates.jsonl').read_text().splitlines()) if r.get('dps')==160]
 with ProcessPoolExecutor(max_workers=14) as p,open('source-validation.jsonl','w',buffering=1) as f:
  for ft in as_completed([p.submit(run,(r,n,panels)) for r in rows for n,panels in [(64,32),(96,40)]],timeout=max(1,DEAD-time.monotonic()-5)):
   try:r=ft.result()
   except Exception as e:r={'error':repr(e)}
   f.write(json.dumps(r)+'\n');print(r.get('T'),r.get('n'),r.get('error'),flush=True)
