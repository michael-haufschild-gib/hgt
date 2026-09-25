import json,time,math
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
import mpmath as m
import source as a
B=json.loads(Path('baseline.json').read_text());LABELS=['control-50','zero-24'];PROFILES=['native','late','early']
def chijet(y):
 if y<=2:return np.array([[0.,0.,0.]]*3)
 if y>=3:return np.array([[1.,0.,0.]]*3)
 u=y-2;v=3-y;h=1/u-1/v
 if abs(h)>700:c=0. if h>0 else 1.;cp=cpp=0.
 else:
  c=1/(1+math.exp(h));hp=-1/u**2-1/v**2;hpp=2/u**3-2/v**3;cp=-c*(1-c)*hp;cpp=c*(1-c)*((1-2*c)*hp*hp-hpp)
 return np.array([[c,cp,cpp],[c*c,2*c*cp,2*(cp*cp+c*cpp)],[2*c-c*c,2*(1-c)*cp,2*((1-c)*cpp-cp*cp)]])
def coeff(t,A,y,margin=100):
 c=a.coefficients(t,A,y,margin);N=len(c)//2;c=c[N:];dy=[(c[0]/2-2*m.sqrt(y)*t*m.sin(m.arg(A)+t*m.log(y)))/y]
 for n in range(1,N+1):
  div=m.fsum(m.cos(t*m.log(m.mpf(n)/(d*d))) for d in range(1,n+1) if n%d==0);x=2*m.pi*n*y
  kp=-m.re(m.besselk(1j*t-1,x)+m.besselk(1j*t+1,x))/2
  dy.append(c[n]/(2*y)+4*m.pi*n*m.sqrt(y)*div*kp/abs(A))
 return c,dy

def grid(label,res):
 t=float(B[label]['item']['t']);q=math.ceil(.7*t+24)*res;x,w=np.polynomial.legendre.leggauss(q);p=[('compact',float((xx+1)/4),float(ww/4)) for xx,ww in zip(x,w)];Y=(t+100)/(2*math.pi)+2
 br=sorted(set([0,math.log(2),math.log(2.5),math.log(3),math.log(Y)]+[k*math.log(2) for k in range(2,math.ceil(math.log(Y)/math.log(2))) if k*math.log(2)<math.log(Y)]))
 for lo,hi in zip(br,br[1:]):p +=[('tail',float((hi+lo)/2+(hi-lo)*xx/2),float((hi-lo)*ww/2)) for xx,ww in zip(x,w)]
 return [p[i:i+6] for i in range(0,len(p),6)]
def packet(job):
 label,res,dps,batch=job;start=time.monotonic();t,A=a.init(B[label]['item']['t'],dps);tf=float(t);lam=.25+tf*tf;tot=np.zeros((3,8))
 try:
  for kind,v,w in batch:
   lo=v if kind=='compact' else None;y=math.sqrt(1-v*v) if lo is not None else math.exp(v);weight=w*v/(1-v*v)**1.5 if lo is not None else w/y
   cc,dd=coeff(t,A,m.mpf(y));c=np.array(list(map(float,cc)));dy=np.array(list(map(float,dd)));N=len(c)-1
   if lo is None:
    nx=1
    while nx<=4*N:nx*=2
    x=np.arange(nx)/nx-.5;ww=np.full(nx,1/nx)
   else:
    xx,ww=np.polynomial.legendre.leggauss(math.ceil(2*math.pi*N)+24);x=(lo+.5)/2+(.5-lo)*xx/2;ww=(.5-lo)*ww
   theta=2*np.pi*np.outer(x,np.arange(1,N+1));cos=np.cos(theta);sin=np.sin(theta)
   S=c[0]+cos@(2*c[1:]);Sy=dy[0]+cos@(2*dy[1:]);Sx=sin@(-4*np.pi*np.arange(1,N+1)*c[1:]);fullLap=-2*lam*S*S+2*y*y*(Sx*Sx+Sy*Sy)
   z=c[0]**2;zp=2*c[0]*dy[0];zpp=2*dy[0]**2-2*lam*z/y**2
   for j,(ch,cp,cpp) in enumerate(chijet(y)):
    F=S*S-ch*z;Fx=2*S*Sx;Fy=2*S*Sy-cp*z-ch*zp;contact=y*y*(cpp*z+2*cp*zp+ch*zpp);Lap=fullLap-contact
    vals=[ww@F,ww@(F*F),y*y*(ww@(Fx*Fx+Fy*Fy)),ww@(Lap*Lap),-ww@(F*Lap),ww@(fullLap*fullLap),float(ww.sum())*contact*contact,-2*contact*(ww@fullLap)]
    tot[j]+=weight*np.array(vals)
  return dict(label=label,res=res,dps=dps,values=tot.tolist(),seconds=time.monotonic()-start)
 except Exception as ex:return dict(label=label,res=res,dps=dps,error=str(ex)[:180],seconds=time.monotonic()-start)
def independent(label):
 start=time.monotonic();t,A=a.init(B[label]['item']['t'],160);out=[]
 for y in [m.mpf('.9'),m.mpf('2.3')]:
  c,dy=coeff(t,A,y)
  for n in [0,1,3]:
   def f(v):
    if n==0:return 2*m.sqrt(v)*m.cos(m.arg(A)+t*m.log(v))
    div=m.fsum(m.cos(t*m.log(m.mpf(n)/(d*d))) for d in range(1,n+1) if n%d==0)
    return 2*m.sqrt(v)*div*m.re(m.besselk(1j*t,2*m.pi*n*v))/abs(A)
   exact=m.diff(f,y);out.append(dict(y=str(y),n=n,relative_error=str(abs(exact-dy[n])/max(1,abs(exact)))))
 return dict(label=label,checks=out,seconds=time.monotonic()-start)
if __name__=='__main__':
 start=time.monotonic();jobs=[];expected={};rows=[]
 for l in LABELS:
  for res,d in [(1,50),(2,50),(2,100),(2,160)]:
   batches=grid(l,res);expected[(l,res,d)]=len(batches);jobs +=[(l,res,d,b) for b in batches]
 with ProcessPoolExecutor(max_workers=14) as pool,open('packets.jsonl','w',buffering=1) as raw:
  for f in as_completed([pool.submit(packet,j) for j in jobs]):
   r=f.result();rows.append(r);raw.write(json.dumps(r)+'\n')
   if len(rows)%40==0:print('packets',len(rows),'/',len(jobs),'elapsed',time.monotonic()-start,flush=True)
  with open('moments.jsonl','w',buffering=1) as out:
   for (l,res,d),n in expected.items():
    pp=[r for r in rows if (r['label'],r['res'],r['dps'])==(l,res,d)];row=dict(label=l,res=res,dps=d,profiles={})
    if len(pp)!=n or any('error' in r for r in pp):row['error']='incomplete'
    else:
     vv=np.array([r['values'] for r in pp]).sum(axis=0);t=float(B[l]['item']['t'])
     for profile,v in zip(PROFILES,vv):
      M,E,G,L,C,full,contact,cross=v;V=E-M*M/(math.pi/3);mu=G/V/t**2;second=L/V/t**4;variance=second-mu*mu
      row['profiles'][profile]=dict(mean=M,energy=E,gradient_energy=G,laplacian_energy=L,green_integral=C,full_laplacian_square=full,contact_square=contact,cross=cross,normalized_mean=mu,normalized_second=second,normalized_variance=variance,green_relative_error=abs(G-C)/max(1,abs(G)))
    out.write(json.dumps(row)+'\n')
  with open('independent.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(independent,l) for l in LABELS]):out.write(json.dumps(f.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,packets=len(rows))))
