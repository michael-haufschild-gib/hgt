import json,time,math,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
import mpmath as m
import source as a
B=json.loads(Path('baseline.json').read_text());LABELS=[k for k in B if k!='control50'];SIGN=np.vstack([np.ones(256)]+[np.random.default_rng(2026091300+j).choice([-1,1],256) for j in range(32)])
def transition(y):
 if y<=2:return 0.
 if y>=3:return 1.
 z=1/(y-2)-1/(3-y)
 return 0. if z>700 else 1. if z< -700 else 1/(1+math.exp(z))
def grid(label,res):
 t=float(B[label]['item']['t']);q=math.ceil(.7*t+24)*res;xx,ww=np.polynomial.legendre.leggauss(q);pts=[('compact',float((x+1)/4),float(w/4)) for x,w in zip(xx,ww)]
 Y=(t+100)/(2*math.pi)+2;breaks=sorted(set([0.,math.log(2),math.log(3),math.log(Y)]+[k*math.log(2) for k in range(2,math.ceil(math.log(Y)/math.log(2))) if k*math.log(2)<math.log(Y)]))
 for lo,hi in zip(breaks,breaks[1:]):pts +=[('tail',float((lo+hi)/2+(hi-lo)*x/2),float((hi-lo)*w/2)) for x,w in zip(xx,ww)]
 return [pts[i:i+8] for i in range(0,len(pts),8)]
def packet(job):
 label,res,dps,ids,batch=job;start=time.monotonic();t,A=a.init(B[label]['item']['t'],dps);tot=np.zeros((len(ids),2,2,2))
 try:
  for kind,v,w in batch:
   lower=v if kind=='compact' else None;y=math.sqrt(1-v*v) if lower is not None else math.exp(v);weight=w*v/(1-v*v)**1.5 if lower is not None else w/y
   cc=a.coefficients(t,A,m.mpf(y),100);N=len(cc)//2;c=np.array([float(x) for x in cc[N:]])
   if lower is None:
    nx=1
    while nx<=4*N:nx*=2
    x=np.arange(nx)/nx-.5;weights=np.full(nx,1/nx)
   else:
    nx=math.ceil(2*math.pi*N)+24;xx,ww=np.polynomial.legendre.leggauss(nx);x=(lower+.5)/2+(.5-lower)*xx/2;weights=(.5-lower)*ww
   S=c[0]+(SIGN[ids,:N]*(2*c[1:]))@np.cos(2*np.pi*np.outer(np.arange(1,N+1),x));sq=S*S;z=c[0]**2;Q=2*np.dot(c[1:],c[1:])
   for ip,ch in enumerate([float(y>1),transition(y)]):
    for ik,sub in enumerate([z,z+Q]):
     F=sq-ch*sub;tot[:,ip,ik,0]+=weight*(F@weights);tot[:,ip,ik,1]+=weight*((F*F)@weights)
  return dict(label=label,res=res,dps=dps,ids=ids,values=tot.tolist(),seconds=time.monotonic()-start)
 except Exception as ex:return dict(label=label,res=res,dps=dps,ids=ids,error=str(ex)[:180],seconds=time.monotonic()-start)
def aggregate(rows,label,res,dps,ids,expected):
 parts=[r for r in rows if (r['label'],r['res'],r['dps'])==(label,res,dps)];out=dict(label=label,res=res,dps=dps,ids=ids)
 if len(parts)!=expected or any('error' in r for r in parts):out['error']='incomplete';return out
 vals=np.array([r['values'] for r in parts]).sum(axis=0);V=vals[:,:,:,1]-vals[:,:,:,0]**2/(math.pi/3);R=float(B[label]['item']['t'])**2*vals[:,:,:,0]**2/(2176*(math.pi/3)*V)
 out.update(moments=vals.tolist(),variance=V.tolist(),ratio=R.tolist());return out

def independent(job):
 label,idx=job;start=time.monotonic();t,A=a.init(B[label]['item']['t'],160);out=[]
 for y in [m.mpf('.9'),m.mpf('1.3'),m.mpf('2.4')]:
  c=a.coefficients(t,A,y,100);N=len(c)//2
  for n in range(1,N+1):c[N-n]*=int(SIGN[idx,n-1]);c[N+n]*=int(SIGN[idx,n-1])
  lower=m.sqrt(1-y*y) if y<1 else None;f=a.conv(c,c);f2=a.conv(f,f)
  def integ(v):
   k=len(v)//2
   if lower is None:return v[k]
   return v[k]*(1-2*lower)+m.fsum(v[k+j]*(-2*m.sin(2*m.pi*j*lower)/(m.pi*j)) for j in range(1,k+1))
  nx=1
  while nx<=4*N:nx*=2
  if lower is None:x=np.arange(nx)/nx-.5;weights=np.full(nx,1/nx)
  else:
   xx,ww=np.polynomial.legendre.leggauss(math.ceil(2*math.pi*N)+24);lo=float(lower);x=(lo+.5)/2+(.5-lo)*xx/2;weights=(.5-lo)*ww
  vv=np.array([float(v) for v in c[N:]]);s=vv[0]+np.cos(2*np.pi*np.outer(x,np.arange(1,N+1)))@(2*vv[1:]);actual=[weights@(s*s),weights@(s**4)];exact=[integ(f),integ(f2)]
  out.append(dict(y=str(y),relative_errors=[str(abs(m.mpf(float(v))-z)/max(1,abs(z))) for v,z in zip(actual,exact)]))
 return dict(label=label,id=idx,checks=out,seconds=time.monotonic()-start)
if __name__=='__main__':
 start=time.monotonic();rows=[];results=[];selected={};counts={}
 Path('signs.json').write_text(json.dumps(SIGN.astype(int).tolist()))
 with ProcessPoolExecutor(max_workers=14) as pool,open('packets.jsonl','w',buffering=1) as raw,open('energy.jsonl','w',buffering=1) as output:
  for stage in ['screen','challenge']:
   jobs=[]
   for label in LABELS:
    variants=[(1,50,list(range(33))),(2,50,list(range(33)))] if stage=='screen' else [(2,d,[0,selected[label]]) for d in [100,160]]
    for res,d,ids in variants:
     batches=grid(label,res);counts[(label,res,d)]=(ids,len(batches));jobs +=[(label,res,d,ids,pk) for pk in batches]
   for f in as_completed([pool.submit(packet,j) for j in jobs]):
    r=f.result();rows.append(r);raw.write(json.dumps(r)+'\n')
    if len(rows)%40==0:print(stage,'packets',len(rows),'elapsed',time.monotonic()-start,flush=True)
   for key,(ids,n) in list(counts.items()):
    if (stage=='screen') != (key[2]==50):continue
    r=aggregate(rows,*key,ids,n);results.append(r);output.write(json.dumps(r)+'\n')
   if stage=='screen':
    for label in LABELS:
     rr=[r for r in results if r['label']==label and r['res']==2][0]
     if 'error' in rr:raise RuntimeError('screen incomplete; no challenge')
     v=np.array(rr['variance']);selected[label]=int(np.argmax(np.max(abs(v[1:]/v[0]-1),axis=(1,2))))+1
    Path('selected.json').write_text(json.dumps(selected))
    if time.monotonic()>a.DEAD-200:raise TimeoutError('insufficient challenge reserve')
  with open('independent.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(independent,(l,i)) for l in LABELS for i in [0,selected[l]]]):out.write(json.dumps(f.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,packets=len(rows),selected=selected)))
