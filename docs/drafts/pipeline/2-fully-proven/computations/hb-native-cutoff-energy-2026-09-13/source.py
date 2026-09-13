import os,time,json,math
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
import mpmath as m
S=json.loads(Path('spec.json').read_text());DEAD=float(os.environ['CAMPAIGN_DEADLINE'])
def init(t,dps):
 m.mp.dps=dps;t=m.mpf(t);s=1+2j*t
 A=m.exp(-s*m.log(m.pi)/2+m.loggamma(s/2))*m.zeta(s)
 return t,A

def coefficients(t,A,y,margin):
 if time.monotonic()>DEAD-8:raise TimeoutError('whole family deadline')
 N=int(m.ceil((t+margin)/(2*m.pi*y)));out=[m.mpf(0)]*(2*N+1)
 out[N]=2*m.sqrt(y)*m.cos(m.arg(A)+t*m.log(y))
 for n in range(1,N+1):
  divisor=m.fsum(m.cos(t*m.log(m.mpf(n)/(d*d))) for d in range(1,n+1) if n%d==0)
  c=2*m.sqrt(y)*divisor*m.re(m.besselk(1j*t,2*m.pi*n*y))/abs(A)
  out[N-n]=out[N+n]=c
 return out

def conv(a,b):
 return list(np.convolve(np.array(a,dtype=object),np.array(b,dtype=object)))

def moments(c,lower=None):
 f=conv(c,c);N=(len(f)-1)//2;cc=c[len(c)//2]
 if lower is None:
  fp=f[:];fc=f[:];fp[N]-=cc*cc;fc[N]=m.mpf(0)
  return [fp[N],m.fsum(x*x for x in fp),fc[N],m.fsum(x*x for x in fc)]
 def integral(v):
  k0=len(v)//2
  return v[k0]*(1-2*lower)+m.fsum(v[k0+k]*(-2*m.sin(2*m.pi*k*lower)/(m.pi*k)) for k in range(1,k0+1))
 M=integral(f);E=integral(conv(f,f));return [M,E,M,E]

def pilot(job):
 item,dps=job;start=time.monotonic();t,A=init(item['t'],dps)
 for y in [m.mpf('.9'),m.mpf('1.3')]:moments(coefficients(t,A,y,100),m.sqrt(1-y*y) if y<1 else None)
 return dict(label=item['label'],dps=dps,seconds=time.monotonic()-start)

def energy(job):
 item,res,margin,dps=job;start=time.monotonic();out=dict(label=item['label'],t=item['t'],resolution=res,margin=margin,dps=dps)
 try:
  t,A=init(item['t'],dps);q=int(math.ceil(.7*float(t)+24))*res
  nodes,weights=np.polynomial.legendre.leggauss(q);tot=[m.mpf(0)]*4
  for z,w in zip(nodes,weights):
   a=m.mpf(float((z+1)/4));weight=m.mpf(float(w/4))*a/(1-a*a)**m.mpf('1.5');y=m.sqrt(1-a*a)
   vals=moments(coefficients(t,A,y,margin),a)
   tot=[v+weight*x for v,x in zip(tot,vals)]
  Y=(t+100)/(2*m.pi)+2;end=m.log(Y);panels=int(m.ceil(end/m.log(2)))
  for j in range(panels):
   lo=end*j/panels;hi=end*(j+1)/panels
   for z,w in zip(nodes,weights):
    v=(lo+hi)/2+(hi-lo)*m.mpf(float(z))/2;y=m.exp(v);weight=(hi-lo)*m.mpf(float(w))/2/y
    vals=moments(coefficients(t,A,y,margin));tot=[a+weight*x for a,x in zip(tot,vals)]
   Path('partial-'+item['label']+'-'+str(res)+'-'+str(margin)+'-'+str(dps)+'.json').write_text(json.dumps(dict(completed_panels=j+1,totals=list(map(str,tot)))))
  result={}
  for label,i in [('principal',0),('constant_fourier',2)]:
   M,E=tot[i:i+2];V=E-M*M/(m.pi/3);R=t*t*M*M/(2176*(m.pi/3)*V)
   result[label]=dict(mean=str(M),energy=str(E),variance=str(V),ratio=str(R))
  out.update(values=result,q=q,Y=str(Y),panels=panels)
 except Exception as ex:out['error']=str(ex)[:220]
 out['seconds']=time.monotonic()-start;return out

def independent(job):
 item,dps=job;start=time.monotonic();t,A=init(item['t'],dps);x=2*m.pi*m.mpf('.9');theta=m.pi/2-1/(t+1)
 end=m.acosh((dps+20)*m.log(10)/(x*m.cos(theta)))
 # Shift the full-line K integral; conjugate halves give this real integral.
 intervals=[end*j/64 for j in range(65)]
 value=m.exp(-t*theta)*m.quad(lambda u:m.exp(-x*m.cos(theta)*m.cosh(u))*m.cos(t*u-x*m.sin(theta)*m.sinh(u)),intervals)
 expected=m.re(m.besselk(1j*t,x))
 return dict(label=item['label'],dps=dps,x=str(x),theta=str(theta),scaled_error=str(abs(value-expected)/abs(A)),seconds=time.monotonic()-start)

if __name__=='__main__':
 start=time.monotonic();pilots=[];admitted=[];rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool:
  for fut in as_completed([pool.submit(pilot,(item,d)) for item in S['heights'] for d in [50,160]]):pilots.append(fut.result())
  cost=0
  for item in S['heights']:
   q=int(math.ceil(.7*float(item['t'])+24));panels=int(math.ceil(math.log((float(item['t'])+100)/(2*math.pi)+2)/math.log(2)))
   slow=max(r['seconds'] for r in pilots if r['label']==item['label'])/2
   estimate=slow*q*(panels+1)*2
   # Two precision challenges plus four crossed screening jobs, with tail/implementation reserve.
   if estimate<min(260,(DEAD-time.monotonic())*.6) and cost+6*estimate/14<(DEAD-time.monotonic())*.7:
    admitted.append(item);cost+=6*estimate/14
  Path('pilot.json').write_text(json.dumps(dict(measurements=pilots,admitted=admitted,estimated_parallel_cost=cost)))
  print('admitted',[r['label'] for r in admitted],flush=True)
  jobs=[(it,res,margin,50) for it in admitted for res in [1,2] for margin in [60,100]]+[(it,2,100,d) for it in admitted for d in [100,160]]
  with open('energy.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(energy,j) for j in jobs]):
    r=fut.result();rows.append(r);out.write(json.dumps(r)+'\n');print('energy',r['label'],r['resolution'],r['margin'],r['dps'],r.get('error'),flush=True)
  with open('independent.jsonl','w',buffering=1) as out:
   for fut in as_completed([pool.submit(independent,(it,160)) for it in admitted]):out.write(json.dumps(fut.result())+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,admitted=len(admitted),completed=sum('values' in r for r in rows))))
