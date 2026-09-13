import json,time,os
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import mpmath as m
import analytic as a
SPEC=json.loads(Path('spec.json').read_text());Q=SPEC['q'];DEAD=float(os.environ['CAMPAIGN_DEADLINE'])
def params(d):
 key='70' if d==50 else '120' if d==100 else '180';p=a.PARAM[str(Q)][key] if Q else a.PARAM[key]
 return p,[{int(k):m.mpf(v) for k,v in p[n].items()} for n in ['h1','h2']]
def carrierjet(t):
 s=m.mpf('.5')+1j*t
 if Q==0:
  pref=s*(s-1)/2*m.exp(-s*m.log(m.pi)/2+m.loggamma(s/2));ld=1/s+1/(s-1)+(m.digamma(s/2)-m.log(m.pi))/2;z=m.zeta(s);zp=m.zeta(s,derivative=1)
 else:
  chi=[0,1,-1,-1,1];pref=m.exp(s*m.log(Q/m.pi)/2+m.loggamma(s/2)-s*m.log(Q));ld=(m.log(Q/m.pi)+m.digamma(s/2))/2-m.log(Q)
  z=m.fsum(chi[r]*m.zeta(s,m.mpf(r)/Q) for r in range(1,Q));zp=m.fsum(chi[r]*m.zeta(s,m.mpf(r)/Q,derivative=1) for r in range(1,Q))
 return pref*z,1j*pref*(zp+ld*z)
def basis(t,d):
 if time.monotonic()>DEAD-8:raise TimeoutError('family deadline')
 if not (0<m.re(t)<SPEC['max_real'] and m.mpf('.001')<abs(m.im(t))<SPEC['max_imag']+1):raise ValueError('outside frozen inverse domain')
 _,h=params(d);ks={0}
 for hh in h:
  for k in hh:ks.update([k,-k])
 X={k:carrierjet(t+k) for k in ks};scale=m.exp(m.pi*t/4);val=[X[0]]+[tuple(m.fsum(c*(X[k][j]+X[-k][j])/2 for k,c in hh.items()) for j in [0,1]) for hh in h]
 return [[scale*x for x in v] for v in val]
def inverse(t,d):
 v=basis(t,d);X,U,V=[r[0] for r in v];A=m.matrix([[U.real,V.real],[U.imag,V.imag]]);de=m.det(A)
 if abs(de)<m.mpf(10)**(-d+15)*max(1,abs(U)*abs(V)):raise ValueError('near-singular inverse')
 ab=m.lu_solve(A,m.matrix([-X.real,-X.imag]));ft=v[0][1]+ab[0]*v[1][1]+ab[1]*v[2][1]
 return ab,ft,v,de
def solve(job):
 x,y,d=job;start=time.monotonic();m.mp.dps=d;out=dict(seed=[str(x),str(y)],dps=d)
 try:
  def f(x,y):
   ab,v,_,_=inverse(m.mpc(x,y),d);return v.real,v.imag
  x,y=m.findroot(f,(m.mpf(x),m.mpf(y)),tol=m.mpf(10)**(-d+12),maxsteps=18);t=m.mpc(x,y);ab,ft,v,de=inverse(t,d)
  bound=sum(map(abs,ab));res=v[0][0]+ab[0]*v[1][0]+ab[1]*v[2][0]
  out.update(t=a.enc(t),alpha=str(ab[0]),beta=str(ab[1]),bound=str(bound),inverse_determinant=str(de),F=a.enc(res),Ft=a.enc(ft),accepted=bool(.03<abs(t.imag)<SPEC['max_imag'] and 0<t.real<SPEC['max_real'] and bound<m.mpf('.8')))
  if d>=100:
   # Differentiate original first jet with parameters held fixed.
   ftt=m.diff(lambda z:sum(c*r[1] for c,r in zip([1,ab[0],ab[1]],basis(z,d))),t)
   out['Ftt']=a.enc(ftt)
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out

def independent(row):
 start=time.monotonic();m.mp.dps=190;t=a.dec(row['t']);alpha=m.mpf(row['alpha']);beta=m.mpf(row['beta']);_,h=params(160)
 def kernel(x):
  u=m.exp(2*x)
  if Q==0:return m.exp(x/2)*m.fsum(2*m.pi*(2*m.pi*n**4*u*u-3*n*n*u)*m.exp(-m.pi*n*n*u) for n in range(1,31))
  chi=[0,1,-1,-1,1];return 2*m.exp(x/2)*m.fsum(chi[n%5]*m.exp(-m.pi*n*n*u/5) for n in range(1,41))
 def mult(x):return 1+alpha*m.fsum(c*m.cos(k*x) for k,c in h[0].items())+beta*m.fsum(c*m.cos(k*x) for k,c in h[1].items())
 out=dict(row=row)
 try:
  intervals=[m.mpf(j)/16 for j in range(65)];val=2*m.quad(lambda x:kernel(x)*mult(x)*m.cos(t*x),intervals);der=-2*m.quad(lambda x:x*kernel(x)*mult(x)*m.sin(t*x),intervals)
  anchor=t+m.mpf('.01');av=2*m.quad(lambda x:kernel(x)*mult(x)*m.cos(anchor*x),intervals);vv=basis(anchor,160);expected=sum(c*r[0] for c,r in zip([1,alpha,beta],vv));scale=m.exp(m.pi*t/4)
  out.update(F_scaled=a.enc(val*scale),Ft_scaled=a.enc(der*scale),anchor_difference=a.enc(av*m.exp(m.pi*anchor/4)-expected))
 except Exception as e:out['error']=str(e)[:180]
 out['seconds']=time.monotonic()-start;return out
if __name__=='__main__':
 start=time.monotonic();m.mp.dps=50;begin=time.monotonic();inverse(m.mpc(SPEC['heights'][0],'.4'),50);cost=time.monotonic()-begin;estimate=cost*120*24/14
 Path('pilot.json').write_text(json.dumps(dict(one_evaluation_seconds=cost,screen_estimate=estimate,admitted=estimate<350)))
 if estimate>350:raise RuntimeError('pilot rejected screen; reformulate before retry')
 rows=[]
 with ProcessPoolExecutor(max_workers=14) as pool,open('screen.jsonl','w',buffering=1) as out:
  for f in as_completed([pool.submit(solve,(x,y,50)) for x in SPEC['heights'] for y in SPEC['imaginary_seeds']]):
   r=f.result();rows.append(r);out.write(json.dumps(r)+'\n');print('screen',r['seed'],r.get('accepted'),r.get('error'),flush=True)
  chosen=[]
  for r in sorted(rows,key=lambda r:float(r.get('t',['0','100'])[1])):
   if r.get('accepted') and not any(abs(a.dec(r['t'])-a.dec(v['t']))<m.mpf('1e-12') for v in chosen):chosen.append(r)
  refined=[]
  with open('validation.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(solve,(*r['t'],d)) for r in chosen[:4] for d in [100,160]]):r=f.result();refined.append(r);out.write(json.dumps(r)+'\n')
  with open('source-validation.jsonl','w',buffering=1) as out:
   for f in as_completed([pool.submit(independent,r) for r in refined if r.get('accepted') and r['dps']==160]):r=f.result();out.write(json.dumps(r)+'\n')
 Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,screen=len(rows),accepted=len(chosen))))
