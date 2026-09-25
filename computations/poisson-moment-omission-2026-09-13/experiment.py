"""Inverse Hermite interpolation inside the positive Poisson self-dual cone.
No Lean build; numerical feasibility and independent source checks only.
"""
import os,time,json,math,traceback
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
from scipy.linalg import qr
from scipy.optimize import linprog
import mpmath as m
import independent
SPEC=json.loads(Path('spec.json').read_text()); Q=SPEC['q']; DEADLINE=float(os.environ['CAMPAIGN_DEADLINE'])
def dump(path,x): Path(path).write_text(json.dumps(x,indent=2)+'\n')
def enc(z): return [str(m.re(z)),str(m.im(z))]
def basis(dps,pivots):
 m.mp.dps=dps; q=Q; root=m.sqrt(q)
 C=m.matrix(q,q); E=m.matrix(q,(q+1)//2)
 for r in range(q):
  for j in range(q): C[r,j]=m.cos(2*m.pi*r*j/q)/root
 E[0,0]=1
 for j in range(1,(q+1)//2): E[j,j]=E[q-j,j]=m.mpf('.5')
 P=(m.eye(q)+C)*E/2
 return m.matrix([[P[r,j] for j in pivots] for r in range(q)]),C

def jets(t,order=2):
 s=m.mpf('.5')+1j*t
 pref=s*(s-1)/2*m.exp(-s*m.log(Q*m.pi)/2+m.loggamma(s/2))
 ld=1/s+1/(s-1)-m.log(Q*m.pi)/2+m.digamma(s/2)/2
 ldd=-1/s**2-1/(s-1)**2+m.polygamma(1,s/2)/4
 out=[[],[],[]]
 for r in range(Q):
  a=m.mpf(r if r else Q)/Q
  z=m.zeta(s,a); zp=m.zeta(s,a,derivative=1)
  out[0].append(pref*z); out[1].append(1j*pref*(zp+ld*z))
  if order==2:
   zpp=m.zeta(s,a,derivative=2)
   out[2].append(-pref*(zpp+2*ld*zp+(ld*ld+ldd)*z))
 return [m.matrix([row]) for row in out[:order+1]]

def constraints(B,t,full):
 base=m.matrix([1+m.sqrt(Q)*(r==0) for r in range(Q)])
 target=jets(t,1); rows=[list(B[0,:])]; rhs=[base[0]]
 if full:
  j0=jets(m.mpf(0));
  for k in full:
   v=j0[k]*B; rows.append([m.re(v[j]) for j in range(B.cols)]);rhs.append(m.re((j0[k]*base)[0]))
 for v in target:
  z=v*B
  for part in [m.re,m.im]: rows.append([part(z[j]) for j in range(B.cols)]);rhs.append(0)
 M=m.matrix(rows); b=m.matrix(rhs)
 # Scaling changes no equality, and avoids absolute LP tolerance at high height.
 scales=[]
 for i in range(M.rows):
  scale=m.sqrt(sum(M[i,j]**2 for j in range(M.cols)));scales.append(scale)
  for j in range(M.cols): M[i,j]/=scale
  b[i]/=scale
 return M,b,base

def discover(arg):
 start=time.monotonic(); T,y,pivots=arg;B,C=basis(50,pivots);t=m.mpc(T,str(y));rows=[]
 for full in [[0],[2]]:
  M,b,base=constraints(B,t,full); mf=np.array(M.tolist(),float);bf=np.array(b.tolist(),float).ravel(); BB=np.array(B.tolist(),float); ab=np.array(list(base),float)
  res=linprog(np.zeros(B.cols),A_ub=np.vstack([-BB,BB]),b_ub=np.r_[-.05*ab,4*ab],A_eq=mf,b_eq=bf,bounds=[(None,None)]*B.cols,method='highs')
  row={'T':T,'y':y,'full_moments':full,'success':bool(res.success),'status':int(res.status),'message':res.message,'dimension':B.cols}
  if res.success:
   cp=qr(mf,pivoting=True,mode='economic')[2][:M.rows].tolist()
   row.update(u=[repr(float(v)) for v in res.x],constraint_pivots=cp,coefficient_min=float(np.min(BB@res.x)),scaled_residual=float(np.max(np.abs(mf@res.x-bf))))
  rows.append(row)
 return {'rows':rows,'seconds':time.monotonic()-start}

def refine(arg):
 row,pivots,dps=arg;start=time.monotonic();B,C=basis(dps,pivots);t=m.mpc(row['T'],str(row['y']));M,b,base=constraints(B,t,row['full_moments']);cp=row['constraint_pivots'];free=[j for j in range(B.cols) if j not in cp]
 u=m.matrix([m.mpf(v) for v in row['u']]);right=b.copy()
 for i in range(M.rows): right[i]-=sum(M[i,j]*u[j] for j in free)
 up=m.lu_solve(m.matrix([[M[i,j] for j in cp] for i in range(M.rows)]),right)
 for j,v in zip(cp,up):u[j]=v
 a=B*u;jt=jets(t);jx=[(v*a)[0] for v in jt];scale=m.exp(m.pi*m.re(t)/4)
 data={'row':row,'dps':dps,'a':[str(v) for v in a],'u':[str(v) for v in u], 'scaled_equality_residual':str(m.norm(M*u-b,p=m.inf)),'dft_residual':str(m.norm(C*a-a,p=m.inf)), 'min_ratio':str(min(a[r]/base[r] for r in range(Q))), 'max_ratio':str(max(a[r]/base[r] for r in range(Q))), 'F_scaled':enc(jx[0]*scale),'Ft_scaled':enc(jx[1]*scale),'Ftt_scaled':enc(jx[2]*scale),'seconds':time.monotonic()-start}
 return data

def sourcecheck(arg):
 row,pivots=arg;start=time.monotonic();m.mp.dps=190
 a=[m.mpf(v) for v in row['a']];t=m.mpc(row['row']['T'],str(row['row']['y']));q=Q
 def kernel(x):
  c=m.pi*m.exp(2*x)/q
  nmax=int(m.ceil(m.sqrt((m.mp.dps*m.log(10)+35)/c)))
  return 2*m.exp(x/2)*m.fsum(a[n%q]*m.exp(-c*n*n) for n in range(1,nmax+1))
 panels=[m.mpf(i)/8 for i in range(33)]
 def integral(tt,derivative=False):
  if derivative:return m.quad(lambda x:-x*kernel(x)*m.sin(tt*x),panels)
  return m.quad(lambda x:kernel(x)*m.cos(tt*x),panels)
 J=integral(t);Jp=integral(t,True);scale=m.exp(m.pi*m.re(t)/4)
 F=a[0]/2-(m.mpf('.25')+t*t)*J
 Ft=-2*t*J-(m.mpf('.25')+t*t)*Jp
 anchor=t+m.mpf('.01');Fa=a[0]/2-(m.mpf('.25')+anchor*anchor)*integral(anchor)
 independent=(jets(anchor,1)[0]*m.matrix(a))[0]
 # Control explicit pole term and analytic baseline identity.
 base=m.matrix([1+m.sqrt(q)*(r==0) for r in range(q)])
 baseline=(jets(t,1)[0]*base)[0];s=m.mpf('.5')+1j*t
 xi=s*(s-1)/2*m.pi**(-s/2)*m.gamma(s/2)*m.zeta(s)
 normal=2*q**m.mpf('.25')*m.cos(t*m.log(q)/2)*xi
 return {'row':row['row'],'F_scaled':enc(F*scale),'Ft_scaled':enc(Ft*scale),'anchor_difference_scaled':enc((Fa-independent)*scale),'baseline_difference_scaled':enc((baseline-normal)*scale),'seconds':time.monotonic()-start,'dps':190,'x_cutoff':4,'tail_exponent_min':str(m.pi*m.exp(8)/q)}

def main():
 start=time.monotonic();m.mp.dps=50
 B0,C=basis(50,list(range((Q+1)//2)));arr=np.array(B0.tolist(),float);_,R,p=qr(arr,pivoting=True,mode='economic');rank=int(np.sum(np.abs(np.diag(R))>1e-12));pivots=p[:rank].tolist();dump('basis.json',{'q':Q,'rank':rank,'pivots':pivots,'qr_diagonal':np.diag(R).tolist()})
 jobs=[(T,y,pivots) for T in SPEC['heights'] for y in SPEC['imaginary']]
 # Short pilot is part of same guard; its real result is retained.
 with ProcessPoolExecutor(max_workers=14) as pool:
  pilot=pool.submit(discover,jobs[0]).result(timeout=max(1,min(100,DEADLINE-time.monotonic()-150)))
  results=[pilot];dump('pilot.json',pilot)
  if time.monotonic()+pilot['seconds']*2>DEADLINE-170:dump('summary.json',{'status':'pilot-too-slow','results':results});return
  with open('discovery.jsonl','w',buffering=1) as f:
   f.write(json.dumps(pilot)+'\n')
   for future in as_completed([pool.submit(discover,j) for j in jobs[1:]],timeout=max(1,DEADLINE-time.monotonic()-150)):
    try:result=future.result()
    except Exception as e:result={'error':repr(e),'traceback':traceback.format_exc()}
    results.append(result);f.write(json.dumps(result)+'\n')
  accepted=sorted([r for x in results for r in x.get('rows',[]) if r['success']],key=lambda r:(not r['full_moments'],r['T'],r['y']))
  selected=accepted[:4];dump('selected.json',selected)
  refined=[]
  with open('validation.jsonl','w',buffering=1) as f:
   futures=[pool.submit(refine,(r,pivots,dps)) for r in selected for dps in [100,160]]
   for future in as_completed(futures,timeout=max(1,DEADLINE-time.monotonic()-80)):
    try:result=future.result()
    except Exception as e:result={'error':repr(e),'traceback':traceback.format_exc()}
    refined.append(result);f.write(json.dumps(result)+'\n')
  high=[r for r in refined if r.get('dps')==160 and m.mpf(r['min_ratio'])>0]
  checked=[]
  with open('source-validation.jsonl','w',buffering=1) as f:
   for future in as_completed([pool.submit(independent.run,(r,n,panels)) for r in high for n,panels in [(64,32),(96,40)]],timeout=max(1,DEADLINE-time.monotonic()-5)):
    try:result=future.result()
    except Exception as e:result={'error':repr(e),'traceback':traceback.format_exc()}
    checked.append(result);f.write(json.dumps(result)+'\n')
  dump('summary.json',{'status':'finished','accepted':len(accepted),'selected':len(selected),'validated':len(high),'source_checked':len(checked),'seconds':time.monotonic()-start})
if __name__=='__main__':main()
