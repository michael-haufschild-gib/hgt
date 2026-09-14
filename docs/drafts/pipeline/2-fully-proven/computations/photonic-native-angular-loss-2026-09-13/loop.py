"""Physical two-layer temporal crystal, finite-energy lattice, three readers.

No zeta, primes, zero ordinates or prescribed spectral data enter this model.
"""
import json,os,time,math
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
from scipy.linalg import eigh,svd

def save(name,d):
 p=Path(name);q=p.with_suffix(p.suffix+'.tmp');q.write_text(json.dumps(d,indent=2)+'\n');q.replace(p)
def budget():
 if time.monotonic()>float(os.environ.get('CAMPAIGN_DEADLINE','inf')):raise TimeoutError('whole-family deadline')
def enc(z):return [float(np.real(z)),float(np.imag(z))]
def matenc(a):return [[enc(v) for v in r] for r in a]
def osc(eps,phase):
 c,s=np.cos(phase),np.sin(phase);r=np.sqrt(eps)
 return np.array([[c,s/r],[-r*s,c]])
def path(m,t):
 lam=(m+np.sqrt(m*m-4))/2
 if t<=.5:return osc(1,np.pi*t)
 return osc(lam*lam,np.pi*(t-.5))@osc(1,np.pi/2)
def lattice(m):
 lam=(m+np.sqrt(m*m-4))/2
 return np.array([[1/lam,-1],[lam,-1]])/np.sqrt(lam-1/lam)
class Code:
 def __init__(self,A,dim,N,pa,pb,pref=None):
  self.A=np.asarray(A,dtype=complex);self.dim=dim;self.N=N;self.pa=pa;self.pb=pb
  a,b,dd=A[0,0],A[0,1],A[1,1]
  self.pref=1/np.sqrt(2*np.pi*1j*b) if pref is None else pref
  self.u=1j*dd/(2*b);self.v=-1j/b;self.w=1j*a/(2*b)
  n=np.arange(-N,N+1);self.phase=np.exp(2j*np.pi*pb*n)
  L=np.sqrt(2*np.pi*dim)
  self.q=[L*(n+(j+pa)/dim) for j in range(dim)]
def overlap(a,b):
 U=np.conj(a.u)+b.u
 if U.real>=0:raise ValueError('non-integrable Gaussian kernel')
 al=np.conj(a.w)-np.conj(a.v)**2/(4*U);be=b.w-b.v**2/(4*U);ga=-np.conj(a.v)*b.v/(2*U)
 pref=np.conj(a.pref)*b.pref*np.sqrt(np.pi/(-U));X=np.empty((a.dim,b.dim),complex)
 phases=np.conj(a.phase)[:,None]*b.phase[None,:]
 for j in range(a.dim):
  r=a.q[j][:,None]
  for k in range(b.dim):
   s=b.q[k][None,:];X[j,k]=pref*np.sum(phases*np.exp(al*r*r+be*s*s+ga*r*s))
 return X
def inverse_root(G):
 G=(G+G.conj().T)/2;ev,V=eigh(G)
 if min(ev)<=0:raise ValueError('non-positive Gram spectrum')
 return (V*(1/np.sqrt(ev)))@V.conj().T,ev

def describe(K,J):
 U,sv,Vh=svd(K);polar=U@Vh
 z=np.trace(J.conj().T@polar)
 distance=np.sqrt(max(0,2-2*abs(z)/len(K)))
 return dict(matrix=matenc(K),singular_values=sv.tolist(),polar=matenc(polar),
  polar_eigenvalues=[enc(z) for z in np.linalg.eigvals(polar)],
  mean_survival=float(np.mean(sv*sv)),worst_survival=float(min(sv)**2),
  projective_distance_to_ideal=float(distance),trace_phase_relative_to_ideal=float(np.angle(z)))

def experiment(job):
 d=job['dim'];N=job['N'];steps=job['steps'];delta=float(job['delta']);m=job['m']
 pa=pb=.5 if d%2 else 0
 g=lattice(m);C=np.array([[np.cosh(delta),-1j*np.sinh(delta)],[1j*np.sinh(delta),np.cosh(delta)]])
 Fs=[path(m,i/steps) for i in range(steps+1)]
 Aint=np.array([[m,-1],[1,0]])
 algebra_error=float(np.linalg.norm(Fs[-1]@g+g@Aint))
 codes=[Code(C@F@g,d,N,pa,pb) for F in Fs]
 inv=[];gram=[];spectrum=[]
 for a in codes:
  G=overlap(a,a);W,ev=inverse_root(G);gram.append(G);inv.append(W);spectrum.append(ev.tolist())
 close=inv[0]@overlap(codes[0],codes[-1])@inv[-1]
 closure_error=float(np.linalg.norm(close.conj().T@close-np.eye(d)))
 if closure_error>1e-7:raise ValueError('endpoint code failed modular closure: '+str(closure_error))
 # J is the endpoint logical action of the ideal lattice relabeling in orthonormal encoding coordinates.
 J=svd(close)[0]@svd(close)[2]
 Lg=Ld=np.eye(d,dtype=complex);max_step_sv=0.;max_norm_error=0.
 raw=Code(C@g,d,N,pa,pb)
 samples=[]
 for i in range(steps):
  budget();D=Fs[i+1]@np.linalg.inv(Fs[i]);a=codes[i];B=D@a.A
  phase_ratio=a.A[0,1]/B[0,1]
  if abs(np.angle(phase_ratio))>np.pi/2:raise ValueError('metaplectic step too large')
  prop=Code(B,d,N,pa,pb,a.pref*np.sqrt(phase_ratio))
  kgeom=inv[i+1]@overlap(codes[i+1],a)@inv[i]
  kdrive=inv[i+1]@overlap(codes[i+1],prop)@inv[i]
  Lg=kgeom@Lg;Ld=kdrive@Ld
  ne=float(np.linalg.norm(inv[i]@overlap(prop,prop)@inv[i]-np.eye(d)));max_norm_error=max(ne,max_norm_error)
  max_step_sv=max(max_step_sv,float(max(svd(kgeom,compute_uv=False))),float(max(svd(kdrive,compute_uv=False))))
  Braw=D@raw.A;raw=Code(Braw,d,N,pa,pb,raw.pref*np.sqrt(raw.A[0,1]/Braw[0,1]))
  if i in [0,steps//2-1,steps-1]:samples.append(dict(i=i,geometric_step=matenc(kgeom),driven_step=matenc(kdrive),source_A=matenc(a.A),target_A=matenc(codes[i+1].A),propagated_A=matenc(prop.A),propagated_pref=enc(prop.pref)))
 bare=inv[0]@overlap(codes[0],raw)@inv[0]
 if max_norm_error>1e-7 or max_step_sv>1+1e-7:raise ValueError('unitarity/contraction control failed')
 return dict(algebra_error=algebra_error,endpoint_closure_error=closure_error,max_unitary_gram_error=max_norm_error,max_step_singular_value=max_step_sv,
  lattice=matenc(g),monodromy=matenc(Fs[-1]),ideal_logical_action=matenc(J),
  geometric=describe(close@Lg,J),driven_monitored=describe(close@Ld,J),unmonitored=describe(bare,J),
  gram_spectra=spectrum,selected_steps=samples,phase_a=pa,phase_b=pb)

def work(job):
 start=time.monotonic();row=dict(job=job)
 try:row.update(experiment(job));row['status']='ok'
 except Exception as e:row.update(status='error',error=repr(e))
 row['seconds']=time.monotonic()-start;save('case-'+str(job['id'])+'.json',row);return row
if __name__=='__main__':
 jobs=json.loads(Path('jobs.json').read_text());start=time.monotonic();rows=[]
 r=work(jobs[0]);rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print('pilot',r['status'],r['seconds'],r.get('error',''),flush=True)
 if r['status']!='ok' or r['seconds']>60:raise SystemExit('pilot failed or oversized')
 with ProcessPoolExecutor(max_workers=14) as ex:
  for f in as_completed([ex.submit(work,j) for j in jobs[1:]]):
   r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['id'],r['status'],r['seconds'],r.get('error',''),flush=True)
