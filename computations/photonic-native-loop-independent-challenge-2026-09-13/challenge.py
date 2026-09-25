from metric import *

def osc(eps,phase):
 c,s=mp.cos(phase),mp.sin(phase);r=mp.sqrt(eps)
 return mp.matrix([[c,s/r],[-r*s,c]])
def flow(m,t):
 lam=(m+mp.sqrt(m*m-4))/2
 if t<=mp.mpf('.5'):return osc(1,mp.pi*t)
 return osc(lam*lam,mp.pi*(t-mp.mpf('.5')))*osc(1,mp.pi/2)
def lattice(m):
 lam=(m+mp.sqrt(m*m-4))/2
 return mp.matrix([[1/lam,-1],[lam,-1]])/mp.sqrt(lam-1/lam)
class Native(Code):
 def __init__(self,A,dim,N,pa,pb,pref=None):
  self.A=A;self.dim=dim;self.nmax=N;self.phase_a=pa;self.phase_b=pb;self.L=mp.sqrt(2*mp.pi*dim)
  a,b,dd=A[0,0],A[0,1],A[1,1];self.pref=1/mp.sqrt(2*mp.pi*1j*b) if pref is None else pref
  self.u=1j*dd/(2*b);self.v=-1j/b;self.w=1j*a/(2*b)
def invroot(G):
 ev,V=mp.eighe((G+G.H)/2);assert min(ev)>0
 return V*mp.diag([1/mp.sqrt(v) for v in ev])*V.H,ev

def describe(K,J):
 U,sv,V=mp.svd(K);polar=U*V;z=trace(J.H*polar);dist=mp.sqrt(max(mp.mpf(0),2-2*abs(z)/K.rows))
 return dict(matrix=matenc(K),singular_values=[str(z) for z in sv],polar=matenc(polar),mean_survival=str(mp.fsum(v*v for v in sv)/K.rows),worst_survival=str(min(sv)**2),projective_distance_to_ideal=str(dist),trace_phase_relative_to_ideal=str(mp.arg(z)))

def experiment(j):
 mp.mp.dps=j['dps'];d=j['dim'];N=j['N'];n=j['steps'];delta=mp.mpf(j['delta']);m=j['m'];pa=pb=mp.mpf('.5') if d%2 else mp.mpf(0)
 g=lattice(m);C=mp.matrix([[mp.cosh(delta),-1j*mp.sinh(delta)],[1j*mp.sinh(delta),mp.cosh(delta)]]);Fs=[flow(m,mp.mpf(i)/n) for i in range(n+1)]
 codes=[Native(C*F*g,d,N,pa,pb) for F in Fs];inv=[];grams=[];spectra=[]
 for a in codes:
  G=overlap(a,a,'theta');W,ev=invroot(G);inv.append(W);grams.append(G);spectra.append([str(v) for v in ev])
 close=inv[0]*overlap(codes[0],codes[-1],'theta')*inv[-1];err=mp.norm(close.H*close-mp.eye(d))
 assert err<mp.mpf('1e-25')
 U,sv,V=mp.svd(close);J=U*V;Lg=mp.eye(d);Ld=mp.eye(d);raw=Native(C*g,d,N,pa,pb);ne=mp.mpf(0)
 for i in range(n):
  budget();D=Fs[i+1]*Fs[i]**-1;a=codes[i];B=D*a.A;ratio=a.A[0,1]/B[0,1];assert abs(mp.arg(ratio))<mp.pi/2
  prop=Native(B,d,N,pa,pb,a.pref*mp.sqrt(ratio))
  Kg=inv[i+1]*overlap(codes[i+1],a,'theta')*inv[i];Kd=inv[i+1]*overlap(codes[i+1],prop,'theta')*inv[i]
  Lg=Kg*Lg;Ld=Kd*Ld
  if i in [0,n//2-1,n-1]:ne=max(ne,mp.norm(inv[i]*overlap(prop,prop,'theta')*inv[i]-mp.eye(d)))
  R=D*raw.A;raw=Native(R,d,N,pa,pb,raw.pref*mp.sqrt(raw.A[0,1]/R[0,1]))
 bare=inv[0]*overlap(codes[0],raw,'theta')*inv[0];assert ne<mp.mpf('1e-25')
 return dict(endpoint_closure_error=str(err),selected_unitary_gram_error=str(ne),ideal_logical_action=matenc(J),geometric=describe(close*Lg,J),driven_monitored=describe(close*Ld,J),unmonitored=describe(bare,J),gram_spectra=spectra)

def work(j):
 start=time.monotonic();r=dict(job=j)
 try:r.update(experiment(j));r['status']='ok'
 except Exception as e:r.update(status='error',error=repr(e))
 r['seconds']=time.monotonic()-start;save('case-'+str(j['id'])+'.json',r);return r
if __name__=='__main__':
 jobs=json.loads(Path('jobs.json').read_text());start=time.monotonic();rows=[];r=work(jobs[0]);rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print('pilot',r['status'],r['seconds'],r.get('error',''),flush=True)
 if r['status']!='ok' or r['seconds']>75:raise SystemExit('pilot failed or oversized')
 with ProcessPoolExecutor(max_workers=14) as ex:
  for f in as_completed([ex.submit(work,j) for j in jobs[1:]]):
   r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['id'],r['status'],r['seconds'],r.get('error',''),flush=True)
