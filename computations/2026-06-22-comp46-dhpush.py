"""comp46 / rt#46 / gpt38-c2: push real Davenport-Heilbronn K_d past the predicted d*~55.
Optimized moment build: Hurwitz Taylor coeffs of zeta(1/2+w, r/5) via Cauchy (mp.taylor
method='quad'), not per-order derivatives. Find first d with lambda_min(H^0_DH,M_triv)<0."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py")
DPS=int(sys.argv[1]); DMIN=int(sys.argv[2]); DMAX=int(sys.argv[3])
mp.mp.dps=DPS
q=5; a=1
chi={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}
chibar={r:mp.conj(v) for r,v in chi.items()}
kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
KMAX=2*DMAX+1; M=2*KMAX
half=mp.mpf('0.5'); lq=mp.log(q)
import time; t0=time.time()
# Cauchy Taylor of zeta(1/2+w, r/5) once per r (radius 0.4 < pole at w=1/2)
hcoef={r: mp.taylor(lambda w,rr=r: mp.zeta(half+w, mp.mpf(rr)/q), 0, M, method='quad', radius=mp.mpf('0.4')) for r in range(1,q)}
e=[mp.power(q,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
def Ltay(cm):
    out=[mp.mpc(0)]*(M+1)
    for r in range(1,q):
        c=cm[r]; h=hcoef[r]
        for m in range(M+1): out[m]=out[m]+c*mp.fsum(e[j]*h[m-j] for j in range(m+1))
    return out
ax=Ltay(chi); axb=Ltay(chibar)
af=[mp.re(((1-1j*kk)/2)*ax[m]+((1+1j*kk)/2)*axb[m]) for m in range(M+1)]
g=[mp.mpf(0)]*(M+1); g[0]=mp.log(af[0])
for m in range(1,M+1):
    s=mp.fsum(n*g[n]*af[m-n] for n in range(1,m)); g[m]=(m*af[m]-s)/(m*af[0])
b=mp.mpf(3)/4
cn=lambda n: mp.polygamma(n-1,b)/(mp.factorial(n)*mp.power(2,n))+g[n]
T=[None]+[2*((-1)**(k+1))*k*cn(2*k) for k in range(1,KMAX+1)]
B=L.Mtriv_L_matrix(DMAX,a); A=H.H0_matrix(DMAX,T)
print(f"# moments built in {time.time()-t0:.0f}s (Cauchy), dps={DPS}, scan d={DMIN}..{DMAX}",flush=True)
sub=lambda Mx,d: mp.matrix([[Mx[i,j] for j in range(d+1)] for i in range(d+1)])
for d in range(DMIN,DMAX+1):
    Ad,Bd=sub(A,d),sub(B,d); Li=mp.inverse(mp.cholesky(Bd)); C=Li*Ad*Li.T; C=(C+C.T)/2
    m=min(mp.eigsy(C,eigvals_only=True))
    print(f"  d={d:2d} lambda_min={mp.nstr(m,5)} (log10|.|={float(mp.log10(abs(m))):.1f}) {'<-- DH OFF-LINE DETECTED' if m<0 else ''}",flush=True)
    if m<0: print(f"  *** d* = {d} : DH off-line zero (gamma=85.7) caught ***"); break
