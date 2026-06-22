"""comp8b2: push DH degree to catch the off-line flip (gamma~85.7, beta'=0.308).
Build faithful DH moments once at high dps; scan d for first lambda_min(H^0_DH,M_triv)<0."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py")
DPS=int(sys.argv[1]); DMIN=int(sys.argv[2]); DMAX=int(sys.argv[3])
mp.mp.dps=DPS
q=5; a=1
chi   ={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}
chibar={r:mp.conj(v) for r,v in chi.items()}
kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
def L_taylor_chi(cm,M):
    half=mp.mpf('0.5'); lq=mp.log(q)
    e=[mp.power(q,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
    out=[mp.mpc(0)]*(M+1)
    for r in range(1,q):
        c=cm[r]; h=[mp.zeta(half,mp.mpf(r)/q,i)/mp.factorial(i) for i in range(M+1)]
        for m in range(M+1): out[m]=out[m]+c*mp.fsum(e[j]*h[m-j] for j in range(m+1))
    return out
KMAX=2*DMAX+1; M=2*KMAX
import time; t0=time.time()
ax=L_taylor_chi(chi,M); axb=L_taylor_chi(chibar,M)
af=[mp.re(((1-1j*kk)/2)*ax[m]+((1+1j*kk)/2)*axb[m]) for m in range(M+1)]
g=[mp.mpf(0)]*(M+1); g[0]=mp.log(af[0])
for m in range(1,M+1):
    s=mp.fsum(n*g[n]*af[m-n] for n in range(1,m)); g[m]=(m*af[m]-s)/(m*af[0])
b=mp.mpf(3)/4
cn=lambda n: mp.polygamma(n-1,b)/(mp.factorial(n)*mp.power(2,n))+g[n]
T=[None]+[2*((-1)**(k+1))*k*cn(2*k) for k in range(1,KMAX+1)]
B=L.Mtriv_L_matrix(DMAX,a); A=H.H0_matrix(DMAX,T)
print(f"# moments+matrices built in {time.time()-t0:.0f}s, dps={DPS}, scan d={DMIN}..{DMAX}",flush=True)
sub=lambda Mx,d: mp.matrix([[Mx[i,j] for j in range(d+1)] for i in range(d+1)])
for d in range(DMIN,DMAX+1):
    Ad,Bd=sub(A,d),sub(B,d)
    Lc=mp.cholesky(Bd); Li=mp.inverse(Lc); C=Li*Ad*Li.T; C=(C+C.T)/2
    E=mp.eigsy(C,eigvals_only=True); m=min(E)
    print(f"  d={d:2d}  lambda_min={mp.nstr(m,5)} (log10|.|={float(mp.log10(abs(m))):.1f}) {'<-- NOT PSD: DH off-line DETECTED' if m<0 else ''}",flush=True)
    if m<0: print(f"  *** d* = {d} for DH off-line zero (gamma=85.7, sigma=0.808) ***"); break
