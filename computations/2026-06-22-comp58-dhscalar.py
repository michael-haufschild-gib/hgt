"""comp58 / rt#58 / gpt39 c4: DH past threshold via batched Hurwitz moments (the #46/#58 FIX).
Track the SCALAR gap s_d=a_*,DH * margin and the rank-one inertia(H^-_DH): does the off-line
zero (gamma=85.7) flip margin<0 / break inertia (d,1)->(d-1,2)? a_*,DH=(3/2)^{-2}=4/9 (odd, mod 5)."""
import sys, time, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py"); hb=imp("hb","2026-06-22-hurwitz-batch.py")
DPS=int(sys.argv[1]); DMIN=int(sys.argv[2]); DMAX=int(sys.argv[3])
mp.mp.dps=DPS
q=5; a=1
chi={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}
chibar={r:mp.conj(v) for r,v in chi.items()}
kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
KMAX=2*DMAX+1; M=2*KMAX; half=mp.mpf('0.5'); lq=mp.log(q)
t0=time.time()
hco={r: hb.hurwitz_taylor(mp.mpf(r)/q, half, M) for r in range(1,q)}   # 4 batched calls
e=[mp.power(q,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
def Ltay(cm):
    out=[mp.mpc(0)]*(M+1)
    for r in range(1,q):
        c=cm[r]; h=hco[r]
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
ystar=-mp.power(mp.mpf('1.5'),-2); astar=mp.power(mp.mpf('1.5'),-2)  # -4/9, 4/9
print(f"# DH moments built in {time.time()-t0:.0f}s (batched Hurwitz, dps={DPS}); scan d={DMIN}..{DMAX}; a_*={mp.nstr(astar,5)}",flush=True)
sub=lambda Mx,d: mp.matrix([[Mx[i,j] for j in range(d+1)] for i in range(d+1)])
ev=lambda y,d: mp.matrix([mp.power(y,i) for i in range(d+1)])
for d in range(DMIN,DMAX+1):
    Ad,Bd=sub(A,d),sub(B,d); Li=mp.inverse(mp.cholesky(Bd)); C=Li*Ad*Li.T; margin=min(mp.eigsy((C+C.T)/2,eigvals_only=True))
    v=ev(ystar,d); Hm=Ad-astar*(v*v.T); Em=mp.eigsy((Hm+Hm.T)/2,eigvals_only=True)
    ip=sum(1 for x in Em if x>0); inn=sum(1 for x in Em if x<0)
    s_d=astar*margin
    flag=""
    if margin<0: flag=" <-- DH DETECTED: margin<0"
    if (ip,inn)!=(d,1): flag+=f" [inertia(H^-)=({ip},{inn}) != (d,1)!]"
    print(f"  d={d:2d} margin={mp.nstr(margin,5)} s_d={mp.nstr(s_d,5)} inertia(H^-)=({ip},{inn}){flag}",flush=True)
    if margin<0: print(f"  *** d*={d}: DH off-line zero caught; scalar gap s_d turned negative ***"); break
