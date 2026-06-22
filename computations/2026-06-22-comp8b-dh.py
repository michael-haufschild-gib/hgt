"""comp8b / rt#38: Davenport-Heilbronn faithful source gate.
DH f(s)=(1-i k)/2 L(s,chi)+(1+i k)/2 L(s,chibar), chi mod 5 order 4 (odd, a=1),
k=(sqrt(10-2sqrt5)-2)/(sqrt5-1). Same mod-5 gamma factor as an odd char => protector a=1.
f has FE-symmetric zeros incl OFF-LINE ones (broken Euler product). Completed Xi_DH even.
Faithful moments T_k^DH=2(-1)^{k+1} k c_{2k}, c_{2k}=[w^{2k}]logXi_DH; ODD coeffs must vanish
(evenness validation). Then find d* = first d with lambda_min(H^0_DH, M_triv)<0 (off-line caught)."""
import sys, mpmath as mp, importlib.util
def imp(n,f):
    s=importlib.util.spec_from_file_location(n,f); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
H=imp("hgtlib","hgtlib.py"); L=imp("hgtlib_L","hgtlib_L.py")
DPS=int(sys.argv[1]) if len(sys.argv)>1 else 340; DMAX=int(sys.argv[2]) if len(sys.argv)>2 else 40
mp.mp.dps=DPS
q=5; a=1
chi   ={1:mp.mpc(1,0),2:mp.mpc(0,1),3:mp.mpc(0,-1),4:mp.mpc(-1,0)}
chibar={r:mp.conj(v) for r,v in chi.items()}
kk=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)

def L_taylor_chi(chimap, M):
    "a_m=L^{(m)}(1/2,chi)/m! for general complex char mod 5 via convolution."
    half=mp.mpf('0.5'); lq=mp.log(q)
    e=[mp.power(q,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
    out=[mp.mpc(0) for _ in range(M+1)]
    for r in range(1,q):
        c=chimap[r]
        h=[mp.zeta(half,mp.mpf(r)/q,i)/mp.factorial(i) for i in range(M+1)]
        for m in range(M+1):
            out[m]+=c*mp.fsum(e[j]*h[m-j] for j in range(m+1))
    return out

KMAX=2*DMAX+1; M=2*KMAX
ax =L_taylor_chi(chi,   M)
axb=L_taylor_chi(chibar,M)
# f(1/2+w) Taylor: a_m^f = (1-i k)/2 a_m^chi + (1+i k)/2 a_m^chibar  (real)
af=[ ((1-1j*kk)/2)*ax[m] + ((1+1j*kk)/2)*axb[m] for m in range(M+1)]
af=[mp.re(x) for x in af]
# log f series
g=[mp.mpf(0)]*(M+1); g[0]=mp.log(af[0])
for m in range(1,M+1):
    s=mp.fsum(n*g[n]*af[m-n] for n in range(1,m)); g[m]=(m*af[m]-s)/(m*af[0])
# full logXi_DH even/odd coeffs c_n = [w^n]( logGamma(3/4+w/2) + log f ); linear/const dropped
b=mp.mpf(3)/4
def cn(n):
    cg = mp.polygamma(n-1,b)/(mp.factorial(n)*mp.power(2,n)) if n>=1 else mp.mpf(0)
    return cg + g[n]
# evenness validation: odd coeffs c_3,c_5,c_7 should ~0 (only linear c_1 nonzero from gamma/qlog, ignore)
print("# evenness check (odd c_n should be ~0):")
for n in [3,5,7,9]:
    print(f"   c_{n} = {mp.nstr(cn(n),4)}")
# moments
T=[None]+[2*((-1)**(k+1))*k*cn(2*k) for k in range(1,KMAX+1)]
print(f"# T_1={mp.nstr(T[1],10)} T_2={mp.nstr(T[2],10)} T_3={mp.nstr(T[3],10)}  (k=catalan note: real)")
B=L.Mtriv_L_matrix(DMAX,a)
A=H.H0_matrix(DMAX,T)
sub=lambda Mx,d: mp.matrix([[Mx[i,j] for j in range(d+1)] for i in range(d+1)])
print("# scanning d for first NON-PSD (lambda_min(H^0_DH,M_triv)<0 => off-line zero detected):")
dstar=None
for d in range(2,DMAX+1):
    Ad,Bd=sub(A,d),sub(B,d)
    try:
        Lc=mp.cholesky(Bd)
    except: print(f"  d={d}: M_triv chol fail"); break
    Li=mp.inverse(Lc); C=Li*Ad*Li.T; C=(C+C.T)/2
    E=mp.eigsy(C,eigvals_only=True); m=min(E)
    if d%4==0 or m<0:
        print(f"  d={d:2d}  lambda_min={mp.nstr(m,5)}  log10|.|={float(mp.log10(abs(m))):.2f}  {'<-- NOT PSD' if m<0 else ''}",flush=True)
    if m<0 and dstar is None:
        dstar=d; print(f"  *** d* = {d} : DH off-line zero DETECTED (faithful failure) ***"); break
if dstar is None: print(f"# no failure up to d={DMAX} (off-line zeros higher than this degree reaches)")
