"""comp75 [P5] / gpt/43 #5 — complex-character / self-dual product test.

For a COMPLEX primitive chi (mod 5, order 4: chi(2)=i; chi(-1)=-1 => odd, a=1), the self-dual
completed object is  Lambda(s,chi) Lambda(s,chibar).  chi,chibar share parity => the Gamma-factor
is Gamma((s+a)/2)^2  (SQUARED): trivial zeros at s=-a-2l of MULTIPLICITY 2, all at the SAME images
y_l=-(2l+a+1/2)^{-2}.  Moments are real: T_k^prod = T_k(chi)+T_k(chibar) = 2 Re T_k(chi), with the
archimedean (polygamma) part DOUBLED (squared Gamma) and the prime part = 2 Re g_{2k}.

Question (gpt/43): is the boundary still RANK ONE (=> N_1), or does the squared Gamma force RANK TWO
(=> N_2, rank = #Gamma channels)?  Since chi,chibar share ONE Gamma channel, the first trivial zero
is a DOUBLED single atom 2 a_* v_* v_*^T (rank one) -- test whether inertia(H^- )=(d,1) with it, and
whether the scalar gap s_d^prod>0 (GRH for the product).  Control: real odd chi3 (single Gamma)."""
import mpmath as mp, sys
sys.path.insert(0,'.')
from hgtlib_L import T_moments_L, CHARS

# ---- complex primitive character mod 5, order 4 (chi(2)=i); r=1..4
Q5=5; A5=1                      # odd
CHI5 = {1:mp.mpc(1,0), 2:mp.mpc(0,1), 3:mp.mpc(0,-1), 4:mp.mpc(-1,0)}

def Tk_complex_selfdual(kmax):
    "T_k for Lambda(chi)Lambda(chibar), chi=mod5 order4: real, arch DOUBLED + 2 Re(prime)."
    M=2*kmax+1; half=mp.mpf('0.5'); lq=mp.log(Q5)
    e=[mp.power(Q5,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
    A=[mp.mpc(0)]*(M+1)
    for r in range(1,Q5):
        c=CHI5[r]
        h=[mp.zeta(half, mp.mpf(r)/Q5, i)/mp.factorial(i) for i in range(M+1)]
        for m in range(M+1):
            A[m]+= c*mp.fsum(e[j]*h[m-j] for j in range(m+1))
    g=[mp.mpc(0)]*(M+1); g[0]=mp.log(A[0])
    for m in range(1,M+1):
        s=mp.fsum(n*g[n]*A[m-n] for n in range(1,m))
        g[m]=(m*A[m]-s)/(m*A[0])
    b=(mp.mpf(A5)+half)/2
    T=[None]*(kmax+1)
    for k in range(1,kmax+1):
        arch=mp.polygamma(2*k-1,b)/(mp.factorial(2*k)*mp.power(4,k))   # one Gamma channel
        c2k = 2*arch + 2*mp.re(g[2*k])                                 # squared Gamma + 2Re(prime)
        T[k]=2*((-1)**(k+1))*k*c2k
    return T

def vy(y,d): return mp.matrix([[y**i] for i in range(d+1)])
def H0(d,T): return mp.matrix([[T[i+j+1] for j in range(d+1)] for i in range(d+1)])
def inertia(Asym):
    ev=mp.eigsy(Asym, eigvals_only=True); tol=mp.mpf(10)**(-40)
    return (sum(1 for e in ev if e>tol), sum(1 for e in ev if e<-tol), sum(1 for e in ev if abs(e)<=tol))

YS = -mp.power(mp.mpf(3)/2,-2)          # y_* = -(a+1/2)^{-2} = -4/9 (odd)
AST_single = mp.power(mp.mpf(3)/2,-2)   # a_* = 4/9
print(f"y_* = {mp.nstr(YS,8)},  a_*(single)=4/9={mp.nstr(AST_single,8)},  a_*(product, doubled)=8/9")

for d in (6,8,10,12):
    mp.mp.dps=int(6.5*d)+150
    Tp = Tk_complex_selfdual(2*d+2)
    Hp = H0(d,Tp); vs=vy(YS,d); vv=vs*vs.T
    i0=inertia(Hp)
    H_single = Hp - AST_single*vv
    H_double = Hp - 2*AST_single*vv
    is_,id_ = inertia(H_single), inertia(H_double)
    # scalar gaps for both removal conventions
    def gap(c, H):
        Hi=mp.inverse(H); m=(vs.T*Hi*vs)[0]; return c+1/m
    g1=gap(AST_single,H_single); g2=gap(2*AST_single,H_double)
    print(f"\nd={d} (dps={mp.mp.dps}):")
    print(f"  inertia H^0(prod)              = {i0}   (PSD/(d+1,0) on GRH)")
    print(f"  inertia H^0 - a_*  v v^T (sing)= {is_}   scalar gap s_d={mp.nstr(g1,6)}")
    print(f"  inertia H^0 - 2a_* v v^T (dbl) = {id_}   scalar gap s_d={mp.nstr(g2,6)}")

print("\n=== control: real odd chi3 (single Gamma, established rank-one (d,1)) ===")
for d in (8,12):
    mp.mp.dps=int(6.5*d)+150
    T=T_moments_L('chi3',2*d+2); H=H0(d,T); vs=vy(YS,d)
    Hm=H-AST_single*(vs*vs.T)
    Hi=mp.inverse(Hm); m=(vs.T*Hi*vs)[0]
    print(f"  d={d}: inertia H^0={inertia(H)}, inertia H^-={inertia(Hm)}, s_d={mp.nstr(AST_single+1/m,6)}")
print("\nDONE")
