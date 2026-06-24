"""comp72 [P2] / gpt/43 #2 — large-scale generalized-Nevanlinna N_kappa Pick stress test.

m_sigma(z) = int dsigma/(t-z),  sigma = nu' - a_* delta_{y_*},
  nu' = sum_n 2 y_n delta_{y_n},  y_n = 1/gamma_n^2 (ZETA, on RH; real>0),  y_*=-0.16, a_*=0.16.
A DH-like FAKE adds an off-line FE quartet w in {+-d +- i g0}, atoms y=-1/w^2 (complex),
small folded weight; on RH d=0 so the quartet sits at y=1/g0^2>0 (a genuine-looking atom),
off-line d>0 makes the atoms complex -> may add a 2nd negative square.

Pick kernel  P_ij = [m(z_i) - conj(m(z_j))] / (z_i - conj(z_j))  is Hermitian; #neg eigenvalues
= kappa (the number of negative squares). N_kappa <=> kappa stable as samples/d grow.
Inertia via the real embedding [[Re,-Im],[Im,Re]] (eigs doubled) + symmetric eig.

PUSH: sample size M and zero-truncation N; ZETA (expect kappa=1) and off-line quartets
(does kappa->2, and is it sampling/height-limited?). Outcome is NOT predictable a priori."""
import mpmath as mp, sys
sys.path.insert(0,'.')
from hgtlib import load_zeros
mp.mp.dps = 60

A_STAR = mp.mpf('0.16'); Y_STAR = -A_STAR
G = load_zeros('zeros400.txt', 400)
Y = [1/(g*g) for g in G]                       # zeta reciprocal atoms y_n>0

def quartet_atoms(beta, g0):
    d = mp.mpf(beta)-mp.mpf('0.5'); g0=mp.mpf(g0)
    ws=[mp.mpc(d,g0),mp.mpc(-d,g0),mp.mpc(d,-g0),mp.mpc(-d,-g0)]
    return [-1/(w*w) for w in ws]              # 4 atoms (conj symmetric)

def m_sigma(z, N, fake=None, wq=mp.mpf('0.5')):
    "Cauchy transform of sigma truncated to N zeros (+optional off-line quartet, folded weight wq/2 each)."
    s = mp.fsum(2*Y[n]/(Y[n]-z) for n in range(N))
    s -= A_STAR/(Y_STAR - z)
    if fake is not None:
        qa = quartet_atoms(*fake)
        s += (wq/2)*mp.fsum(2*y/(y - z) for y in qa)   # mass 2y per atom, folded weight
    return s

def neg_squares(zs, N, fake=None, tol=mp.mpf(10)**(-18)):
    "kappa = #negative eigenvalues of the Hermitian Pick matrix at sample points zs."
    M=len(zs)
    P=[[ (m_sigma(zs[i],N,fake)-mp.conj(m_sigma(zs[j],N,fake)))/(zs[i]-mp.conj(zs[j]))
         for j in range(M)] for i in range(M)]
    # real embedding [[Re,-Im],[Im,Re]] (each P-eigenvalue appears twice)
    Re=[[mp.re(P[i][j]) for j in range(M)] for i in range(M)]
    Im=[[mp.im(P[i][j]) for j in range(M)] for i in range(M)]
    B=mp.zeros(2*M)
    for i in range(M):
        for j in range(M):
            B[i,j]=Re[i][j]; B[i+M,j+M]=Re[i][j]; B[i,j+M]=-Im[i][j]; B[i+M,j]=Im[i][j]
    ev=mp.eigsy(B, eigvals_only=True)
    neg=sum(1 for e in ev if e< -tol)
    return neg//2, min(ev)

def sample_points(M):
    "M points in C^+ spread across the support scale [y_*, ~y_1] with small imaginary parts."
    xs=[mp.mpf('-0.16')+ (mp.mpf('0.17'))*mp.mpf(i)/(M-1) for i in range(M)]  # -0.16 .. 0.01
    ts=[mp.mpf('0.002')+ (mp.mpf('0.03'))*mp.mpf(i%5)/4 for i in range(M)]    # 0.002..0.032
    return [mp.mpc(x,t) for x,t in zip(xs,ts)]

print("=== ZETA (RH): kappa vs (sample size M, zero-truncation N) — expect kappa=1 stable ===")
for M in (6,12,20,30):
    row=[]
    for N in (50,100,200,400):
        k,mn=neg_squares(sample_points(M),N)
        row.append(f"N{N}:k={k}")
    print(f" M={M:3d}  "+"  ".join(row))

print("\n=== off-line quartet (DH-like), N=400, M=20: kappa vs (beta, gamma0) ===")
print("   on-line beta=0.5 -> quartet at y=1/g0^2>0 (genuine-looking); off-line beta>0.5 -> complex atoms")
for beta in ('0.5','0.7','1.0'):
    row=[]
    for g0 in (10,20,50):
        k,mn=neg_squares(sample_points(20),400,fake=(beta,g0))
        row.append(f"g0={g0}:k={k}")
    print(f" beta={beta}  "+"  ".join(row))

print("\n=== sampling-resolution test: off-line beta=1.0,g0=20, push M (denser near 1/g0^2=0.0025) ===")
def sample_near(M, center, half):
    xs=[center-half+2*half*mp.mpf(i)/(M-1) for i in range(M)]
    ts=[mp.mpf('0.0005')+mp.mpf('0.004')*mp.mpf(i%4)/3 for i in range(M)]
    return [mp.mpc(x,t) for x,t in zip(xs,ts)]
for M in (8,16,28):
    k,mn=neg_squares(sample_near(M, mp.mpf('0.0025'), mp.mpf('0.0025')), 400, fake=('1.0',20))
    print(f" M={M:3d} near y=0.0025:  kappa={k}   min-eig={mp.nstr(mn,3)}")
print("\nDONE")
