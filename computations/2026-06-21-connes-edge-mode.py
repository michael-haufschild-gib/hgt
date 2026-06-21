"""
CONSTRUCT the edge mode and test the universality conjecture (plumbing seal x coral growing-edge x invariant).
v_d = eigenvector of the SMALLEST generalized eigenvalue of (Q_0, M_triv) (the unique mode an off-line zero
flips). As a polynomial p_d(y), rescale to the hard edge: xi = y / y_d, y_d = gamma_d^{-2} (deepest used zero).
Conjecture: the rescaled profiles p_d(xi*y_d), normalized, OVERLAY across d -> a universal edge mode Phi(xi).
Report p_d on a common xi-grid for d=6,8,10,12 to eyeball convergence + a cross-d L2 distance.
args: N dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
mp.mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 130
DS=[6,8,10,12]; KMAX=2*max(DS)+1; q1=mp.mpf(1)/4
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
T={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def maMM(m): return (-1)**m*mp.mpf(2)**(-2*(m+1))*(mp.zeta(2*(m+1),q1)-mp.mpf(4)**(2*(m+1)))
def edge_coeffs(d):
    H0=mp.matrix(d+1,d+1); MA=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H0[i,j]=T[i+j+1]; MA[i,j]=maMM(i+j)
    L=mp.cholesky(MA); Li=mp.inverse(L); G=Li*H0*Li.T; G=(G+G.T)/2
    E,V=mp.eigsy(G); x=[V[i,0] for i in range(d+1)]      # smallest-eigenvalue eigvec in mu_triv-ON basis
    v=[mp.fsum(Li.T[i,j]*x[j] for j in range(d+1)) for i in range(d+1)]   # back to coeff space
    return v
xis=[mp.mpf(t)/10 for t in range(2,31,2)]     # xi grid 0.2..3.0
prof={}
print(f"# edge mode universality, N={N}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
for d in DS:
    v=edge_coeffs(d); yd=gam[d-1]**(-2)
    # p_d at y = xi*yd
    vals=[mp.fsum(v[i]*(xi*yd)**i for i in range(d+1)) for xi in xis]
    nrm=mp.sqrt(mp.fsum(z*z for z in vals));
    s=1 if vals[len(vals)//2]>=0 else -1                  # fix sign by mid value
    vals=[s*z/nrm for z in vals]
    prof[d]=vals
    print(f"d={d:2d} (y_d={mp.nstr(yd,3)}): "+" ".join(f"{mp.nstr(z,3):>7s}" for z in vals))
# cross-d L2 distances of the rescaled profiles (should -> 0 if universal)
print(f"# xi grid: "+" ".join(mp.nstr(x,2) for x in xis))
for a,b in [(6,8),(8,10),(10,12)]:
    dist=mp.sqrt(mp.fsum((prof[a][i]-prof[b][i])**2 for i in range(len(xis))))
    print(f"# L2 distance rescaled profile d={a} vs d={b}: {mp.nstr(dist,5)}")
