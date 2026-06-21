"""
ATTACK the bridge via the Hankel = Vandermonde-discriminant identity (a genuine positive structure).
ny' := y-weighted zero measure  nu' = sum_rho 2 y_rho delta_{y_rho}.  Shifted Hankel H_d=[T_{i+j+1}]
= [int y^{i+j} dnu'], and the Gram/Andreief identity gives
   det H_d = (1/(d+1)!) sum_{rho_0..rho_d} prod_k(2 y_{rho_k}) prod_{i<j}(y_{rho_i}-y_{rho_j})^2.
Each TERM is >=0 iff the participating y's are real-positive (RH). Off-line conjugate pairs {y,ybar}
inject the only negativity: self-term y*ybar*(y-ybar)^2 = -4|y|^2(Im y)^2 < 0.

This script:
 (1) verifies the discriminant identity for d=1,2 against det of the cached-zero Hankel;
 (2) BULK-DOMINATION: takes a hypothetical off-line pair at height gamma0 (real part beta), computes its
     negative self-term vs its POSITIVE cross-terms with the on-line bulk, to show the bulk overwhelms it
     unless gamma0 is comparable to gamma_1 -- i.e. det H_1>0 is robust/unconditional for high off-line zeros.
args: N gamma0 beta dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 120
g0=mp.mpf(sys.argv[2]) if len(sys.argv)>2 else mp.mpf(50)
beta=mp.mpf(sys.argv[3]) if len(sys.argv)>3 else mp.mpf('0.25')
mp.mp.dps=int(sys.argv[4]) if len(sys.argv)>4 else 50
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
y=[1/g**2 for g in gam]           # on-line reciprocal-seam points (real, >0)
w=[mp.mpf(2) for _ in gam]        # folded weight 2 per zero
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
def Tk(k): return mp.fsum(wi*yi**k for wi,yi in zip(w,y))+tail(k)
# (1) discriminant identity, d=1 and d=2
H1=mp.matrix(2,2)
for i in range(2):
    for j in range(2): H1[i,j]=Tk(i+j+1)
det1=H1[0,0]*H1[1,1]-H1[0,1]**2
# discriminant double sum (truncated to N, same truncation as Hankel -> compare modulo tail)
disc1=mp.fsum(w[a]*w[b]*y[a]*y[b]*(y[a]-y[b])**2 for a in range(N) for b in range(N))/2
print(f"# discriminant attack, N={N}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"## (1) identity check")
print(f"det H_1 (from Hankel, no tail) = {mp.nstr(mp.fsum(w[a]*y[a] for a in range(N))*mp.fsum(w[a]*y[a]**3 for a in range(N))-mp.fsum(w[a]*y[a]**2 for a in range(N))**2,8)}")
print(f"discriminant 1/2 sum_ab ...     = {mp.nstr(disc1,8)}   (should match)")
# d=2 (truncated, no tail; compare det vs discriminant triple sum)
m=[mp.fsum(w[a]*y[a]**k for a in range(N)) for k in range(0,6)]   # raw moments of nu' : m_k=int y^k dnu'
H2=mp.matrix(3,3)
for i in range(3):
    for j in range(3): H2[i,j]=m[i+j+1]
det2=mp.det(H2)
# triple discriminant (Vandermonde) -- O(N^3), keep N modest
idx=range(N)
disc2=mp.mpf(0)
ys=y[:N]; ws=w[:N]
disc2=mp.fsum(ws[a]*ws[b]*ws[c]*ys[a]*ys[b]*ys[c]*((ys[a]-ys[b])*(ys[b]-ys[c])*(ys[a]-ys[c]))**2 for a in idx for b in idx for c in idx)/6
print(f"det H_2 (truncated)            = {mp.nstr(det2,8)}")
print(f"discriminant 1/6 sum_abc ...    = {mp.nstr(disc2,8)}   (should match)")
# (2) bulk domination for a hypothetical off-line pair at (beta, gamma0)
wo=mp.mpc(beta,g0); yo=-1/wo**2; yb=mp.conj(yo)        # off-line reciprocal points (complex conj pair)
self_term=2*mp.re(yo*yb*(yo-yb)**2)                    # weight 2 each; the negative self-term
cross=mp.fsum(2*w[a]*mp.re(yo*y[a]*(yo-y[a])**2 + yb*y[a]*(yb-y[a])**2) for a in range(N))  # cross with bulk
print(f"## (2) bulk domination, off-line pair beta={mp.nstr(beta,3)} gamma0={mp.nstr(g0,5)} (|y_off|={mp.nstr(abs(yo),4)})")
print(f"negative self-term (the only negativity)   = {mp.nstr(self_term,6)}")
print(f"positive cross-terms with on-line bulk     = {mp.nstr(cross,6)}")
print(f"net off-line contribution to det H_1       = {mp.nstr(self_term+cross,6)}  ({'POSITIVE: bulk dominates' if self_term+cross>0 else 'NEGATIVE'})")
print(f"ratio |self|/cross                          = {mp.nstr(abs(self_term)/abs(cross),5)}")
