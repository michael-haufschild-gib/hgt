"""Audit of claim row #32: kappa_-(finite carrier) = #off-line conjugate pairs, exactly.
Model (from formal/GaloisForLFunctions/CarrierCauchy.lean): k off-line poles t_i (Im>0), 2k nodes z_j;
a_i(j)=(t_i-z_j)^-1, e_i(j)=(conj t_i - z_j)^-1; carrier vectors w_i=e_i+a_i, u_i=e_i-a_i;
H = sum_i w_i w_i* - sum_i u_i u_i* = [W|U] diag(I_k,-I_k) [W|U]*.
Proof: [W|U] invertible (carrier linear independence) => Sylvester's law => kappa_-=k.
On-line pole (real t): u_i = e_i - a_i = 0 => no negative direction => kappa_- counts off-line pairs only.
NOTE: Cauchy matrices are ill-conditioned; k>=4 needs high precision (mpmath dps=60) or double precision
falsely reports a deficient inertia (the k=5 double-precision artifact)."""
import mpmath as mp
mp.mp.dps = 60
def carrier_km(t, z):
    k = len(t); n = len(z)
    a = [[1/(t[i]-z[j]) for j in range(n)] for i in range(k)]
    e = [[1/(mp.conj(t[i])-z[j]) for j in range(n)] for i in range(k)]
    w = [[e[i][j]+a[i][j] for j in range(n)] for i in range(k)]
    u = [[e[i][j]-a[i][j] for j in range(n)] for i in range(k)]
    H = mp.zeros(n, n)
    for i in range(k):
        for p in range(n):
            for q in range(n):
                H[p, q] += w[i][p]*mp.conj(w[i][q]) - u[i][p]*mp.conj(u[i][q])
    for p in range(n):
        for q in range(n):
            H[p, q] = (H[p, q] + mp.conj(H[q, p]))/2
    ev = mp.eig(H, left=False, right=False)
    km = sum(1 for x in ev if mp.re(x) < -mp.mpf('1e-40'))
    return km
for k in [1, 2, 3, 4, 5, 6]:
    t = [mp.mpf(j)/3 - 1 + (mp.mpf('0.5')+mp.mpf(j)/5)*1j for j in range(k)]
    z = [mp.mpf(j)+mp.mpf('0.3') for j in range(2*k)]
    km = carrier_km(t, z)
    print(f"k={k}: kappa_-={km} (expect {k}) {'OK' if km==k else 'FAIL'}")
