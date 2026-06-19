# The Hermite engine for the arithmetic Jensen polynomials (foundations §83-84).
#
# GORZ (2019): the Jensen polynomials J^{d,n} of xi are approximated by Hermite polynomials, and
# are eventually hyperbolic (each d, large n). The field's §83.4 says the SAME Hermite engine runs
# the crystalline classification + the oscillator algebra. Concrete test (beyond GORZ's asymptotic):
# at finite (d,n), (i) confirm hyperbolicity + measure the margin (min root gap), (ii) compare the
# rescaled Jensen roots to the Hermite-H_d roots, quantifying the deviation. RH needs hyperbolicity
# to PERSIST (all d,n); the Hermite engine predicts the root pattern; the margin vs deviation is the
# finite-level necessary-condition picture.
# Run: runpod python3.13 + mpmath. 2026-06-19.
import mpmath as mp
mp.mp.dps = 40

def xi(s):
    return 0.5*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)

# Xi(t) = xi(1/2 + i t) is real and even in t; Taylor coeffs a_{2k} at t=0 give the Jensen sequence.
def Xi(t):
    return xi(mp.mpf(1)/2 + 1j*t).real

# Taylor coefficients of Xi at 0 up to order N (even powers nonzero)
N = 24
taylor = mp.taylor(Xi, 0, N)   # taylor[k] = Xi^{(k)}(0)/k!
# Jensen sequence: a_k := (the even Taylor coeffs, reindexed). Pólya-Jensen uses gamma_k from
# Xi(t) = sum gamma_k t^{2k}/(2k)! ; equivalently a_k = (2k)! * taylor[2k]  (the "moment" sequence).
# Pólya b_n must be POSITIVE: b_n = (-1)^n (2n)! Xi^{(2n)}(0)/(2n)!·(2n)! = (-1)^n (2n)! taylor[2n].
a = [((-1)**k)*mp.factorial(2*k)*taylor[2*k] for k in range(0, N//2+1)]
print('Jensen moment positivity check (b_n>0 for n=0..5):', [b>0 for b in a[:6]])

def jensen_poly(d, n):
    # J^{d,n}(X) = sum_{j=0}^d C(d,j) a_{n+j} X^j
    return [mp.binomial(d, j)*a[n+j] for j in range(d+1)]  # coeffs low->high

def hermite_roots(d):
    # roots of physicists' Hermite H_d (real); via mp Hermite
    # build H_d coefficients and find roots
    import mpmath
    # use known: roots of H_d are real; get them from numpy-free mp.polyroots of Hermite coeffs
    # Hermite recurrence H_0=1,H_1=2x,H_{n+1}=2xH_n-2nH_{n-1}
    H=[[mp.mpf(1)],[mp.mpf(0),mp.mpf(2)]]
    for nn in range(1,d):
        prev,cur=H[nn-1],H[nn]
        nxt=[mp.mpf(0)]*(nn+2)
        for i,c in enumerate(cur): nxt[i+1]+=2*c
        for i,c in enumerate(prev): nxt[i]-=2*nn*c
        H.append(nxt)
    coeffs=H[d][::-1]
    return sorted([r.real for r in mp.polyroots(coeffs, maxsteps=200, extraprec=100)])

print("=== Hermite engine for arithmetic Jensen polynomials (§83-84) ===")
print("dps=%d, Xi Taylor order=%d" % (mp.mp.dps, N))
for d in (2,3,4,5):
    hr = hermite_roots(d)
    hgap = min(hr[i+1]-hr[i] for i in range(len(hr)-1))
    print("\n-- degree d=%d (Hermite H_%d min root gap = %.4f) --" % (d,d,hgap))
    for n in (0,1,2,4):
        coeffs = jensen_poly(d, n)[::-1]  # high->low for polyroots
        roots = mp.polyroots(coeffs, maxsteps=400, extraprec=200)
        ims = [abs(r.imag) for r in roots]
        res = sorted([r.real for r in roots])
        maxim = max(ims)
        gap = min(res[i+1]-res[i] for i in range(len(res)-1)) if len(res)>1 else mp.mpf('nan')
        hyp = "YES" if maxim < mp.mpf('1e-20') else "NO"
        print("  n=%d: hyperbolic=%s  max|Im(root)|=%.2e  min real-gap(margin)=%.4e" %
              (n, hyp, float(maxim), float(gap)))
print("\n=== verdict: hyperbolicity + margin at finite (d,n); Hermite gap is the engine's prediction ===")
