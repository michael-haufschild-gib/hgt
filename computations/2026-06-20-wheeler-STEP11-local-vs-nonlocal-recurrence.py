"""
STEP 11 — WILD metaphor experiment (no predictable outcome).
Node metaphor: long-range (NON-LOCAL) vs short-range (LOCAL) coupling. Weld: d_s local
(differential) vs sigma_p non-local (multiplicative). HT germ has NO local recurrence
(consecutive indices). WILD question: does it satisfy a NON-LOCAL / MULTIPLICATIVE recurrence
(DILATED indices c_k, c_{2k}, c_{3k})? i.e. local-transcendental but non-local-algebraic?
Compare sigma_min of LOCAL {c_k,c_{k+1},c_{k+2}} vs MULTIPLICATIVE {c_k,c_{2k},c_{3k}}.
mpmath-native, dps=40. Outcome unknown.
"""
import mpmath as mp
mp.mp.dps=40

def sigma_local(c, kmax, d=1):
    rows=[]
    for k in range(1,kmax):
        rows.append([(mp.mpf(k)**e)*c(k+i) for i in (0,1,2) for e in range(d+1)])
    return _smin(rows)
def sigma_mult(c, kmax, d=1):
    rows=[]
    for k in range(1,kmax):
        rows.append([(mp.mpf(k)**e)*c(m*k) for m in (1,2,3) for e in range(d+1)])
    return _smin(rows)
def _smin(rows):
    A=mp.matrix(rows)
    for j in range(A.cols):
        nrm=mp.sqrt(sum(A[i,j]**2 for i in range(A.rows)))
        if nrm!=0:
            for i in range(A.rows): A[i,j]=A[i,j]/nrm
    return mp.sqrt(abs(mp.eigsy(A.T*A, eigvals_only=True)[0]))

kmax=12   # multiplicative needs indices up to 3*kmax
germs={
 "DA exp 1/k!":          lambda k: mp.mpf(1)/mp.factorial(k),
 "DA geom 2^-k":         lambda k: mp.mpf(2)**(-k),
 "HT zeta(k)":           lambda k: mp.zeta(k+1),      # shift to keep k>=1 -> zeta(k+1)
 "HT logGamma z(k)/k":   lambda k: mp.zeta(k+1)/(k+1),
 "HT Stieltjes gamma_k": lambda k: mp.stieltjes(k),
}
print("="*78)
print(" STEP11 WILD: LOCAL (consecutive) vs MULTIPLICATIVE (dilated c_k,c_2k,c_3k) recurrence")
print("="*78)
print(f"\n {'germ':24s}  sigma_LOCAL   sigma_MULT    mult<<local? (non-local-algebraic?)")
for n,c in germs.items():
    sl=sigma_local(c,kmax); sm=sigma_mult(c,kmax)
    flag = "YES (mult relation!)" if sm < sl*mp.mpf('1e-3') and sm<mp.mpf('1e-10') else "no"
    print(f" {n:24s} {mp.nstr(sl,3):12s} {mp.nstr(sm,3):12s}  {flag}")
print("\n wild-read: if any HT germ has sigma_MULT << sigma_LOCAL (and ~0), it is")
print(" local-transcendental but NON-LOCAL(multiplicative)-algebraic = a genuine weld signature.")
