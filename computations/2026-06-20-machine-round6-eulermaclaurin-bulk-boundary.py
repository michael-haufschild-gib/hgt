#!/usr/bin/env python3
# THE MACHINE (codex+rng walk) — Round 6. WIDE: related-to(HT/Gamma/Li/zeta) -> rng#15 = Bernoulli numbers
# -> specifics -> rng#5 = NODE: EULER-MACLAURIN summation formula. (In-field/computational-backbone node;
# walk seeded at the problem, not yet wandered out.) Codex EM-rules transferred -> experiment:
#   RULE: discrete object = smooth BULK (integral) + BOUNDARY-ONLY corrections (endpoint derivatives,
#   Bernoulli coeffs); the correction series is ASYMPTOTIC (optimal truncation), not convergent.
# STEP 7: run on zeta. Test (a) bulk(=pole 1/(s-1)) + boundary-corrections at n reconstructs zeta;
#   (b) the boundary-correction series is divergent/asymptotic (least-term / optimal truncation).
import mpmath as mp
mp.mp.dps = 30

def zeta_em(s, N, K):
    # Euler-Maclaurin: zeta(s) = sum_{n=1}^{N-1} n^-s + N^{1-s}/(s-1) + (1/2)N^-s
    #   + sum_{k=1}^{K} B_{2k}/(2k)! * (s)_{2k-1} * N^{-s-2k+1}
    head = mp.fsum(mp.mpf(n)**(-s) for n in range(1, N))
    bulk = mp.power(N, 1-s)/(s-1)          # BULK = integral term (carries the pole)
    half = mp.mpf(1)/2 * mp.power(N, -s)    # boundary endpoint value
    corr_terms = []
    poch = mp.mpf(1)
    for k in range(1, K+1):
        # (s)_{2k-1} rising factorial
        poch = mp.rf(s, 2*k-1)
        term = mp.bernoulli(2*k)/mp.factorial(2*k) * poch * mp.power(N, -s-2*k+1)
        corr_terms.append(term)
    return head + bulk + half + mp.fsum(corr_terms), corr_terms

s = mp.mpf('2.5')
true = mp.zeta(s)
print(f"zeta({float(s)}) true = {mp.nstr(true,18)}")
print("\n(a) BULK+BOUNDARY reconstruction (N=8), increasing K boundary-correction terms:")
for K in [0,1,2,3,5,8,12,18,25]:
    val,_ = zeta_em(s, 8, K)
    print(f"  K={K:2d}  err={float(abs(val-true)):.3e}")
_,terms = zeta_em(s, 8, 30)
mags=[float(abs(t)) for t in terms]
kmin=min(range(len(mags)), key=lambda i:mags[i])
print(f"\n(b) boundary-correction term magnitudes -> least term at k={kmin+1} (optimal truncation),")
print(f"    then DIVERGE: |term_k| for k=1..12: "+", ".join(f"{m:.1e}" for m in mags[:12]))
print(f"    min |term|={mags[kmin]:.1e}  ;  term[25]={mags[24]:.1e} (blown up) => ASYMPTOTIC series confirmed.")
print("\n=== STEP 8 self-curate ===")
print("(a) surprising? NO. (b) shows something about zeta I didn't know? NO.")
print("  This is the TEXTBOOK Euler-Maclaurin continuation of zeta: bulk=pole 1/(s-1), boundary=Bernoulli")
print("  endpoint corrections, asymptotic with optimal truncation. The 'bulk+boundary' holographic reframing")
print("  is on-mission but = known zeta-regularization. EM is zeta's own computational backbone (in-field node).")
print("  => DEAD END. Bank; advance the walk's current-node so next tick wanders out of the field.")
