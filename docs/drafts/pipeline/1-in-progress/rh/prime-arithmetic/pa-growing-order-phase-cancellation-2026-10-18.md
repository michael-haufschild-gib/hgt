# PA growing-order positivity through phase cancellation

- **ID:** PA-GROWING-ORDER-20261018
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `RHTower/PrimeArchHausdorffFixedOrderLargeShiftPositivity.lean`; PA frontier row.
- **Statement under attack:** A uniform quadratic (or comparably stronger than cubic) shift region makes the actual calibrated prime–archimedean Hausdorff differences nonnegative.

## Goal

Rotate from JAS to PA. Produce actual positivity while both Hausdorff order and shift grow. Strengthen BiScaleUncertainty with a quantitative phase-cancellation mechanism usable on the arithmetic source. RH remains open; positivity outside the proven region is not assumed.

## Evidence and scope

Existing fixed-order proof uses `K = 10(k+1)+20`, `T = sqrt(r/(KR))`, and `T >= 42(k+1)+44K`. Its displayed construction already gives a uniform cubic threshold after one source-dependent constant is chosen. Merely exposing that quantifier bound would not remove a hard obstacle.

For `x^(k+1)(R-x)^r`, the first-order phase derivative vanishes at `x = R(k+1)/(r+k+1)`. Test whether retaining this cancellation reduces the phase budget in the dominant band enough to obtain a quadratic region. Counting and negative-tail domination must be proved jointly; local atom positivity alone does not close the conjecture.

## Plan

1. Inspect current Lean source and corpus search hits; attack the claimed uniform region and isolate exact analytic dependencies.
2. Write a dependency-closed paper proof or a precise obstruction with its strongest positive survivor.
3. Formalize the exact proved statement, connect to the actual PA source, wire leaves, and run canonical leaf and axiom audits.

## Gates

- [x] Source located; existing bound and its limitation checked.
- [ ] Conjecture attack complete.
- [ ] Dependency-closed paper proof complete.
- [ ] Lean theorem and actual source specialization audited.

## Dependency-closed paper component: populated quadratic saddle bands

The full-array quadratic conjecture remains open. The following component is proved on paper and is the exact next formalization target; it does not assert positivity of the complementary spectrum.

**Signed phase law.** For real `tau, sigma` and natural `n,r`, put
`B = |n*tau-r*sigma| + (n*|tau|^3+r*|sigma|^3)/3`.
Then the real part of `(1+i*tau)^n*(1-i*sigma)^r` is at least
`(1-B^2/2)` times its modulus. Indeed its unreduced phase is
`theta=n*atan(tau)-r*atan(sigma)`; the corpus theorem
`abs_arctan_sub_self_le_cube` gives `|theta| <= B`. Polar factorization and
`cos(theta) >= 1-theta^2/2` finish. No smallness of either accumulated absolute phase is required. In particular `B <= 1` retains half the modulus.

**Actual Xi atom geometry.** Write `u=|Im rho|`, `v=1/2-Re rho`, and
`lambda=(u^2-v^2)/(u^2+v^2)^2`. Existing unconditional geometry gives
`u^2 >= 41/2`, `v^2 < 1/4`, `|Im x|/lambda <= 2/u`.
Moreover `1/(u^2+1) <= lambda <= 1/u^2`. For the new lower bound, after clearing positive denominators the difference is
`u^2*(1-3v^2)-v^2-v^4 >= u^2/4-5/16 > 0`.
Thus, for `a=lambda/(1-lambda)`,
`1/u^2 <= a <= 1/(u^2-1)`.

**Quadratic band.** Let `H>=1`, `T>=max(4,H)`, `n>=1`, and `r=n*T^2`.
For any actual copy with `T <= u <= T+H`, the preceding slope bounds give
`a<=1`, `r*a<=2n`, and `|n-r*a| <= 4nH/T`.
For the lower side use
`n-r*a <= n*(u^2-T^2)/u^2 <= 3nH/T`.
For the upper side use
`r*a-n <= n/(T^2-1) <= nH/T`.
Set `tau=Im(x)/lambda`, `sigma=a*tau`. Then
`|n*tau-r*sigma| <= 8nH/T^2`, while
`(n*|tau|^3+r*|sigma|^3)/3 <= 8n/T^3`.
If `32nH <= T^2`, these bounds sum to at most `1/4+1/16<1`.
The positive real scale `lambda^n*(1-lambda)^r` therefore gives
`Re[x^n*(1-x)^r] >= |x^n*(1-x)^r|/2 > 0` on the entire band.
This replaces the previous local requirement `T` proportional to `n` with `T^2` proportional to `nH`.

**Population, without RH.** Use the corpus logarithmic Riemann--von Mangoldt remainder `|N(t)-M(t)| <= C log t`. For fixed `H>=1` and sufficiently large `t>=H`, convexity gives
`M(t+H)-M(t) >= H/(4*pi)*log t`, and the two errors sum to at most `3C log t`.
Choose `H=16*pi*(C+1)`. Then `N(t+H)-N(t)>=log t>0` eventually. Hence the symmetric copy band is nonempty; no simplicity or RH assumption is used.

Choose one natural constant `A` large enough to dominate `32H`, `H^2`, `16`, and the square of that counting threshold. For every `k` and every `r>=A*(k+1)^2`, set `n=k+1` and `T=sqrt(r/n)`. All band hypotheses hold. The actual radius-one Hausdorff atom sum on `(T,T+H]` is strictly positive and retains at least half of its total absolute mass. This is a uniform unconditional source subpacket producer. The full Hausdorff sum still requires control of the complementary negative contribution.

**Attack audit.** An arbitrary off-line divisor can retain this positive band, so this component cannot imply RH alone. The cubic Taylor remainder is kept; replacing `atan(t)` by `t` exactly would be invalid. The radius is explicitly `1`, not silently the endpoint radius. Population uses the logarithmic remainder, not the weaker fixed-relative-error count. Strict positivity uses nonempty bands and nonzero actual atoms, not a vacuous finite sum.

**Exact source remainder.** Absolute convergence gives
`D_1(k,r) = sum_band Re(atom) + sum_complement Re(atom)`.
Consequently any negative actual prime--archimedean difference in the quadratic region forces the complementary sum to be strictly less than minus half the band's total absolute mass. This identifies a quantitative residual outside the proved positive band. It does not control that residual's size from the arithmetic side.

## Log

- 2026-10-18 — Opened during route rotation. Previous own cycle: RW, TH, MSC, RB, SZ, BVI, HCF audit, JAS. No new PA theorem claimed yet.
- Initial deep search completed without partial stages; coverage snapshot one generation old, semantic coverage unavailable, compiler applicability unchecked. Source arguments include the existing band-dominance proof and cofinal Hausdorff criteria. No proof ideas returned. Follow-up search targets saddle cancellation.
- Follow-up deep search also completed; semantic ranking was mostly unrelated. Targeted source search located the existing cubic arctangent estimate, the exact reciprocal-square atom formulas, and the unconditional logarithmic zero-count remainder. The short-window Littlewood theorem was rejected as a dependency because it assumes RH.
- Completed local component: [populated positive quadratic saddle bands](../../../3-formalized/pa-quadratic-saddle-bands-2026-10-18.md). All three canonical leaves, all 19 public axiom audits, API probes, source hashes, and repository lint pass. The full-array conjecture remains open; no positive bound for the complementary signed sum has been proved. Continue route rotation before revisiting this conjecture.
