# Mixed payment between pair averages and balanced cells

- **ID:** acs-complete-cell-mixed-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [complete-cell index payment](acs-complete-cell-index-payment.md)
- **Statement:** Control the original mixed Weil interaction between complete pair averages and the now-positive balanced detail directions, with a signed payment that remains valid under complete-cell refinement.

## Known input and missing step

[Balanced whole-cell effectivity](../3-formalized/acs-complete-cell-haar-effectivity.md) gives a growing logarithmic floor on every signed high-index balanced detail and exact smooth source effectivity. Arbitrary complete-cell data also have independent pair averages. Positivity of the detail block does not bound its mixed coupling or the residual after its elimination.

## Concrete source calculation underway

The coarse pair is `C_a = cellAtom (2*a) + cellAtom (2*a+1)`. For coefficients `u,v` on its two complete cells, the checked exact splitting is

`u cellAtom(2*a) + v cellAtom(2*a+1) = (haarRightCoeff a*u + haarLeftCoeff a*v) C_a + (u-v) haarAtom a`.

The average block is the actual cell system translated by `log 2`. Every integer-translated coarse pair has zero real inner product with every balanced detail. The opposite mixed orientation remains. The open task is a genuine bound for the remaining original Gamma–prime–pole coupling; no assumed positive Schur residual or unchanged-sign claim is permitted.

## Status

[Complete-cell prime triangularity](../3-formalized/acs-complete-cell-prime-triangularity.md) passed its exact final Lean check, with five clean transitive axiom audits: actual pair splitting, exact `log 2` shift identity, endpoint-jump formula, and vanishing of the entire average-to-detail prime block for every integer multiplier. The opposite mixed orientation is retained. No mixed Weil sign has been proved. No stage-2 parking.

## Checked full-source Gamma variance bound

For a finite family of disjoint nonempty intervals `I_i=(a_i,b_i)` of widths `w_i≤1`, define `mean_i=(∫ I_i f)/w_i` and `V_i=∫ I_i (f-mean_i)²`. Lean now proves:

`Σ_i log(1/w_i)*V_i ≤ levyEnergy f`

for every compact BV source, without local mean-zero restrictions. This pays local oscillation even with nonzero pair averages. Weighted variance on each exponential Gamma slice pays its minimum weight times the unweighted variance; coherent interval charges preserve coefficient one. The theorem does not retain the entire coarse Gamma energy as an additional free term.

[Gamma payment with arbitrary means](../3-formalized/acs-gamma-payment-with-arbitrary-means.md) records twelve clean exact-file/transitive audits through the full logarithmic inequality `levyEnergy_ge_sum_log_variance` and its exact complete-cell specialization.

`CompleteCellVariancePayment.lean` passed its exact final audit, including four clean transitive axiom prints. It retains independent average and detail coefficients on every pair and identifies them with arbitrary original cell coefficients. `cellPairSum_levyEnergy_ge` proves `Σ log(a)*haarMass(a)*(u(a)-v(a))² ≤ levyEnergy(Σ u(a)*rawCell(2a)+v(a)*rawCell(2a+1))` for arbitrary signed `u,v` and every finite horizon. No pair average is suppressed.

## Next remainder conjecture

For product weights `w≥m≥0`, `v≥n≥0`, the four nonnegative product pieces from `w=m+(w-m)` and `v=n+(v-n)` retain the additional term `m*n*|I|*|J|*(mean_I(f)-mean_J(g))²` alongside both variance charges. `IntervalVarianceRemainder.lean` passed its exact final audit with three clean axiom prints: exact variance identity, strengthened product-kernel inequality, and exponential consequence. `GammaVarianceRemainder.lean` passed its exact final check and both transitive axiom audits. It proves the full Gamma-series extension and exterior-point mean-displacement term.

`/tmp/acs-gamma-mean-variance-capacity.lean` prepares the coherent strengthening

`Σ_i log(1/w_i) V_i(f) + (1/2) Σ_ij w_i*w_j*k(max(b_j-a_i,b_i-a_j))*(mean_i(f)-mean_j(f))² ≤ levyEnergy f`.

The extra term is an explicit graph on the actual interval means, not the entire coarse Gamma energy. The extended-integral theorem also retains `2 Σ_i ∫_F w_i*(mean_i(f)-f(y))²*gammaFarCharge_i(y)`, where `F` is the family complement; the displayed real graph inequality is its weaker corollary. The candidate combines the three-term pair estimate with the full exterior mean-displacement charge. The Gamma-series extension passed; the finite-family extension remains unchecked. The complete-cell specialization is prepared in `/tmp/acs-complete-cell-mean-graph.lean`, retaining arbitrary original coefficients and the mean graph alongside logarithmic detail payment.

## Log

- 2026-10-28 — Opened after the full balanced-cell floor and smooth effectivity passed exact Lean audits.

The pending finite-family candidate now also retains the exterior term in its real inequality, using the exact finite extended integral. Its finiteness is derived from the original compact-BV Gamma energy; no new integrability assumption is added. Candidate declaration: `levyEnergy_ge_log_variance_add_mean_graph_add_exterior`.

The concrete candidate now keeps an explicit boundary charge depending only on the pair averages. The complete-cell source vanishes almost everywhere on the family complement, so this charge is the actual far-end kernel integral of width times average squared. Both the finite-family real exterior estimate and concrete specialization remain unverified.
