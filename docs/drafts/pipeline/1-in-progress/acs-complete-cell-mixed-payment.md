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

## Checked mean and exterior remainder

[Simultaneous Gamma payment](../3-formalized/acs-gamma-detail-mean-boundary-payment.md) passed exact project checks and ten clean transitive axiom audits. `IntervalVarianceRemainder.lean` proves the product-weight splitting; `GammaVarianceRemainder.lean` proves its full Gamma-series and exterior-point consequences. `GammaMeanVarianceCapacity.lean` proves the coherent finite-family bound and the real inequality

`Σ_i log(1/w_i) V_i(f) + (1/2) Σ_ij w_i*w_j*k(max(b_j-a_i,b_i-a_j))*(mean_i(f)-mean_j(f))² + Σ_i ∫_F w_i*(mean_i(f)-f(y))²*gammaFarCharge_i(y) ≤ levyEnergy f`.

The exterior sum is proved finite before conversion to real numbers. All three terms coexist in the original energy; no local mean-zero or exterior-vanishing premise appears. The explicit mean graph is not identified with the entire coarse Gamma energy.

`CompleteCellMeanGraph.lean` passed its exact project check and both transitive axiom audits. It retains arbitrary original cell coefficients, logarithmic detail payment, the full mean graph, and an explicit exterior charge depending only on the actual pair averages. Its source is proved zero almost everywhere outside the interval family.

## Checked coarse Gamma recovery

[Coarse Gamma recovery](../3-formalized/acs-coarse-gamma-recovery.md) passed all three exact project checks and thirteen standard-axiom audits. Uniform integrated row bounds, their actual-pair transfer, and exterior finiteness give

`Γ(averageSectionProfile q X) + Σ_(a=1..X) log(a)*haarMass(a)*d(a)² ≤ Γ(completePairProfile q d X) + C*∫(averageSectionProfile q X)²`

for every signed `q,d` and every horizon, with the explicit nonnegative constant `C=2*(13*exp(1/2)+2*gammaTailMass(log(3/2)))`. The integral equals the actual coefficient mass `Σ logCellWidth(a)*q(a)²`. The original independent cell coefficients `u,v` are retained in a separate exact specialization. This closes coarse Gamma recovery without using the detail reserve twice. Full signed prime and pole coupling remains unpaid.

## Log

- 2026-10-28 — Opened after the full balanced-cell floor and smooth effectivity passed exact Lean audits.
