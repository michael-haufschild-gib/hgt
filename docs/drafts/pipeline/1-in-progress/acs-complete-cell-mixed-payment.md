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

The coarse pair is `C_a = cellAtom (2*a) + cellAtom (2*a+1)`. For coefficients `u,v` on its two complete cells, the candidate exact splitting is

`u cellAtom(2*a) + v cellAtom(2*a+1) = (haarRightCoeff a*u + haarLeftCoeff a*v) C_a + (u-v) haarAtom a`.

The average block is the actual cell system translated by `log 2`. Integer right shifts preserve this block. The expected triangular prime law is that every translated coarse pair is orthogonal to every balanced detail. Prove these actual-vector identities in Lean, retaining the opposite mixed orientation. Then derive and audit a genuine bound for the remaining original Gamma–prime–pole coupling; no assumed positive Schur residual or unchanged-sign claim is permitted.

## Status

`HaarCellCoarseSplitting.lean` contains the actual pair splitting, exact `log 2` shift identity, endpoint-jump formula, and vanishing of the entire average-to-detail prime block for every integer multiplier. Four declarations passed their transitive axiom checks; the shift identity's numeral-coercion fix still needs its exact final audit. The opposite mixed orientation is retained. No mixed Weil sign has been proved. No stage-2 parking.

## Full-source Gamma conjecture

For a finite family of disjoint intervals `I_i=(a_i,b_i)` of widths `w_i≤1`, define `mean_i=(∫ I_i f)/w_i` and `V_i=∫ I_i (f-mean_i)²`. The next analytic target removes all local mean-zero restrictions:

`Σ_i log(1/w_i)*V_i ≤ levyEnergy f`

for every compact BV source. This would pay the balanced differences inside arbitrary complete-cell data even when pair averages are nonzero. The candidate mechanism is weighted variance on each exponential Gamma slice: its weighted variance is at least the minimum weight times the unweighted variance. Summing both interval charges should then preserve the existing coefficient one. This strengthening is conjectural and requires its own Lean proof; it does not retain the coarse Gamma energy as an additional free term.

[Gamma payment with arbitrary means](../3-formalized/acs-gamma-payment-with-arbitrary-means.md) records six clean exact-file/transitive audits: actual interval variance, weighted moment-matrix payment, the exponential estimate, full two-interval Gamma coupling, and exterior-point variance charge. `GammaVarianceCapacity.lean` contains the finite-family extension; logarithmic coercivity remains prepared in `/tmp/acs-gamma-variance-coercivity.lean`. Those last extensions are not yet checked and are not counted as proofs.

The concrete source specialization is prepared in `/tmp/acs-complete-cell-variance.lean`. It retains independent average and detail coefficients on every pair and identifies them with arbitrary original cell coefficients. Its target is `Σ log(a)*haarMass(a)*(u(a)-v(a))² ≤ levyEnergy(Σ u(a)*rawCell(2a)+v(a)*rawCell(2a+1))`. Every dependency and this exact source theorem still need their final checks.

## Next remainder conjecture

The same positive-kernel splitting may retain an explicit coarse remainder as well as both variance charges. For product weights `w≥m≥0`, `v≥n≥0`, the proposed additional term is `m*n*|I|*|J|*(mean_I(f)-mean_J(g))²`. The four nonnegative product pieces from `w=m+(w-m)` and `v=n+(v-n)` suggest a proof. Its Gamma counterpart would preserve the far-end kernel coupling of actual pair averages while paying detail variances. `/tmp/acs-variance-remainder.lean` contains the exact variance identity and a Lean candidate for this strengthened product-kernel bound. It has not been checked; no mathematical input from it is yet used.

## Log

- 2026-10-28 — Opened after the full balanced-cell floor and smooth effectivity passed exact Lean audits.
