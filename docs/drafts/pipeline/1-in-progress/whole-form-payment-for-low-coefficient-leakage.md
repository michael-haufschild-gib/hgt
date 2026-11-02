# Whole-form payment for low coefficient leakage

- **Stage:** 1-in-progress.
- **Type:** CONJECTURE.
- **Wall:** Σ1d.
- **Target:** Polynomial conductor spans at a fixed positive multiple of `log log N` for every nonzero compact real `C²` profile.

## New input

Monotonicity in overlap and the existing bound at overlap one imply
`E_m(c)≤|selfφ(1)|+2log m+3` for every `c≥1`.
Thus a low conductor packet has logarithmic completed energy uniformly in overlap;
the former `3c⁴` upper bound is unnecessary.

## Proposed cancellation

For `u⊥V_Q`, write its coefficient packet as `u=v+y`, with coefficients of `y`
vanishing below `Q`. The existing frame estimates give `‖v‖=O((1+log R)/log N)`.
The current overlap comparison pays this leakage by the operator bound
`c(1+log c)‖v‖`, losing a factor `log c`.

Instead use the complete-form quasimode identity
`⟨Wv,u⟩=⟨residual(v),u⟩` and the logarithmic upper bound for `W(v)`.
This suggests a cost `O(log Q)‖v‖²` plus a vanishing residual, retaining
the cancellations among low-mode center, prime and overlap terms.

The coefficient-high packet `y` need not be exactly pole-orthogonal.
Its pole and center contributions must be combined before applying separate
quadratic bounds. No lower bound for that combined term is claimed yet.

## Exact sources

- `TheOverlapThatResolvesATwistIsAnExactThreshold.completedConductorEnergy_anti`.
- `ConductorBandOverlapAndNonRatioBounds.completedConductorEnergy_le_of_one_le`.
- `EveryProfileHasALogarithmicHighConductorGap.lean`: coefficient split and current overlap payment.
- `EveryPolylogConductorSpanIsPositiveAtLogLogOverlap.lean`: raw low-block residual.

The uniform diagonal upper bound has a two-line derivation from checked source
statements. Whole-form leakage cancellation remains open.
