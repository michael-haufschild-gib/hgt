# Whole-form payment for low coefficient leakage

- **Stage:** 0-backlog.
- **Type:** CONJECTURE.
- **Wall:** Σ1d.
- **Target:** Fixed polynomial conductor spans through a super-log-log overlap clock for every nonzero compact real `C²` profile.

## New input

Monotonicity in overlap and the existing bound at overlap one imply
`E_m(c)≤|selfφ(1)|+2log m+3` for every `c≥1`.
Thus a low conductor packet has logarithmic completed energy uniformly in overlap;
the former `3c⁴` upper bound is unnecessary.

## Proposed cancellation

For `u⊥V_Q`, write its coefficient packet as `u=v+y`, with coefficients of `y`
vanishing below `Q`. The existing frame estimates give `‖v‖=O((1+log R)/log N)`.
The linear-moment overlap bound pays this leakage by `Oφ(c)‖v‖`.
This gives the fixed log-log interval in
`exists_universal_loglog_polynomial_span_coercivity`, with a clean Lean audit.
For a fixed polynomial cutoff, the remaining `c(1+log R)/log N` cost prevents
the same estimate from reaching a super-log-log interval.

Instead use the complete-form quasimode identity
`⟨Wv,u⟩=⟨residual(v),u⟩` and the logarithmic upper bound for `W(v)`.
This suggests a cost `O(log Q)‖v‖²` plus a vanishing residual, retaining
the cancellations among low-mode center, prime and overlap terms.

The coefficient-high packet `y` need not be exactly pole-orthogonal.
Its pole and center contributions must be combined before applying separate
quadratic bounds. No lower bound for that combined term is claimed yet.

## Remaining center payment

The center proof separates the constant coefficient from a mean-zero periodic
packet. Its collar near term still costs `(1+log R)/log N`, even after that
coefficient is removed. Whole-form leakage cancellation alone therefore does
not remove every `c(1+log R)/log N` term.

The existing collar proof suggests a more direct bound. For a prefix packet
`z∈V_M∩V_1^⊥` and a larger packet `w∈V_R∩V_1^⊥`, retain the linear moments of
both arguments in `collar_half_pair_le` and `collar_near_pair_le`.
The desired mixed-prefix estimate is
`|⟨center z,w⟩|≤C|α|(1+log M)‖z‖‖w‖/log N`.
Applying `conductor_packet_sq_le_logarithmic_weight` would then give
`|⟨center u,u⟩|²≤Cα²(1+log R)G‖u‖²/(log N)²`.
For polynomial `R` and `c≤(log log N)²`, its coefficient tends to zero and
prime adjunction pays the center. The existing weighted cross theorem has only
one denominator `log N`, because its second argument is arbitrary.

For coefficient-high packets, the remaining arithmetic pole term involves the
unweighted sum of mean-zero periodic Ramanujan modes. Finite-period cancellation
may make that term negligible after its `1/N` factor; this still needs a bound.

The exact definition confirms that `fullWeilPoleErrorMatrix` is also a scalar
multiple of `arithmeticPoleKernel`. Both pole contributions therefore use the
same two moments. For a packet with zero conductor-one coefficient, periodic
cancellation bounds its unweighted mode sum by `2R²` times its coefficient
norm; the remaining harmonic moment is bounded by Cauchy–Schwarz.
The direct inequality `poleDefect_normalizedRamanujanPacket_ge_logarithmic`
does not require pole orthogonality, so it remains available on the
coefficient-high packet before the complete-form leakage identity is applied.

With those two bounds, `W(u)=W(y)−W(v)+2⟨Wv,u⟩` would cost only
`O((1+log Q)ρ²)` for `ρ=(1+log R)/log N`, plus the raw low residual.
For a sufficiently small fixed polynomial exponent, this is absorbable into
the `log Q` gap independently of `c≤(log log N)²`. The explicit spectral clock
would then give the conjectured super-log-log interval.

## Exact sources

- `TheOverlapThatResolvesATwistIsAnExactThreshold.completedConductorEnergy_anti`.
- `ConductorBandOverlapAndNonRatioBounds.completedConductorEnergy_le_of_one_le`.
- `ConductorEnergiesHaveAUniformLogarithmicUpperBound.completedConductorEnergy_le_logarithmic_uniform`.
- `EveryProfileHasALogarithmicHighConductorGap.lean`: coefficient split and current overlap payment.
- `EveryPolylogConductorSpanIsPositiveAtLogLogOverlap.lean`: raw low-block residual.

The uniform diagonal upper bound is formalized in
`CompletedArithmeticForms/ConductorEnergiesHaveAUniformLogarithmicUpperBound.lean`.
Its direct source check passed; transitive axioms are only `propext`,
`Classical.choice`, `Quot.sound`. Whole-form leakage cancellation remains open.
