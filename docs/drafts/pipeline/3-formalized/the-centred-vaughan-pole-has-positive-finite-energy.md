# The centered Vaughan pole has positive finite energy

- **ID:** the-centred-vaughan-pole-has-positive-finite-energy
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** All seven energy/rate targets and the actual endpoint product-horizon consequence passed final direct Lean checks and standard-axiom audits.
- **Source:** uniform-vaughan-residual-power-rates-are-fixed-strips.md
- **Statement:** For every `ε≥0`, the centered pole energy has a cutoff-independent limit `L_ε` with `2^(-2ε)/32≤L_ε≤1/4`. Consequently its normalization by `T^(1-2ε)` cannot decay with a larger power exponent.
- **Novelty status:** Exact positive first-cell refinement of the existing active-pair energy bound. No external novelty claim.

## Exact energy and positive limit

Write `a_ε(n)=pmActiveSawtoothComponent ε n`. The checked source formula is

`a_ε(n)=-(c_ε(n)-c_(1+ε)(n))/2`.

At a prime `p`, divisor inversion gives `c_ε(p)=1-p^(-ε)`. Also `a_ε(1)=0`.
Thus `a_ε(2)=2^(-ε)/4`, and its forward difference at `1` is `2^(-ε)/4`.
The centered pole piece is exactly `-Δa_ε(n)`, independently of both cutoffs.
Therefore

`G^c_44(T;U,V)=Σ_(1≤n≤T)|Δa_ε(n)|²/[n(n+1)]`.

For `T≥1`, its first summand is `2^(-2ε)/32>0`. All remaining terms are
nonnegative. The existing source theorem `pmActivePairPronicEnergy_bounds` bounds
the whole sum by `1/4` when `ε≥0`. Monotone bounded partial sums consequently
converge to a finite `L_ε` satisfying the stated two-sided bounds. This limit
persists under arbitrary moving cutoff schedules, because the identity is exact
before taking a limit.

## Sharp restriction on a possible rate

Put `β=1-2ε`. If `δ>β` and some constant bounded

`G^c_44(T;U(T),V(T))/T^β≤C/T^δ`

for every positive horizon, then `G^c_44(T)≤C T^(-(δ-β))→0`. This contradicts
its explicit positive first cell. The same contradiction applies to eventual
bounds after absorbing a finite initial interval.

For `0<ε<1/2`, the universal smooth Gram coefficient in entry `(4,4)` is zero.
Thus a power rate for the entire residual matrix can have exponent at most
`1-2ε`. The harmonic contrast's separate exponent-one obstruction still describes
the convolution block after the pole row is removed.

At half damping the pole entry converges to a positive constant. When both
cutoffs diverge, the product-horizon Gram tends to the actual matrix of rows
`(A,A,-A,0,P)`. Its rank is exactly two and its pole diagonal is at least `1/64`;
in particular this limit is nonzero. Product divergence alone removes the
harmonic mass; convergence to this particular matrix uses both divergent cutoffs.

## Positive survivor and status

The obstruction preserves a concrete invariant: a positive finite source energy,
with an explicit lower bound and a cutoff-independent limiting value. It does not
exclude positive power savings below the stated cap and does not answer full Q-I.

All seven targets in
`BezoutValuationIncidence/TheCentredVaughanPoleHasPositiveFiniteEnergy.lean`
passed corrected producing and final direct checks. Each transitive axiom audit
contains only `propext`, `Classical.choice`, and `Quot.sound`. The module is
wired and its scratch removed:

- `addDiff_pmActiveSawtoothComponent_one`
- `pmActivePairPronicEnergy_one`
- `pmActivePairPronicEnergy_lower`
- `pmPronicVaughanCentredGram_pole_eq_active`
- `exists_tendsto_pmActivePairPronicEnergy`
- `exists_positive_tendsto_pmPronicVaughanCentredGram_pole`
- `not_pmPronicVaughanCentredGram_pole_faster_power`

The final theorem rules out eventual faster-power bounds, including arbitrary
moving cutoffs. The actual endpoint matrix is now formally nonzero, with
pole entry at least `1/64`, in `TheActualEndpointVaughanGramHasRankTwo.lean`.
The endpoint convergence theorem
`tendsto_pmPronicVaughanCentredGram_half_product` in
`ProductHorizonVaughanGramsAtHalfDampingHaveFiniteLimits.lean` also passed its
final direct check and standard-axiom audit. Together with
`pmPronicVaughanHalfLimitGram_ne_zero`, it discharges the stated nonzero-limit
consequence. All supporting modules are wired. No route is retired.
