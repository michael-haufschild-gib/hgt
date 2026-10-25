# Vaughan admission across half damping

- **ID:** vaughan-admission-phase-transition-at-half-damping
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** COMPLETE. Admission, coefficient Wiener convergence, actual upper-half row/Gram convergence, and exact infinite rank two passed final direct Lean checks and standard-axiom audits. All supporting modules are wired.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** Extend the fixed Vaughan coefficient classification through half damping and prove uniform payment of all centered pieces above half damping.

## Exact phase law

For positive fixed cutoffs, the lower-half normal form gives admitted coefficient
dimension two or three, according to admission of the actual interior receiver.
At `ε=1/2`, the actual receiver is already admitted, while the smooth square-root
sequence has divergent logarithmic energy. Thus admission is exactly
`L_w=0` and `w_2=w_3`, with coefficient dimension three.
For every `ε>1/2`, admission is exactly `L_w=0`, with dimension four, including zero cutoffs.
The linear coefficient is nonzero as a functional because its pole coordinate is `-ρ`.

## Stronger uniform upper-half statement

For each `ε>1/2`, one bound pays every centered component norm, uniformly
over the horizon and both cutoffs. The first three damped floor coefficients are
dominated by `τ(d)^2 d^(-ε)`. Its critical Wiener mass is
`Σ τ(d)^2 d^(-ε-1/2)<∞`, from the existing divisor-square Dirichlet estimate.
The proved critical Wiener floor bound then pays the first three centered components.
The pole correction is uniformly bounded, and the exact five-piece identity plus
actual receiver admission pays the fourth component. Fixed coefficient combinations
inherit a uniform norm bound depending only on their coefficient absolute sum.

## Dependency-closed proof

For `ε≥1/2`, `exists_pmPowerDampedDivisorDiscreteEnergy_budget_of_half_le` pays the
actual damped receiver. The checked theorem
`exists_pmBezoutInteriorPronicEnergy_budget_iff` transfers this to the interior energy.
The identity `E_int(T)=‖I‖_T²` then gives one bound for the interior norm.

At `ε=1/2`, the checked fixed-packet normal form applies because `0<ε<1`.
Admission already forces `L_w=0`. The square of the smooth-power norm is exactly
`Σ_(1≤n≤T)1/(n+1)`, which diverges by
`Real.tendsto_sum_range_one_div_nat_succ_atTop` after deleting its first term.
The interior and normal-form remainder have bounded norm. The reverse triangle
inequality therefore forces `Q_w=0`. Conversely, these two zero coefficients leave
only bounded terms. Finite harmonic nonvanishing gives `Q_w=0 ↔ w_2=w_3`.
The checked independent frame `b_U,b_V,1` spans the resulting three-dimensional space.

For `ε>1/2`, put `W=Σ_(d≥1)τ(d)²d^(-ε-1/2)`, finite by
`summable_divisor_sq_rpow`. Each of the first three raw floor coefficients `a` satisfies
`|a(d)|≤τ(d)²d^(-ε)`. Thus `a` lies in the critical Wiener class and
`‖A_a‖_T≤(sqrt(2)+1)W`, uniformly in both cutoffs. Absolute reciprocal convergence
identifies its mean with the explicit Vaughan mean: the checked floor-average limit
and `tendsto_pmPronicVaughanPiece_div_nat` have the same sequence, so uniqueness of
limits identifies their means. Multiplying the exact floor-average identity by `n`
identifies the centered piece with `A_a(n)`; `n=0` contributes zero.

The fourth, pole-centered piece has norm at most `1/2`. The sum of the five means is
zero, and the sum of the five raw pieces is the interior prefix. The remaining
both-large centered piece is consequently bounded by the interior bound plus the
other four bounds. If `B_I` bounds the interior norm and
`B_F=(sqrt(2)+1)W`, the single constant `B_I+3B_F+1/2` bounds every component.
The triangle inequality bounds a centered packet by this constant times `Σ_i|w_i|`.
It follows that `L_w=0` suffices for admission, while the checked linear-mean necessity
proves the converse. The nonzero linear functional `w↦L_w` has kernel dimension four.

This closes the paper proof without a new analytic premise. It does not use the
sub-half receiver-admission alternative to deduce any new admission below half damping.

## Joint Gram limit above the threshold

For every fixed `ε>1/2`, the common critical Wiener majorant also gives strong
convergence of the centered rows as both cutoffs diverge. The first two floor
coefficients converge pointwise to the full damped Möbius coefficient. The
small-small coefficient converges to its negative: once both cutoffs exceed a fixed
index, the convolution at that index is `μ⋆μ⋆1=μ`. The common majorant
`τ(d)²d^(-ε-1/2)` is summable. Dominated convergence therefore makes each coefficient
difference tend to zero in critical Wiener norm.

The checked bound `pronicNorm_weightCenteredPrefix_le_critical` is linear in that
coefficient norm and uniform over every horizon. Hence the corresponding centered
rows converge in full pronic L² to `A,A,-A`. The pole row is the fixed row
`P=-Δa_ε`; the exact five-piece sum then forces the both-large row to converge
to zero, because the interior is `A+P`. Thus, independently as `T,U,V→∞`,

`G^c(T;U,V) → Gram(A,A,-A,0,P)`.

Cauchy–Schwarz controls the errors in finite pairings uniformly in `T`; the finite
energies of the limiting rows pay their omitted horizon tails. The two-cell
determinant theorem on `the-endpoint-vaughan-limit-has-rank-two.md` applies to
every `ε>0`, so this upper-half limiting Gram has rank exactly two.

Above half damping there is a single joint limit of rank two. The row and Gram
limits, coefficient Wiener convergence, and rank assertion are all Lean-verified
below. At half damping, the additional harmonic-mass ray is a separate obligation
on the endpoint card; it is not needed for this upper-half uniqueness theorem.
These results introduce no below-half admission estimate.

## Corpus and novelty audit

- `pronicNorm_weightCenteredPrefix_le_critical` gives the explicit Wiener norm bound.
- `summable_divisor_sq_rpow` already supplies the corresponding majorant convergence
  in the uniform floor-mean module; the new exponent is `ε+1/2>1`.
- `receiverBounded_pmPowerDamped_half` uses the established source energy budget at
  half damping. The same source theorem covers all larger dampings.
- The fixed packet normal form is proved on paper for `0<ε<1`, covering the endpoint.
- The shifted harmonic divergence and the exact interior/source energy-budget
  equivalence have been read in source.
- The floor-average limit identifies the mean and therefore the exact centered-prefix
  bridge; no uniform interchange of an unbounded family of limits is required.

No new receiver admission below half damping follows. This is an exact phase
classification of the finite Vaughan family, not a solution to Q-I. The general Wiener
payment and half-damping boundary are already in the corpus; this is their exact
five-component specialization, with no external novelty claim.

## Status

All nine targets in `VaughanAdmissionAtHalfDamping.lean` passed producing and
final direct checks. Their transitive axioms are only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired and its scratch removed.
This certifies interior admission, the smooth endpoint obstruction, complete
scalar classification, exact admitted span, dimension three, and quotient
dimension two at positive cutoffs.
All eleven targets in `VaughanAdmissionAboveHalfDamping.lean` also passed
corrected producing and final direct checks with standard axioms only,
including the common
critical Wiener bound, uniform admission of every centered piece and packet, the exact
linear-mean kernel, dimension four, and quotient dimension one. The module is
wired and its scratch removed. The twenty admission targets are recorded in
`../3-formalized/vaughan-admission-at-and-above-half-damping.md`.
The shared four finite packet identities in
`VaughanPacketGramIdentities.lean` already passed final direct checks and
standard-axiom audits.

The joint upper-half Gram limit and its exact infinite rank-two consequence
are Lean-verified.
Their common summable envelope can be obtained from the positive divisor
majorant's centered floor defect: its critical Wiener bound pays the square
envelope, and the five-piece identity pays the both-large row. The already
checked all-positive cell limits and dominated moving-sum transfer then apply.
Both `MovingVaughanRowsConvergeCellByCell.lean` targets passed final direct
checks with standard axioms only; the module is wired and its scratch removed.
`UpperHalfVaughanGramsHaveAnActualLimit.lean` passed its producing check and final
direct audit; all eight targets have only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms. The module is wired and its scratch removed:
the explicit envelope norm bound, domination of all five actual rows, common
summable square and pair envelopes, summability of the limiting Gram entries,
the independent joint Gram limit, full pronic square convergence, and convergence
at every finite moving horizon. The exact declarations are:

- `pronicNorm_pmPronicVaughanUpperEnvelope_le`
- `abs_pmPronicVaughanCentredPiece_le_upperEnvelope`
- `exists_summable_pmPronicVaughanCentredPiece_upper_square_envelope`
- `exists_summable_pmPronicVaughanCentredPiece_upper_pair_envelope`
- `summable_pmPronicVaughanLimitGram_terms_of_half_lt`
- `tendsto_pmPronicVaughanCentredGram_of_half_lt`
- `tendsto_tsum_pmPronicVaughanCentredPiece_sub_limit_sq_of_half_lt`
- `tendsto_pronicNorm_pmPronicVaughanCentredPiece_sub_limit_of_half_lt`

The positive-floor domination and
dominated square-norm transfer are shared with the endpoint through
`PositiveFloorMajorantsControlPronicEnergy.lean`. All five shared transfer
targets passed corrected producing and final direct checks with standard
axioms only; the module is wired and its scratch removed. See
`../3-formalized/positive-floor-majorants-and-pronic-convergence.md`.
The actual upper-half specialization is therefore certified.
The shared moving-horizon dominated-convergence theorem also passed producing
and final direct checks with standard axioms only. Its module is wired as
`HTGeometry/MovingTruncationsPreserveDominatedLimits.lean`; see
`../3-formalized/moving-truncations-preserve-dominated-limits.md`.
All eleven targets in `TheActualVaughanLimitGramHasRankTwo.lean` passed corrected
producing and final direct checks with standard axioms only. The module is
wired and its scratch removed. For every `ε≥1/2`, the actual Gram is positive
semidefinite of rank exactly two; its prefix/pole submatrix is positive definite,
with determinant at least `2^(-4ε)/15552`. Summability is derived from the actual
endpoint and upper-half row bounds, without an additional analytic premise:

- `summable_pmPronicVaughanLimitGram_terms_of_half_le`
- `tendsto_sum_pmPronicVaughanLimitGram_terms`
- `pmPronicVaughanLimitGram_symm`
- `sum_sum_mul_pmPronicVaughanLimitGram_nonneg`
- `pmPronicVaughanLimitGram_eq_two_outer_products`
- `rank_pmPronicVaughanLimitGram_le_two`
- `pmPronicVaughanLimitGram_prefix_pole_minor_lower`
- `pmPronicVaughanLimitGram_pole_lower`
- `pmPronicVaughanLimitGram_posSemidef`
- `pmPronicVaughanLimitGram_prefix_pole_posDef`
- `rank_pmPronicVaughanLimitGram`

The paper's separate coefficient-level assertion is now Lean-verified in
`TheVaughanFloorCoefficientsConvergeInCriticalWienerNorm.lean`. Its three targets
prove exact finite small-small stabilization and critical Wiener convergence
of both truncated Möbius legs and the signed small-small coefficient. All
three passed the final direct check with standard axioms only; the module is
wired and its scratch removed. See
`../3-formalized/vaughan-floor-coefficients-converge-in-critical-wiener-norm.md`.
