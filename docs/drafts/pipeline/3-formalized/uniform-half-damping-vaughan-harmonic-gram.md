# Uniform harmonic Gram law at half damping

- **ID:** uniform-half-damping-vaughan-harmonic-gram
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Verification:** Every stated finite Gram/packet, moving-limit, pronic-convergence, rank, harmonic-mass, realization, and product-horizon claim passed final direct Lean checks and standard-axiom audits.
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** At half damping, the centered Vaughan Gram differs from its explicit harmonic rank-one term by a bounded matrix uniformly over all cutoffs and horizons. Its renormalized moving-cutoff limit is an actual finite Gram of two source rows.
- **Novelty status:** Endpoint refinement of the uniform convolution argument; initial corpus search found the fixed-cutoff admission law and smooth-power estimates, not this uniform bounded-error statement. No external novelty claim.

## Exact endpoint statement

Fix `ε=1/2`. Let `e_i(n;U,V)` be the five centered pieces,
`H_U=Σ_(d≤U)μ(d)/d`, `K_(U,V)=subHalfZetaCoeff(1/2)H_UH_V`,
`s=(0,0,-1,1,0)`, and `J(T)=Σ_(1≤n≤T)1/(n+1)`.
There is a finite constant `C`, independent of `U,V,T,i,j`, such that

`|G^c_ij(T;U,V)-K_(U,V)^2 s_i s_j J(T)|≤C`.

In particular, every entry outside the two-by-two convolution block is uniformly
bounded. The convolution block has one explicit harmonic divergence. Removing its
smooth coefficient gives uniform bounded energy, even when the cutoffs move.

## Uniform pointwise remainder

The dependency-closed paper argument in the source card proves arbitrary logarithmic
mean-error bounds for the undamped small-small coefficient
`a_(U,V)=μ_≤U⋆μ_≤V⋆1`, with mean `H_UH_V`. Its bound
`|a_(U,V)(d)-H_UH_V|≤C₀ τ(d)^2` is uniform in both cutoffs.

At half damping the generalized finite hyperbola estimate remains valid:

`|A_r(n)|≤C₁ D^(1/2)(1+log D)^4+26 L_D n D^(-1/2)`,

where `L_D` is a common bound for `|Σ_(d≤x)r(d)|/x` for all `x≥D`.
For any prescribed `A>0`, take `D=floor(n/(log n)^b)` with
`b/2>A+4`, and use a partial-sum logarithmic rate of order greater than `A+b/2`.
The resulting bound is `O_A(sqrt(n)/(log n)^A)` uniformly in `U,V`.

The same argument applies uniformly to the truncated Möbius patterns. Indeed,
their partial sums are `M(min(U,x))`. If `min(U,x)≤sqrt(x)`, their absolute value
is at most `sqrt(x)`. Otherwise the checked arbitrary logarithmic Mertens estimate,
with `log(min(U,x))≥(log x)/2`, gives a common arbitrary logarithmic rate.
The untruncated actual Möbius pattern has that rate as well.

For the unit pattern, the read source theorem `abs_subHalfRemainder_le` gives
remainder `O(n^(1/4))` at `ε=1/2`. It is not a pointwise constant bound; the
quarter-power error is still smaller than `sqrt(n)/(log n)^A` for every fixed `A`.
The harmonic factors are uniformly bounded. The pole correction is bounded by `1/2`.
The exact sum of the five centered pieces is the interior prefix.

Consequently there are remainders `r_i(n;U,V)` with

`e_i(n;U,V)=K_(U,V)s_i sqrt(n)+r_i(n;U,V)`

and, for every fixed `A`, a common eventual estimate

`|r_i(n;U,V)|≤C_A sqrt(n)/(log n)^A`.

A finite initial interval has one uniform bound: the summable Vaughan divisor
majorant bounds all centered pieces by a fixed multiple of `n`, and `K_(U,V)` is
bounded. These statements include zero cutoffs.

## Summing the Gram error

Use the remainder estimate with `A=2`. Uniformly in `U,V,i`, both sums

`Σ_(n≥1) sqrt(n)|r_i(n;U,V)|/[n(n+1)]`,
`Σ_(n≥1) |r_i(n;U,V)|^2/[n(n+1)]`

are bounded. Their tails are dominated respectively by constant multiples of
`1/(n(log n)^2)` and `1/(n(log n)^4)`; the finite initial ranges are already paid.
Expanding the product of the two centered pieces proves the stated bounded error.
This is stronger than a norm-triangle `O(sqrt(log T))` error because the mixed
smooth/remainder pairing is absolutely summable.

For any real coefficient vector `w`, writing `Q_w=K_(U,V)(w_3-w_2)`, the same bound gives

`|‖Σ_i w_i e_i‖_T^2-Q_w^2 J(T)|≤C(Σ_i|w_i|)^2`.

Thus packets with `Q_w=0` have one uniform bound over all cutoffs and horizons.
At positive cutoffs, harmonic nonvanishing identifies that condition with `w_2=w_3`.
For the uncentered packet one must also remove its linear mean.

## The moving renormalized Gram

Let `A(n)` be the actual centered power-damped Möbius divisor prefix at half damping,
and let `P(n)` be the centered pole piece, namely minus the active correction.
Both rows have finite pronic energy. Set

`R=(A,A,-A,0,P)`.

For each fixed `n`, as both cutoffs tend to infinity, the small pieces tend to `A`,
the small-small piece tends to `-A` by the actual convolution identity, and the
both-large piece tends to zero. Their means converge to the full reciprocal mean.
Also `H_UH_V→0`, so each `r_i(n;U,V)→R_i(n)`.

The common summable squared envelope above gives convergence of the remainders in
pronic L². This also holds for partial pairings at any horizon `T→∞`: the common
summable envelope pays the omitted tail uniformly. Their pairings therefore tend to

`G∞_ij=Σ_(n≥1)R_i(n)R_j(n)/[n(n+1)]`.

The two smooth/remainder pairings are uniformly bounded in absolute value, while
`K_(U,V)→0`. Hence, with `T,U,V→∞` independently,

`G^c_ij(T;U,V)-K_(U,V)^2 s_i s_j J(T) → G∞_ij`.

The limiting matrix is positive semidefinite and has rank exactly two. All five rows
lie in the span of `A` and `P`; their two-cell determinant proves independence, with
`det Gram(A,P)≥1/62208`, as shown in `../3-formalized/the-endpoint-vaughan-limit-has-rank-two.md`.
The positive first pole cell also gives `G∞_44≥1/64`; see
`../3-formalized/the-centred-vaughan-pole-has-positive-finite-energy.md`. Both refinements are
Lean-verified, including positive definiteness and the explicit nonzero matrix.
A finite limit of the scalar harmonic mass `K_(U,V)^2 J(T)→ℓ` gives
actual Gram limit `G∞+ℓssᵀ`; harmonic mass tending to `+∞` forces the corresponding
convolution diagonal to tend to `+∞`. Mere unboundedness does not assert convergence
to infinity. The cutoff/horizon interaction is thus carried by
one explicit nonnegative scalar at the endpoint.

The finite limiting matrices consequently form the ray `G∞+ℓssᵀ`, `ℓ≥0`.
Their rank is two for `ℓ=0` and three for `ℓ>0`: the independent coefficient
directions `(1,1,-1,0,0)` and `(0,0,0,0,1)` supporting `G∞` have zero fourth
coordinate, whereas `s` does not. Conversely, convergence of the full Gram forces
convergence of the harmonic mass, because its `(3,3)` entry is that mass plus a
remainder tending to zero.

Every value `ℓ≥0` is attainable with both cutoffs divergent. For `ℓ=0`, take
`U=V=N,T=N²`. For `ℓ>0`, put `k_N=K_(N,N)^2>0` and choose the first integer
`T_N` with `k_N J(T_N)≥ℓ`. Harmonic divergence guarantees existence; finite
harmonic nonvanishing gives `k_N>0`. Each increment of `J` is at most one, so
`ℓ≤k_N J(T_N)≤ℓ+k_N`. Since `k_N→0`, the mass tends to `ℓ`. Also `J(T)≤T`;
for any fixed bound `B`, eventually `k_N B<ℓ`, forcing `T_N>B`.
Thus the ray is the exact set of
finite joint-limit matrices, not merely an upper description. The rank
corollaries and realization of every ray point are Lean-verified.

## Product horizons

At `T=UV`, let `W=max(U,V)`. For positive cutoffs, `T≤W²`, so
`J(T)≤1+2log W`. The harmonic factors are bounded, and the factor at `W` has every
logarithmic saving. Consequently `K_(U,V)^2 J(UV)→0` whenever `UV→∞`, uniformly in
the factorization. Finite products and zero products are harmless. The centered
product-horizon trace therefore has one uniform finite bound at half damping.
If both cutoffs diverge, the actual centered product-horizon Gram tends to `G∞`.
The limit is nonzero: its pole diagonal is at least `1/64`.

The checked Lean proof uses an equivalent separated majorant:
`J(UV)≤(1+log U)(1+log V)` for positive cutoffs. The nonnegative sequence
`g(N)=H_N²(1+log N)` tends to zero and is globally bounded. Hence
`K_(U,V)²J(UV)≤subHalfZetaCoeff(1/2)² g(U)g(V)`. The checked product-index
lemma makes the right side vanish whenever `UV→∞`, including factorizations
with one bounded cutoff. This also directly supplies the common finite bound.

## Audit and status

Read source dependencies include `abs_subHalfRemainder_le`, the checked mean-zero
prefix hyperbola estimate at `ε≤1/2`, the actual half-damping receiver budget,
arbitrary logarithmic Mertens and harmonic bounds, the exact five-piece identity,
and the uniform finite floor majorant. The endpoint argument introduces no new
analytic premise. The uniform double-convolution logarithmic theorem, generic
damped logarithmic transfer, actual convolution fluctuation, and uniform
truncated-Möbius logarithmic prefixes are now checked
in Lean. The actual bounded-error and renormalized moving-limit laws are
verified, including full pronic convergence, exact rank two, and the harmonic-mass
convergence criterion with the rank-two/three ray law. Product-horizon corollaries
and arithmetic realization are also checked. Full Q-I remains open.

The generic endpoint summation step is Lean-verified in
`UniformCriticalPronicPairingsFromLogarithmicCancellation.lean`: two logarithms
in a common critical-prefix bound give one summable envelope dominating both
the squared cell and its absolute square-root mixed cell. A common linear
majorant pays the finite head. All three targets passed corrected producing
and final direct checks with standard axioms only. The module is wired and
its scratch removed; see [the audit](../3-formalized/uniform-critical-pronic-pairings-from-logarithmic-cancellation.md).
The actual five-row pointwise specialization also passed its producing and
final direct checks. All six targets have standard transitive axioms only.
`UniformLogarithmicPrefixRemaindersInAllVaughanRows.lean` proves the bounded
active correction, unit-pattern remainder, exact both-large triangle bound,
common logarithmic prefix rate through half damping, and common linear
finite-head bound. The module is wired and its scratch removed; see
[the prefix audit](../3-formalized/uniform-logarithmic-prefix-remainders-in-all-vaughan-rows.md).
The three actual specializations passed corrected producing and final direct
checks with standard axioms only in `UniformHarmonicVaughanGramsAtHalfDamping.lean`:
one summable envelope for every endpoint remainder, common energy and absolute
mixed-pairing bounds, and the uniform bounded harmonic Gram error. The module
is wired and its scratch removed; see
[the endpoint Gram audit](../3-formalized/uniform-harmonic-vaughan-grams-at-half-damping.md).
The three packet laws also passed their corrected final direct check and
standard-axiom audits in `UniformHarmonicEnergyLawsForVaughanSuperpositions.lean`.
Their homogeneous error bound and both smooth-annihilation corollaries are
included in the endpoint Gram audit. The packet module is wired and its
scratch removed. Moving renormalized limits and exact ray ranks are also checked below.

## Relation to subcritical limit classification

The Lean-verified classification
`../3-formalized/vaughan-subcritical-gram-limit-classification.md` identifies the normalized
subcritical limit set as a countably infinite compact family, discrete away from
zero. Positive nonzero limits there require an eventually fixed harmonic amplitude
and bounded cutoffs. At half damping, the additional factor `J(T)` amplifies
vanishing amplitudes into every finite nonnegative harmonic mass, producing the
continuous ray above even with both cutoffs divergent. The distinction concerns
the exact limiting matrices; it supplies no fixed-strip power estimate.

## Moving-cell proof obligations

`MovingVaughanRowsConvergeCellByCell.lean` proves the centered and smooth-remainder
cell limits, importing the checked finite row frame from the twelve-target
independence module. For each fixed cell, the finite floor sums stabilize once both cutoffs
cover it; the checked moving-mean theorem supplies their centered limits. The
five-piece identity supplies the convolution limit without exchanging an
infinite convolution and a limit. This argument works for every `ε>0`, a
stronger pointwise statement than the endpoint application. The source hypotheses
were checked at every positive damping; no energy conclusion follows from this
pointwise extension alone. Both targets passed corrected producing and final
direct checks with standard axioms only. The module is wired and its scratch
removed:

- `tendsto_pmPronicVaughanCentredPiece_moving_cell`
- `tendsto_pmPronicVaughanSmoothRemainder_moving_cell`

All twelve targets in `TheVaughanLimitRowsAreIndependentInTwoCells.lean`
passed final direct checks with standard axioms only. Dominated endpoint moving
pairings and rank two are also checked below. The harmonic-mass convergence
criterion and ray ranks are checked as well; product-horizon consequences are
certified below, together with arithmetic realization.

The five shared majorant and pronic-convergence targets are certified in
`PositiveFloorMajorantsControlPronicEnergy.lean`. Positive reciprocal majorants
dominate centered floor prefixes; one summable square envelope gives full
pronic convergence and convergence at any moving finite horizon. Corrected
producing and final direct checks passed with standard axioms only; the module
is wired and its scratch removed. See
[the transfer audit](../3-formalized/positive-floor-majorants-and-pronic-convergence.md).

The reusable passage from a common summable envelope and cellwise convergence
to sums at independently growing horizons passed producing and final direct
checks with standard axioms only in
`HTGeometry/MovingTruncationsPreserveDominatedLimits.lean`. The module is wired
and its scratch removed; see
[the moving-sum audit](../3-formalized/moving-truncations-preserve-dominated-limits.md).
All six actual endpoint applications in
`UniformHalfDampingVaughanGramsHaveAnActualLimit.lean` passed corrected producing
and final direct checks with only standard axioms. The module is wired and
its scratch removed. The final step uses the common absolute mixed-pairing
bound and vanishing harmonic amplitude:

- `exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope`
- `summable_pmPronicVaughanHalfLimitGram_terms`
- `tendsto_pmPronicVaughanSmoothRemainder_half_pairing`
- `tendsto_tsum_pmPronicVaughanSmoothRemainder_half_sub_limit_sq`
- `tendsto_pronicNorm_pmPronicVaughanSmoothRemainder_half_sub_limit`
- `tendsto_pmPronicVaughanCentredGram_half_sub_harmonic`

These prove absolute summability of the actual limiting pairings, convergence
at independently divergent horizons, full pronic square convergence, and norm
convergence at every finite moving horizon. Realization of every ray point
and the product-horizon consequences are checked below.

The endpoint packet consequence is certified in `UniformHarmonicEnergyLawsForVaughanSuperpositions.lean`:
the harmonic energy error is bounded by one constant times the square of the
absolute coefficient sum. Two further targets give common energy bounds when
the smooth coefficient vanishes, in particular when the two convolution
coefficients agree. All three passed their final direct check and standard-axiom
audits; their declarations are listed in the endpoint Gram audit linked above.

All eleven targets in `TheActualEndpointVaughanGramHasRankTwo.lean` passed
producing and final direct checks with standard axioms only. The module is
wired and its scratch removed. They certify positive semidefiniteness,
the positive-definite prefix/pole submatrix, determinant at least `1/62208`,
pole entry at least `1/64`, a nonzero matrix, and exact rank two. See the
complete rank card linked above. All eleven targets in
`TheHalfDampingVaughanGramLimitsFormARankThreeRay.lean` also passed corrected
producing and final direct checks with standard axioms only, under default limits.
The module is wired and its scratch removed. They certify nonnegative harmonic
mass, its scalar readout at `(3,3)`, both directions of the finite convergence
criterion, divergence equivalence, and the exact ray ranks:

- `pmPronicVaughanHalfHarmonicMass_nonneg`
- `pmPronicVaughanHalfLimitGram_large`
- `pmPronicVaughanHalfLimitRay_large_diag`
- `tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass`
- `tendsto_pmPronicVaughanCentredGram_half_large_sub_harmonicMass`
- `tendsto_pmPronicVaughanCentredGram_half_large_atTop_iff`
- `pmPronicVaughanCentredGram_half_limit_forces_harmonic_mass`
- `tendsto_pmPronicVaughanCentredGram_half_iff_harmonic_mass`
- `pmPronicVaughanHalfLimitRay_zero`
- `rank_pmPronicVaughanHalfLimitRay_of_pos`
- `rank_pmPronicVaughanHalfLimitRay`

All six targets in `ProductHorizonVaughanGramsAtHalfDampingHaveFiniteLimits.lean`
passed corrected producing and final direct checks with standard axioms only.
The module is wired and its scratch removed:

- `sum_Icc_reciprocal_succ_product_le`
- `tendsto_pmPronicVaughanHalfHarmonicMass_product`
- `exists_uniform_pmPronicVaughanHalfHarmonicMass_product_bound`
- `exists_uniform_pmPronicVaughanCentredGram_half_product_bound`
- `exists_uniform_pmPronicVaughanCentredGram_half_product_trace_bound`
- `tendsto_pmPronicVaughanCentredGram_half_product`

The first five require no separate divergence of both cutoffs. The final
matrix-limit theorem does require both cutoffs to diverge. The stronger entry
bound follows directly from the common harmonic Gram error and bounded mass.
All four generic targets in
`HTGeometry/VanishingPositiveScalesRealizeHarmonicMasses.lean` passed producing
and final direct checks with standard axioms only. The module is wired and
its scratch removed:

- `shiftedHarmonicSum_le`
- `tendsto_shiftedHarmonicSum_atTop`
- `exists_scaled_shiftedHarmonicSum_between`
- `exists_tendsto_scaled_shiftedHarmonicSum`

They formalize harmonic divergence and first-crossing realization for every
positive vanishing scale. All three actual arithmetic targets in
`EveryNonnegativeEndpointVaughanLimitIsRealized.lean` passed their final direct
check with standard axioms only. The module is wired and its scratch removed:

- `exists_pmPronicVaughanHalfHarmonicMass_limit`
- `exists_pmPronicVaughanCentredGram_half_limit`
- `pmPronicVaughanCentredGram_half_joint_limit_iff`

Actual finite harmonic nonvanishing and logarithmic cancellation supply the
positive vanishing scale without an analytic premise. These targets certify
every nonnegative mass, every ray matrix, and both directions of the exact
joint-limit classification with all three schedules divergent.

The eleven checked ray targets include the exact equivalence between
divergence to `+∞` of the fourth diagonal and of the harmonic mass. This corrects
the earlier overly weak word “unbounded”; no unconditional divergence is claimed.
