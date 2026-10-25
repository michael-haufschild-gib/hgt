# Uniform second-scale Vaughan Gram at all cutoffs

- **ID:** uniform-second-scale-vaughan-gram-at-all-cutoffs
- **Stage:** 2-fully-proven
- **Type:** CLAIM (Lean verification pending)
- **Verification:** UNPROVED. The argument below is not a certified result until its Lean proof and transitive axiom audit pass; checked component lemmas are identified separately.
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** The fixed-cutoff smooth-power Gram asymptotic holds uniformly over every pair of cutoffs, without a product-horizon relation.
- **Novelty status:** A uniform refinement of the checked fixed-cutoff law, derived from the corpus's arbitrary logarithmic Möbius estimates. No external novelty claim.

## Statement

For `0<ε<1/2`, let `β=1-2ε`, `H_U=Σ_(d≤U)μ(d)/d`,
`K_(U,V)=subHalfZetaCoeff(ε)H_UH_V`, and `s=(0,0,-1,1,0)`.
The checked fixed-cutoff law is

`G^c_ij(T;U,V)/T^β → K_(U,V)^2 s_i s_j/β`.

In fact,

`sup_(U,V) |G^c_ij(T;U,V)/T^β - K_(U,V)^2 s_i s_j/β| → 0`.

This controls unrestricted triples `(T,U,V)`. It gives no fixed power saving.

## Uniform mean of the undamped convolution

Write `M(x)=Σ_(d≤x)μ(d)`, `H_U=Σ_(d≤U)μ(d)/d`, and

`a_(U,V)(n)=(μ_≤U ⋆ μ_≤V ⋆ 1)(n)`.

The existing arbitrary logarithmic rates give, for every integer `A>0`, constants
`C_A,X_A` such that for every `x≥X_A`,

`|M(x)|/x + |H_x| ≤ C_A/(log x)^A`.

Also `|H_x|≤B` for one constant `B`. All constants below are independent of `U,V`.

First put `S_V(y)=Σ_(b≤V)μ(b) floor(y/b)`. If `V≤√y`, rounding gives
`|S_V(y)-yH_V|≤V≤√y`. If `V>√y`, Möbius inversion gives the exact identity

`S_V(y)=1-Σ_(k≤y/(V+1)) [M(floor(y/k))-M(V)]`.

Every nonempty summand has both arguments at least `V`. A tail envelope `η(V)` for
`|M(x)|/x` therefore yields

`|S_V(y)|≤1+η(V)y(2+log y)`.

Together with the bound for `H_V`, this proves, for every `A`,

`sup_V |S_V(y)-yH_V|/y = O_A((log y)^(-A))`.

Now let `S_(U,V)(x)=Σ_(n≤x)a_(U,V)(n)`. If `min(U,V)≤x^(1/4)`, symmetry lets
us take `U≤x^(1/4)` and use

`S_(U,V)(x)=Σ_(a≤U)μ(a) S_V(floor(x/a))`.

Every nonempty argument is at least `x^(3/4)/2` for sufficiently large `x`. The preceding
uniform bound costs at most the harmonic factor `1+log x`. The additional rounding
error in replacing `floor(x/a)H_V` by `(x/a)H_V` is at most `BU≤Bx^(1/4)`.
Starting with a larger logarithmic exponent absorbs both errors.

If both `U,V>x^(1/4)`, use the exact undamped Vaughan identity

`M(x)=M(min(U,x))+M(min(V,x))-S_(U,V)(x)+R_(U,V)(x)`,

where

`R_(U,V)(x)=Σ_(U<a≤x/(V+1)) μ(a)
  Σ_(k≤x/(a(V+1))) [M(floor(x/(ak)))-M(V)]`.

The inner arguments are at least `V>x^(1/4)`. Taking absolute values only after
applying the signed Mertens estimate gives

`|R_(U,V)(x)|≤η(x^(1/4)) x (1+log x)(2+log x)`.

The other two Mertens terms have the same arbitrary logarithmic saving. The product
`H_UH_V` is uniformly small by the harmonic estimate. If a cutoff is zero, the
convolution and its mean are zero. Consequently, for every `A>0`,

`sup_(U,V) |S_(U,V)(x)-xH_UH_V|/x = O_A((log x)^(-A))`.

The first two terms of the undamped Vaughan identity are truncated Möbius sums,
not the floor sums `S_U,S_V`.

### A direct finite bound

The uniform double-convolution argument also admits a shorter proof that avoids
feeding the single-floor asymptotic back through a second convolution. Let `h(n)`
be the ordinary harmonic sum. Suppose `1≤D≤n`, `L,K≥0`, and for every `x≥D`,

`|M(x)|≤Lx`, `|H_x|≤K`.

Then, for every `U,V`,

`|S_(U,V)(n)-nH_UH_V|
 ≤D²+D+3Ln+2Ln h(n)²+Kn`.                                     (1)

Here the read corpus theorem `abs_sum_moebius_div_le_one` gives `|H_U|≤1` for
all positive `U`; the zero cutoff has zero harmonic sum. Its elementary proof uses
the sharper rounding remainder `1-1/d` in Möbius floor inversion, with the first
harmonic term absorbing the excess.

If both cutoffs are less than `D`, direct rounding of the double floor sum gives
error at most `UV≤D²`. Otherwise symmetry lets `V≥D`. In the exact Vaughan
identity, the three Mertens terms cost at most `D+3Ln`: the term at `min(U,n)`
costs at most `D` when `U<D`, and at most `Ln` otherwise; the other two arguments
are at least `D`.

For the both-large remainder, each nonempty inner Möbius block ends at
`q=floor(n/(ak))≥V` and is bounded by `|M(q)|+|M(V)|≤2Lq≤2Ln/(ak)`.
Taking absolute values of the remaining Möbius coefficient and enlarging the two
outer ranges to `1,…,n` costs at most `2Ln h(n)²`. Finally
`n|H_UH_V|≤Kn`. This proves (1), including zero cutoffs.

Choosing `D=floor(n^(1/4))`, and taking the Mertens and harmonic logarithmic
estimates two orders higher than the desired rate, recovers every uniform logarithmic
rate above. No estimate for the single-floor family is needed in this proof.

If a Mertens power rate with gain `η>0` is supplied, the corresponding harmonic
bound gives `L,K=O(D^(-η))`. Balancing the head `D²` with the tail `nD^(-η)`
at `D≈n^(1/(2+η))` yields every gain strictly below `η/(2+η)` for the undamped
convolution mean, uniformly in both cutoffs. This strengthens the quantitative
transfer used in the fixed-strip equivalence; it does not produce a power rate.
The harmonic transfer itself is now Lean-verified in
`RHTower/MertensPowerBoundsControlMobiusHarmonicSums.lean`: the exact successor
boundary minus strict tail gives constant `C(1+1/η)` at the original exponent.
Both targets passed final direct checks and standard-axiom audits. The balanced
uniform-convolution consequence remains under verification.

## Transfer through the damped floor transform

Set `λ=H_UH_V` and `r_(U,V)(d)=a_(U,V)(d)-λ`. Its value at zero contributes neither
to a positive-index sum nor to the reciprocal mass. For positive `d`,
`|r_(U,V)(d)|≤(1+B²)τ(d)²`. The corpus's divisor-square estimate gives

`Σ_(d≤D)|r_(U,V)(d)|d^(-ε)
 ≤ (1+B²)D^(1-ε)(1+log D)^4`.

Indeed, pull out `d^(1-ε)≤D^(1-ε)` and apply
`Σ_(d≤D)τ(d)²/d≤(1+log D)^4`. The same divisor majorant gives absolute convergence
of `Σ|r_(U,V)(d)|d^(-1-ε)`, uniformly in both cutoffs.

The finite hyperbola proof of
`abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos` gives the more general bound

`|A_(r,ε)(n)|≤Σ_(d≤D)|r(d)|d^(-ε)+(13/ε)L n D^(-ε)`

whenever `1≤D≤n`, the reciprocal series converges absolutely, and
`|Σ_(d≤x)r(d)|≤Lx` for every `x≥D`. The coefficient bound `|r|≤1` in the existing
lemma is used only to bound the displayed head and to establish summability. The
finite Abel interval bound has no coefficient bound; the infinite tail follows from
that same finite bound and the supplied summability. Thus the divisor majorant
discharges both uses without inserting a new analytic assumption.

Choose a fixed real `b>4/(1-ε)` and `D=floor(n/(log n)^b)`. Eventually `D≥√n`.
The head, divided by `n^(1-ε)`, is
`O((log n)^(4-b(1-ε)))`, which tends to zero. Choose an integer `A>bε+1` in the
uniform partial-sum bound above. For all `x≥D`, it supplies
`L=C_A/(log D)^A`. The normalized tail is
`O((log n)^(bε-A))`, which also tends to zero. Therefore

`sup_(U,V) |A_(r_(U,V),ε)(n)|/n^(1-ε) → 0`.

The common absolutely convergent divisor majorant gives `|A_(r,ε)(n)|≤Cn` for
all cutoffs. Splitting the pronic energy at a common threshold and using
`Σ_(n≤T)n^(-2ε)=O(T^β)` upgrades the preceding limit to

`sup_(U,V) ||A_(r_(U,V),ε)||_T / T^(β/2) → 0`.

## Uniform Gram law

Linearity of the damped floor transform and the checked unit-pattern normal form give

`p_2^c(n)=-λ subHalfZetaCoeff(ε)n^(1-ε)+e_(U,V)(n)`,

where the normalized pronic norm of `e_(U,V)` tends uniformly to zero. The
unit-pattern remainder has a uniformly bounded pronic norm because `|λ|≤B²`. The two centered small
legs have uniformly vanishing normalized norms by the truncated-pattern theorem.
The centered pole piece has bounded norm, and the actual interior has vanishing
normalized norm. Their exact sum is the interior, so the centered both-large piece
has the opposite smooth term and another uniformly negligible remainder.

The checked smooth-power norm law is
`||n^(1-ε)||_T²/T^β→1/β`. Cauchy–Schwarz bounds every mixed error uniformly,
because the smooth coefficients are bounded. This proves the stated matrix limit.

For any fixed real coefficient vector `w`, the centered packet density is consequently
uniformly asymptotic to
`subHalfZetaCoeff(ε)^2 H_U²H_V²(w_3-w_2)^2/β`.
If `UV→∞`, boundedness and `H_N→0` imply `H_UH_V→0`; hence every moving-cutoff
centered Gram is `o(T^β)` whenever both `T→∞` and `UV→∞`, with no relation between
these two quantities. This includes the product-horizon theorem.

The same parameter choices give every prescribed logarithmic rate for the normalized
prefix error: choose `b` so that `b(1-ε)>4+p`, then `A>bε+p`.
The analogous truncated-pattern estimate follows by the same argument without the
divisor logarithm. The case `p=0`, together with the common finite-head majorant,
first gives a global bound `|A(n)|≤K n^(1-ε)`. Splitting each energy at `√T` then
bounds the early part by `O(T^(β/2))` and the late part by
`O_(ε,p)(T^β/(log T)^(2p))`. This transfers the prefix bounds to every logarithmic
rate for the normalized norm. The smooth-power energy differs from
`T^β/β` by a bounded term, by integral comparison and the summable difference between
`n^(1-2ε)/(n+1)` and `n^(-2ε)`. Thus the uniform Gram error itself is
`O_(ε,p)((log T)^(-p))` for every fixed `p>0`. This remains weaker than a fixed power
of `T`.

## Bounded coefficient schedules

Put `L(w)=Σ_i|w_i|`. The same estimate is uniform in the coefficient vector
after this explicit homogeneous factor is included. If `P_w^c` is the centered
packet, then

`||P_w^c-cH_UH_V(w_3-w_2)n^(1-ε)||_T
 ≤ C_(ε,q)L(w) sqrt(T^β)/(log T)^q`

for every cutoff pair and every real `w`, with a common horizon threshold.
Indeed, the difference is exactly `Σ_i w_i R_i`, where `R_i` are the five
smooth remainders. The finite triangle inequality and scalar norm identity give
the displayed bound. The reverse triangle inequality gives the same bound for
the difference between the packet norm and its explicit smooth norm.
If `w_2=w_3`, the smooth term vanishes identically.

The entrywise uniform Gram estimate also gives

`| ||P_w^c||_T²/T^β - (c²/β)H_U²H_V²(w_3-w_2)² |
 ≤ C_(ε,q)L(w)²/(log T)^q`.

Expand the quadratic form and bound each error entry; the sum of absolute
coefficient products is `L(w)²`. Thus arbitrary bounded moving coefficient
vectors give zero normalized packet norm whenever the horizon and cutoff
product diverge separately. These statements are homogeneous consequences of
the uniform row and Gram laws, with no new analytic premise or power saving.

## Status

Dependency-closed paper proof. Lean formalization remains pending. Source proofs read:
`MoebiusHarmonicArbitraryLogRate.lean`, `DeningerHarmonicPartial.lean`,
`CriticalDivisorAffineMeanSquare.lean`,
`AllDampingVinogradovKorobovBandAndInteriorGrowth.lean`, and
`ReceiverBoundedInTheZeroFreeBandBelowHalfDamping.lean`.
The fixed-cutoff residual-density theorem and uniform truncated-pattern transfer
passed their final direct Lean audits. No fixed power estimate or full Q-I answer
is claimed.

The generalized hyperbola estimate has four audited targets, including the finite
floor-tail swap and divisor-square head bound. Its scratch check passed with only
standard axioms; it is migrated and wired as
`HyperbolaCancellationWithDivisorBoundedCoefficients.lean`. Its producing and final direct repository checks passed. The scratch file was removed.

All seven single-floor targets passed their final direct check and standard-axiom
audits: rounding, the exact omitted Möbius floor tail, a common cutoff estimate,
its unconditional finite logarithmic bound, and the full logarithmic rate through
the unit second cutoff. They are wired as
`UniformLogarithmicCancellationInMobiusFloorSums.lean`; see
[the complete audit](../3-formalized/uniform-logarithmic-cancellation-in-mobius-floor-sums.md).
The owned scratch was removed.

The direct finite proof has ten checked targets in
`UniformCancellationInTheUndampedVaughanConvolution.lean`: the arithmetic-function and summatory Vaughan
identities, exact tail blocks, their signed bound, the full double floor rectangle,
rounding, bound (1), and its unconditional finite logarithmic specialization.
It reuses the checked harmonic bound `|H_U|≤1`. All ten targets passed their scratch
checks with only standard axioms. They are migrated and wired as
`UniformCancellationInTheUndampedVaughanConvolution.lean`; its producing and final
direct repository audits passed.
The full uniform logarithmic rate is checked in `UniformLogarithmicCancellationInTheVaughanConvolution.lean`
using the quarter-power cutoff and the read bound `log_floor_rpow_ge`; its scratch
check passed with standard axioms. It is migrated and wired as
`UniformLogarithmicCancellationInTheVaughanConvolution.lean`; its final direct
check has passed. The undamped theorem is recorded in
`../3-formalized/uniform-undamped-vaughan-convolution-cancellation.md`.
The complete uniform Gram law is now checked below.

The logarithmic hyperbola transfer is checked in `LogarithmicCancellationSurvivesTheDampedFloorTransform.lean`:
the cutoff `floor(n/(log n)^(2(q+5)))` remains above `sqrt(n)` and preserves
`log D ≥ (log n)/2`; the resulting head and tail bounds give every prescribed
logarithmic rate for a divisor-square bounded family. The actual coefficient
fluctuation, discharge of those family hypotheses, and its exact decomposition
of the centered convolution piece are checked as nine targets in
`TheVaughanConvolutionSeparatesItsSmoothMean.lean`. The corrected logarithmic transfer scratch check passed with standard axioms. It is migrated and wired as
`LogarithmicCancellationSurvivesTheDampedFloorTransform.lean`; producing and final
direct repository audits passed. Its scratch file was removed. The actual-family
file passed all nine scratch axiom audits after algebraic and inference fixes.
It is migrated and wired as `TheVaughanConvolutionSeparatesItsSmoothMean.lean`;
its producing and final direct checks passed, and its scratch file was removed.
The completed subtheorem card is
`../3-formalized/vaughan-convolution-mean-and-logarithmic-fluctuation.md`.

`UniformLogarithmicCancellationInTruncatedMobiusReceivers.lean` proves the two corresponding small-leg
targets. Splitting `min(U,n)` at `sqrt(n)` gives uniform logarithmic bounds for
the truncated Möbius partial sums; the general divisor-square transfer then
gives uniform logarithmic bounds for their damped prefixes. Both targets passed
their corrected scratch checks and transitive axiom audits with standard axioms.
They are migrated and wired as
`UniformLogarithmicCancellationInTruncatedMobiusReceivers.lean`; producing and
final direct checks passed. The scratch file was removed; the completed card is
`../3-formalized/uniform-logarithmic-truncated-mobius-receivers.md`.
The subsequent prefix-to-energy transfer
retains a common finite-head bound.

The six generic prefix-to-energy targets passed their corrected scratch checks,
standard-axiom audits, producing check, and final direct repository check.
`UniformLogarithmicEnergyFromPrefixCancellation.lean` absorbs the common finite
head, bounds the split pronic sum, preserves every logarithmic energy and norm
rate, and handles bounded norm families. It is wired; its scratch file was removed.
The completed card is `../3-formalized/uniform-logarithmic-prefix-to-pronic-energy.md`.

That application has five checked targets in
`UniformLogarithmicEnergyInTheVaughanConvolution.lean`: the common linear floor-transform bound,
its actual divisor-majorant specialization, the global smooth-power bound, and
uniform logarithmic pronic norm estimates for both the convolution fluctuation
and the truncated Möbius receivers. The first check found a redundant `ring`
after the preceding rewrite had already closed the identity. It was removed;
the corrected scratch check passed all five targets with only standard axioms.
They are migrated and wired as
`UniformLogarithmicEnergyInTheVaughanConvolution.lean`; producing and final
direct repository checks passed. The scratch was removed. The completed card is
`../3-formalized/uniform-logarithmic-vaughan-convolution-energy.md`.

`LogarithmicEnergySavingsForTheMobiusInterior.lean` proves four unconditional actual-receiver targets.
The read series identity `hasSum_pmPowerDampedRealWeight_div` identifies the mean
with the reciprocal zeta density. Generic logarithmic prefix and energy transfers
then apply to the actual Möbius pattern; subtracting the bounded active increment
gives every logarithmic norm saving for the interior. The first check found an
invalid reverse-definition simplification and an unopened namespace. Both were
fixed. All four corrected scratch targets passed with standard axioms only.
They are migrated and wired as `LogarithmicEnergySavingsForTheMobiusInterior.lean`;
producing and final direct repository checks passed. The scratch was removed.
The completed card is `../3-formalized/logarithmic-energy-savings-for-the-mobius-interior.md`.

`UniformLogarithmicRemaindersInAllVaughanRows.lean` proves six targets assembling all five
rows. The convolution smooth remainder is a bounded unit-pattern correction plus
the actual coefficient fluctuation. The opposite smooth terms cancel exactly in
the five-row sum, so the both-large remainder is bounded by the other four rows
and the interior. Thus all five share every logarithmic norm saving uniformly in
both cutoffs. A reserved-token conflict and a rewrite targeting the wrong
summand were corrected. All six scratch targets now pass Lean with standard
axioms only. The module is migrated and wired as
`UniformLogarithmicRemaindersInAllVaughanRows.lean`; its producing check passed
with the same standard-axiom audits. The final direct repository check passed;
the scratch was removed. The completed card is
`../3-formalized/uniform-logarithmic-remainders-in-all-vaughan-rows.md`.

The finite Gram comparison has three checked targets in
`PronicGramErrorsAroundASmoothRankOneTerm.lean`: a bounded smooth-energy error, a smooth norm
majorant, and the exact three-pairing bound around a rank-one term.
`UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean` proves four targets for the complete
uniform matrix law: every logarithmic rate, its normalized form, arbitrary moving
horizon smooth asymptotics, and zero normalized Gram whenever the horizon and
cutoff product diverge separately. The first finite Gram check passed both
smooth-energy targets but found an unavailable Cauchy–Schwarz reference in the
private pairing adapter. The adapter now uses finite weighted Cauchy–Schwarz
directly, avoiding an import that would shadow the norm throughout this branch.
The corrected three-target scratch check and all transitive axiom audits passed
with standard axioms only. They are migrated and wired as
`PronicGramErrorsAroundASmoothRankOneTerm.lean`; its producing check passed,
and its final direct repository check passed with the same standard axioms.
The scratch was removed; see
`../3-formalized/pronic-gram-errors-around-a-smooth-rank-one-term.md`.
The four complete matrix targets passed their scratch, producing, and final
direct repository checks with only standard transitive axioms. They are wired
as `UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean`; the scratch was
removed. The complete matrix law, including independent divergent horizon and
cutoff-product schedules, is recorded in
`../3-formalized/uniform-vaughan-grams-follow-their-smooth-rank-one-term.md`.
The packet and single-floor laws are checked. The quantitative
Mertens-power consequence remains under verification, so this combined paper
card is not yet fully formalized.

The first logarithmic-transform scratch check found two algebraic Lean issues
(nested inverse normalization and function composition); both were corrected.
The cutoff-bounds theorem passed with standard axioms; the complete transfer
passed its corrected check with standard axioms. No analytic premise was added.

Seven checked targets in `UniformLogarithmicLawsForVaughanSuperpositions.lean` prove the homogeneous
superposition consequences: the exact smooth-remainder sum, the norm
and energy bounds with `L(w)` and `L(w)^2`, the smooth-neutral specialization,
and zero normalized norms for bounded moving coefficients at independent
divergent horizon and cutoff-product scales. Four exact finite centering and
Gram identities are shared with the upper-half branch through
`VaughanPacketGramIdentities.lean`. The four finite identities passed their
producing and final direct checks, with standard transitive axioms only.
The module is wired and its scratch was removed; see
`../3-formalized/vaughan-packet-gram-identities.md`. The seven uniform packet
targets also passed their corrected producing and final direct checks, with
standard transitive axioms only. They are wired as
`UniformLogarithmicLawsForVaughanSuperpositions.lean`; its scratch was removed.
The completed packet card is
`../3-formalized/uniform-logarithmic-laws-for-vaughan-superpositions.md`.
