# The one-prime payment complex has an exact Fredholm phase transition

- **ID:** biarithmetic-one-prime-payment-fredholm-phase
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md)
- **Statement:** For the geometric source `I_a`, `0<a<5`, restrict kernels to powers of five and give its paid ideal the source graph norm. Its inclusion into the critical Wiener algebra is Fredholm of index zero when `a<sqrt(5)`, Fredholm of index minus one when `a>sqrt(5)`, and non-Fredholm at equality. At equality its reduced cokernel is isometrically `C`, but its unreduced cokernel has Hamel dimension continuum.

## Canonical complex and its domain

Normalize one-prime kernel coefficients by `g_r=5^(-r/2)f(5^r)`, identifying the
critical Wiener algebra with `W=ell1(N,C)`. Put `q=a/sqrt(5)>0` and

`T_q g(m)=sum_(r<=m) q^(m-r)g_r`.

The exact source payment criterion on the digital-energy card is
`P_q={g in W:T_q g in ell2}`. Thus this is a source-derived domain, not a prescribed
annihilator. Its norm `||g||_1+||T_q g||_2` is equivalent to the canonical receiver
graph norm by the proved paper digit norm equivalence and the nonzero factor
`a/(5-a)`. The graph is closed: convergence in `ell1` fixes every finite partial
sum coordinate, while convergence in `ell2` fixes the output coordinate. Hence
`P_q` with this graph norm is Banach.

Take the two-term complex `P_q --J_q--> W`, where `J_q` is inclusion. It is bounded
and injective. Its algebraic cokernel records unpaid kernels, its quotient topology
records whether payment is closed, and its reduced cokernel is `W/closure(P_q)`.

## Subcritical and strict regimes

If `0<q<1`, the operator is causal convolution with `(q^m)_m`. Its `ell1` norm
is at most `||g||_1/(1-q)`, by summing the nonnegative absolute majorant. Since
`ell1` embeds continuously in `ell2`, every kernel is paid and
`||T_q g||_2<=||g||_1/(1-q)`. The graph norm is equivalent to the Wiener norm,
so `J_q` is a Banach isomorphism and its Fredholm index is zero.

If `q>1`, payment is exactly the zero-evaluation condition
`E_q(g)=sum_r q^(-r)g_r=0`. Necessity follows from
`q^(-m)T_q g(m)->0` for an `ell2` output and convergence of the coefficient sum.
For sufficiency, zero evaluation gives the exact future-tail formula

`T_q g(m)=-sum_(s>=1) q^(-s)g_(m+s)`.

Nonnegative double summation yields
`sum_m |T_q g(m)|<=||g||_1/(q-1)`. In particular the output belongs to `ell2`.
The functional `E_q` is continuous, has norm one, and takes `delta_0` to one.
Thus `P_q=ker E_q` is closed of codimension one. The same tail estimate proves
equivalence of its graph and Wiener norms. The kernel of `J_q` is zero, its
cokernel has dimension one, and its Fredholm index is minus one.

## Critical contact and continuous duality

At `q=1`, `T_q g` is the ordinary coefficient partial-sum sequence. The critical
closure-defect card proposes that `P_1` is dense and proper in
`Z={g:sum_r g_r=0}`, with `dim_C(Z/P_1)=continuum`. Its range is not closed,
so `J_1` is not Fredholm. The exact sequence
`0 -> Z/P_1 -> W/P_1 -> C -> 0` and the ambient cardinality upper bound give
`dim_C(W/P_1)=continuum` as well.

The reduced cokernel is nevertheless isometrically `C`: the sum functional gives
the lower quotient-norm bound `|sum g|<=||g+z||_1` for every `z in Z`, while the
representative `(sum g)delta_0` gives equality. Every continuous functional on
the unreduced cokernel factors through this reduction, since it vanishes on the
closure of zero. Its continuous dual is therefore one-dimensional. This is an
exact continuous pairing, whereas algebraic duality also sees the continuum
of unpaid classes inside that closure.

## Actual golden transfer and limits of the construction

For the ordinary-floor golden source, the checked paid-ideal reduction identifies
these domains at `a=goldenPrimaryRoot*t`. Adding the paid remainder and multiplying
by a nonzero scalar also give equivalent source graph norms: bounded Wiener action
on the remainder bounds the change in receiver norm in both directions. Hence
the same Fredholm classification holds for `0<t<=1`.

For the intrinsic norm-lattice receiver it holds for `0<t<1`. Below threshold,
its exact factored series is a polynomial times geometric factors with ratios
`1`, `a`, and `b`, all strictly below `sqrt(5)`. Its coefficients are therefore
absolutely summable at radius `1/sqrt(5)`, so the receiver and every critical
Wiener action are paid. At and above threshold, its primary geometric coefficient
is nonzero and its remainder is paid, giving the same graph-domain comparison.
At `t=1` the intrinsic response is constant and paid, so that endpoint has index
zero instead. Neither construction identifies kernels with individually labelled
generalized primes before norm aggregation.

This is a precise payment complex and index calibration, not a sheaf construction,
Mayer--Vietoris theorem, curve-cohomology comparison, or arithmetic Riemann--Roch.
The real degree/torsion invariant remains separate. No general novelty claim is
made for closed graph norms or Fredholm index.

- [x] Dependency-closed paper source domain and graph completeness.
- [x] Proof plans recorded for quantitative bounds, all three phases, and critical reduced duality.
- [ ] Lean source payment criterion and graph-norm construction.
- [ ] Lean Fredholm classification and exact reduced/unreduced cokernel comparison.
- [ ] Direct source checks, transitive axiom audits, and umbrella imports.

## Corpus audit for division and the tail estimate

Dedicated searches found the actual local-factor unit classification in
`ArithmeticOrientationTheory/LocalFactorsAreTheUnitsOfTheWienerMonoid.lean`,
general discrete convolution bounds, and the `ell2` backward-shift contraction
in `HTGeometry/ConstitutiveToeplitzDefectIndex.lean`. Their relevant source
statements were inspected. No one-prime Wiener division theorem identifying
the interior evaluation kernel with the principal Euler-factor ideal was returned.
The existing unit law covers only `|a|<sqrt(p)` and does not prove the strict
escaping phase.

The direct future-tail estimate can be obtained from the summable nonnegative
product `|g_r| b^(s+1)`, `b=1/q<1`. The injection
`(m,s)->(m+s+1,s)` gives joint summability of
`|g_(m+s+1)|b^(s+1)`. Reordering this nonnegative series and bounding each
coefficient tail by `||g||_1` gives the exact operator bound
`b/(1-b)||g||_1=||g||_1/(q-1)`. This is the missing formal analytic estimate;
it introduces no additional source hypothesis beyond the Wiener norm.

The same absolutely convergent tail satisfies
`B_b g(m)=b*g_(m+1)+b*B_b g(m+1)`. If `E_q(g)=0`, splitting its
series at zero gives `-B_b g(0)=g_0`. The negative tail therefore satisfies
the same initial value and recurrence as `T_q g`, since `q=1/b`:
`-B_b g(m+1)=q*(-B_b g(m))+g_(m+1)`. Induction gives the future-tail
formula without a separate rescaling and reindexing of each infinite tail.
`GeometricFutureTail` proves the recurrence together with the norm bound.
Its direct source check and all four axiom audits passed; the
[stage-3 card](../3-formalized/biarithmetic-geometric-future-tail.md) records
the scope. The source comparison and Fredholm conclusion remain pending in Lean.

The dependent `/tmp/BiarithmeticGeometricCausalDivision.lean` now drafts the
full complex sequence-domain equivalence. For necessity, square summability
makes the causal response tend to zero, while its product with `b^M` is
exactly the `M`th partial sum of the reciprocal evaluation. That product
tends to zero and the absolutely convergent evaluation therefore vanishes.
For sufficiency, the recurrence identifies the response with the negative
future tail; its proved paper absolute-sum bound implies square summability.
The draft includes the explicit norm bound and is unchecked. Actual source
transfer, bounded evaluation maps, and the Fredholm cokernel still need Lean
construction; the sequence-domain theorem alone does not discharge them.

The exact source transfer is drafted separately as `StrictPrimePayment`.
For `q=a/sqrt(5)` and lifted coefficients `f_r=sqrt(5)^r g_r`, the finite
pole sum is `sum_(r<=M)g_r/q^r`; multiplication by `q^M` is the causal
response. Since `q^2=a^2/5`, its norm square is exactly the checked source
payment summand. Thus above threshold the source criterion becomes
`sum_r (sqrt(5)/a)^r g_r=0`. Applying the existing actual golden ideal
identity replaces `a` by `alpha*t`. This normalization introduces no
comparison constants or additional summability premise. The new draft is
unchecked; its bounded cokernel and Fredholm packaging remain separate.

## Critical closure and reduced cokernel formalization

The additional corpus audit found the existing continuous augmentation,
its surjectivity, and its one-dimensional annihilator theorem in
`HTGeometry/ConstraintMotiveRelativity/PrimeAugmentationCompletion.lean`.
`CriticalCoefficientDomain` reuses that functional on actual complex `ell1`,
packages square-summable partial sums as a submodule, and drafts its exact
closure using `CriticalPartialSumCore`. It also drafts the attained minimum
distance to the zero-evaluation hyperplane and the continuous annihilator
classification. The file `/tmp/BiarithmeticCriticalCoefficientDomain.lean`
awaits its first Lean check; five audits are included.

`/tmp/BiarithmeticCriticalReducedCokernel.lean` drafts the exact quotient norm,
the quotient's linear isometry with `C`, and its dimension one. Its quotient
denominator is the closure of the coefficient payment domain, identified
with the augmentation kernel by the preceding leaf. The four audit targets
remain unchecked. These are obligations, not established cokernel results.

`/tmp/BiarithmeticCriticalCoefficientWienerRealization.lean` drafts the
actual source bridge for that coefficient space: a complex linear isometry,
normalized coefficient restriction for every Wiener kernel, both inverse
identities on the prime-five support, the exact range classification, and
the pullback of the actual critical golden paid ideal. Summability of the
restricted coordinates follows from AOT's actual `summable_norm` theorem
and injectivity of the five-power map. Six audits are drafted; no result
from this file is established yet.

`/tmp/BiarithmeticSubcriticalCausalBound.lean` drafts the complementary
subcritical analytic estimate, including `q=0`. The complex response norm
is dominated by the finite nonnegative convolution of coefficient norms.
The checked `finiteGeometricConvolution_sum` identity leaves a nonnegative
endpoint term, so every partial absolute sum is at most `||g||_1/(1-q)`.
Monotone series convergence yields the full absolute-sum bound, hence
square summability. Four audits drafted; unchecked. The Banach graph,
bounded evaluation maps, and Fredholm packaging still require Lean proofs.

`/tmp/BiarithmeticGeometricCoefficientDomain.lean` drafts the common complex
coefficient submodule, its full subcritical domain and exact critical
specialization, and the strict closed evaluation hyperplane. The reciprocal
evaluation has norm exactly one and an explicit section `z -> z*delta_0`.
Six audits drafted; unchecked. The corpus provides the general partial-map
Fredholm interface and index-minus-one theorem in
`HTGeometry/UnboundedFredholm.lean`; its statements and source were inspected.
The other bounded Fredholm interface requires Hilbert spaces, so it is not
silently applied to the `ell1` coefficient space. Graph completeness and
the actual source comparison remain required in addition to the index claim.

`/tmp/BiarithmeticCriticalCoefficientNonclosed.lean` drafts the critical
nonclosed-range input in actual complex `ell1`. It embeds the checked real
inverse-square-root-tail differences, preserving their exact norm two and
zero total evaluation. Their complex partial-sum squares remain the
divergent harmonic sequence. The checked finite-core mechanism supplies
convergent paid approximants. Four audits drafted; unchecked.

`/tmp/BiarithmeticGeometricCoefficientFredholm.lean` drafts the index part
using that existing partial-map interface. The operator is the identity
restricted to the actual causal square-energy submodule. Its kernel is
zero and its range is precisely that submodule. Subcritical range is all
of `ell1`; strict range is the kernel of a surjective continuous scalar
evaluation; critical range is not closed. These laws yield the proposed
indices and the exact Fredholm locus `q>=0, q!=1`. Seven audits drafted;
unchecked. This does not yet assert the full bounded graph-inclusion
comparison with ordinary or intrinsic source norms.

`/tmp/BiarithmeticGeometricCoefficientGraph.lean` drafts the complete Banach
domain itself as the coordinate-equality submodule of `ell1 x ell2`. Every
response coordinate is a finite continuous coefficient functional, so
the graph is closed. Its input is bounded and injective, with image
exactly the causal payment domain and a unique square-summable output.
Five audits drafted; unchecked. The inherited norm is the maximum of
input and output norms; the paper sum norm is equivalent but is not the
literal Lean definition. Quantitative comparison and actual-source graph
calibration still remain to be formalized.

`/tmp/BiarithmeticGeometricGraphNormBounds.lean` drafts the quantitative
norm comparison. The corpus's `FormationDepthBaireCategoryEscape` proves
the elementary `ell1`-to-`ell2` norm estimate through finite square sums;
the same inspected finite-sum argument is applied directly to the actual
causal output coordinates here. The output bounds are
`||g||_1/(1-q)` below criticality and `b/(1-b)||g||_1` at ratio `q=1/b>1`.
Together with the maximum graph norm, these give both norm-comparison
constants explicitly. Five audits drafted; unchecked. The ordinary and
intrinsic source graph calibrations remain separate obligations.
