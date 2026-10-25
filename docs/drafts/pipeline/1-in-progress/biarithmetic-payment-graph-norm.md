# Payment is a complete graph-norm ideal

- **ID:** biarithmetic-payment-graph-norm
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** For every arithmetic row, the critical Wiener kernels whose full cofactor action has finite total pronic energy form the domain of a closed operator and a canonical Banach ideal. The source's origin value is irrelevant. For an absolutely mean-summable source this is exactly its paid ideal. Ambient Wiener closedness is equivalent to a uniform total-energy estimate on all paid kernels.

## The universal pronic action

Let `H` consist of complex rows `w(0)=0` with
`||w||_H^2=sum_(n>=1)|w(n)|^2/[n(n+1)]<infinity`.
Multiplication of each coordinate by `1/sqrt(n(n+1))` identifies it isometrically with
ordinary complex `ell2` on positive integers, so `H` is complete.

For positive integer `j`, set `D_jw(n)=w(floor(n/j))`. The exact pronic fibre mass
`sum_(n=jm)^(jm+j-1)1/[n(n+1)]=1/[j*m(m+1)]` gives
`||D_jw||_H=j^(-1/2)||w||_H`, including complex rows by taking modulus squares.
Also `D_jD_k=D_(jk)`. Therefore the coefficient series
`pi(a)=sum_j a(j)D_j` integrates every critical Wiener kernel to a bounded operator,
with `||pi(a)||<=||a||_W`, and gives a unital algebra representation on `H`.
This is an ordinary pronic module; it is distinct from a normalized escape completion.

For an arbitrary row `v(0)=0`, with no growth premise, define its formal cofactor action

`P_a v(n)=sum_(j<=n) a(j)v(floor(n/j))`.

Every coordinate is a finite sum. The floor-composition identity gives
`P_(a*b)v=P_a(P_bv)` exactly. On `H`, this formal action agrees with `pi(a)`: finite
Wiener truncations converge in operator norm, and each coordinate of the finite sum
stabilizes. Coordinate evaluation is continuous in both the Wiener and pronic norms.

The zero-origin condition on the source row can be removed. For every summation
index `1<=j<=n`, one has `floor(n/j)>=1`; at `n=0` the sum is empty.
Consequently no cofactor coordinate reads `v(0)`, and the output always has
zero origin. Replacing the source's origin by zero leaves its entire cofactor
action and graph domain unchanged. The formal construction exposes this slight
strengthening; the finite-index observation proves it independently on paper.
It is an elementary extension of the same construction, not a separate
originality claim.

## Closed graph and Banach ideal

Define `D_v={a in W : P_a v belongs to H}` and `T_v a=P_a v`.
Its graph is closed in `W x H`. Indeed, if `a_i->a` in Wiener norm and
`T_v a_i->w` in `H`, continuity of each finite coordinate gives
`w(n)=P_a v(n)` for every `n`. Thus `a` belongs to the domain and `T_v a=w`.
Equivalently the graph is the intersection, over positive `n`, of the closed kernels
of the continuous linear maps `(a,w)->w(n)-P_a v(n)`.

Equip the domain with

`||a||_(D_v)=||a||_W+||P_a v||_H`.

A Cauchy sequence converges in both complete factors, and graph closedness identifies
its limit. Hence this norm is complete. The composition law and the operator bound give,
for every `a in W` and `b in D_v`,

`||a*b||_(D_v)<=||a||_W ||b||_(D_v)`.

Thus `D_v` is a Banach ideal, continuously embedded in `W`, even when its image is not
closed in the ambient Wiener norm. No closedness of that image is inferred from graph
completeness.

## Identification with the actual paid ideal

Take `v=A_c`, where `c` is a real source with absolutely convergent mean `m_c`.
The exact source convolution law gives, componentwise for complex kernels,

`A_(a*c)=P_a A_c+m_c A_a`.

Every critical Wiener kernel has a uniformly bounded receiver norm; monotonicity of
the nonnegative energy sums identifies that bound with membership in `H`.
Consequently `A_(a*c)` belongs to `H` exactly when `P_a A_c` does. Requiring this for
the real and imaginary parts is precisely AOT's `paidIdeal c`. Thus the construction
supplies a canonical complete norm on the actual paid ideal without assuming that
payment is closed in Wiener norm or that paid finite truncations are dense.

The image is Wiener closed exactly when there is a constant `C` such that
`||P_a A_c||_H<=C||a||_W` for every paid kernel `a`. If the image is closed, it is a
Banach subspace of `W`; its closed operator into `H` is bounded by the closed graph
theorem. Conversely such a bound makes every Wiener-Cauchy sequence of paid kernels
Cauchy in graph norm, so completeness puts its Wiener limit back in the ideal.
This identifies the exact missing uniform estimate behind any closedness assertion.

## The critical one-prime domain has a concrete core

At the critical prime-five tower, write `g_r=f(5^r)5^(-r/2)` and
`S_l=sum_(r<=l)g_r`. The exact digit-energy comparison makes the graph norm equivalent
to `||g||_ell1+||S||_ell2`. For a paid sequence, `S_l->0`, so its total sum is zero.
Define the corrected finite approximation by keeping `g_r` for `r<M`, replacing
`g_M` by `g_M-S_M`, and setting all later coefficients to zero. Its partial sums agree
with `S_l` for `l<M` and vanish thereafter. Hence its graph-norm distance tends to zero:
the partial-sum error is exactly the `ell2` tail, while its `ell1` error is at most twice
the original coefficient tail. Finite multiples of the repairing Euler factor therefore
form a graph-norm core in this one-prime domain.

For the explicit unpaid boundary kernel with `S_l=-1/sqrt(l+1)`, these same corrected
finite kernels remain Wiener bounded and converge in Wiener norm, but their squared
receiver norms grow comparably to the harmonic partial sums. This is a quantitative
witness to the failure of the uniform estimate above. It supplies a positive complete
space and a dense finite core alongside the nonclosedness obstruction.

## Scope and verification

Closed graph norms and the closed graph theorem are classical. The proposed programme
use is the canonical actual-payment ideal, its precise uniform-bound criterion, and the
critical digit-domain comparison. This construction supplies neither a vanishing theorem
nor an arithmetic orientation estimate, and does not make the ambient quotient Hausdorff.

- [x] Dependency-closed paper construction and source comparison.
- [x] Paper critical-domain core and quantitative failure of ambient closedness.
- [ ] Lean universal pronic module, closed graph, and Banach ideal.
- [ ] Lean source comparison and critical finite-core theorem.
- [ ] Direct checks, axiom audits, and umbrella imports.

Corpus reuse audit: `ArithmeticOrientationTheory/WienerCoefficientEvaluation.lean`
provides the actual continuous coefficient functional `coefficientLinear` and
its weighted norm bound. `HTGeometry/FokasLenellsRawComplexGraph.lean` supplies
the checked pattern for a closed graph submodule, its inherited complete norm,
and continuous input/output projections. No generic payment-graph result was
returned by the dedicated corpus query. The pronic Hilbert search returned
general `lp` norm and matrix constructions, not an existing universal pronic
payment graph. The graph's coordinates can therefore be defined directly in
`W_(1/2) x lp(C,2)` by the finite cofactor formula divided by the square root
of the pronic weight; closedness is a countable intersection of coordinate
equalizers. This graph construction is now formalized; its source comparison
and Wiener ideal action remain separate pending leaves.

For the critical closure, `HTGeometry/ConstraintMotiveRelativity/PrimeAugmentationCompletion.lean`
already proves `closure_image_augIdeal_one`: finite zero-sum vectors are dense
in the kernel of the sum functional in `ell1`, for arbitrary coordinate types.
Its statement and proof were inspected. The actual source comparison and the
square-partial-sum domain still require their own proofs; the abstract density
theorem does not supply them.

The formalized graph inherits the product's maximum norm. It is equivalent
to the displayed sum norm, since `max(x,y)<=x+y<=2*max(x,y)` for nonnegative
`x,y`. Thus the checked construction must distinguish which norm is literally
defined from the equivalent sum norm used in the paper estimates. No Lean
claim of the ideal-action estimate is made yet.

The total-energy corpus search returned the digit-specific criterion and
ADR's monotone finite-energy limit theorem, not the general positive-cell
summability interface needed here. The latter is formalized separately as
`PronicEnergyDomain`, with its direct source check and four audits passed;
`PaidGraphIdentification` then uses the checked actual
cofactor/payment equivalence on both complex components. Its scratch check and
both transitive audits passed; the wired production source awaits its direct
repository check. This source identification uses every Wiener coefficient, with
no tower-support restriction and no presumed closedness of payment.

The closed graph, completeness, input injectivity, and exact energy-domain
identification passed the five audits and direct source check in
`CofactorGraphDomain`; its [stage-3 card](../3-formalized/biarithmetic-complete-cofactor-graph.md)
records the exact scope. The ambient closedness criterion is drafted in
`/tmp/BiarithmeticCofactorGraphClosedness.lean`. Corpus search found a Hilbert-space
bounded-below criterion, which does not apply to the Wiener Banach domain.
Mathlib's Banach theorem
`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective` applies
directly instead. For the maximum graph norm, output bound `C` gives inverse
bound `max(1,C)`, and any inverse bound controls the output. This supplies
exactly the paper criterion without imposing a Hilbert structure on the Wiener
algebra. Its first check exposed an unloaded nonnegative-real notation; the
explicit `NNReal` carrier repairs that elaboration error. Recheck remains pending.

## Exact finite-core errors

For complex coefficients `g`, let `S_M=sum_(r<=M)g_r` and define
`g^[N]_r=1_(r<=N)g_r-1_(r=N)S_N`. Its partial sums equal `S_M` for
`M<N` and zero for `M>=N`. Its coefficient error is zero below `N`,
`-S_N` at `N`, and `-g_r` above `N`. Therefore, for every `g in ell1`,

`||g^[N]-g||_1=|S_N|+sum_(r>N)|g_r| -> |sum_r g_r|`.

This is an equality, strengthening the earlier upper bound. If additionally
`S in ell2`, the squared partial-sum error is exactly
`sum_(M>=N)|S_M|^2`, which tends to zero. Since square summability also
forces `sum g=0`, the same approximants converge in the graph norm.
The proof is the displayed pointwise partition plus convergence of the two
nonnegative series. The dedicated finite-core corpus query returned generic
tail estimates and other graph cores, but no exact partial-sum core theorem.
No external originality is claimed for this elementary sequence result.

`CriticalPartialSumCore` passed its direct repository check and all seven
audits. Its [formalized card](../3-formalized/biarithmetic-critical-partial-sum-core.md)
records the exact finite-core result and its scope.

## Reusable completed block operators

The further corpus search found `HTGeometry/PositiveIntegerBlockOperators.lean`.
Its `PNatBlock.divBlockOp` already constructs bounded floor-block operators on
complex `ell2` indexed by positive integers. The checked statements
`norm_sq_divBlockOp`, `norm_divBlockOp_le`, `divBlockOp_comp`, and
`norm_sq_divBlockOp_single` supply the norm, composition, and sharpness interfaces.
The pronic specialization uses

`w_j(n)=sqrt(((floor(n/j))*(floor(n/j)+1))/(n*(n+1)))`.

This weight is at most one. At every positive quotient `m`, its squared block
mass is exactly `1/j`, by the public theorem
`sum_Icc_pronic_dilation_fibre` in
`ArithmeticContinuationAndCriticalEnergy/TheDilationSelfSimilarityOfThePronicMeasure.lean`.
Thus the existing operator is exactly normalized pronic dilation, with squared
norm `(1/j)||f||^2`; its composition formula reduces to cancellation of the
middle weight. This reuses the completed operator infrastructure. The pronic
specialization and its integrated Wiener action are now formalized in
`PronicDilationOperators`, with a direct check and six clean audits;
the [stage-3 card](../3-formalized/biarithmetic-completed-pronic-dilations.md)
records its ordinary-energy scope.

The subsequent coordinate audit found the existing real identity
`RHTower.floorTransform_comp` in `RHTower/FloorTransformHarmonicInverse.lean`:
finite floor transforms compose by Dirichlet convolution for every input row.
Its proof explicitly identifies the two hyperbola index sets, so no analytic
interchange is involved. The complex actual-Wiener coordinate bridge remains
to be checked. `HTGeometry/FramePurificationPartialTrace.lean` and
`RHTower/Deninger/DeningerArithmeticPositiveCalderonKoszul.lean` confirm the
operator-evaluation interface `ContinuousLinearMap.apply` with `HasSum.mapL`.
`PronicWienerCoordinates` uses those existing maps: after
evaluation at cell `n`, every scale `j>n` vanishes because the row's origin is
zero, leaving exactly the finite cofactor formula.
Its scratch check and both transitive audits passed. The production source is
wired and awaits its direct repository check.

The two indexing conventions already have an exact corpus isometry:
`HTGeometry.lpDomCongr` in `HTGeometry/LatticeL2Shift.lean`, specialized to
`Equiv.pnatEquivNat` and exponent two. Its source and application formula were
inspected, and its dependency olean exists. This identifies the graph draft's
natural-index coordinates with the positive-index block-operator space without
constructing another completed carrier or changing the graph norm.

## Finite extension proves formal composition without growth assumptions

There is also a direct bridge from the completed representation to arbitrary
formal source rows. Fix a horizon `N` and prescribe `v(m)` for `1<=m<=N`.
The normalized row `v(m)/sqrt(m(m+1))` on those cells, zero elsewhere, is a
finite-support vector of the completed pronic space. Its unnormalized row agrees
with `v` throughout that horizon. Every cofactor coordinate at `n<=N` reads only
positive indices at most `n`, so the integrated Wiener action agrees there with
the formal cofactor transform of `v`.

Apply this twice at horizon `N`. The representation law gives
`pi(a)pi(b)=pi(a*b)`. The finite coordinate formula on both sides therefore gives
`P_a(P_bv)(N)=P_(a*b)v(N)` for every source row, with no growth premise. Since `N`
was arbitrary, this proves the full formal composition law. It uses a finite
extension separately at each horizon; it does not assert that the original
source belongs to the completed pronic space.

For a graph member `(b,w)` with `w=P_bv`, the same finite coordinate identity
shows that `(a*b,pi(a)w)` belongs to the graph. The two norm estimates in the
complete factors then give the graph-ideal bound for either the maximum norm
or the equivalent sum norm. This supplies a route to the Banach ideal action
without duplicating the existing hyperbola-reindexing proof for complex rows.
