# Renormalized intersection theory of arithmetic counts

Arithmetic-count programme associated with [review 0811](../../../docs/reports/review-0811/obstacles-summary.md).
Namespace: `GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts`.
Companions: [effective scaling geometry](../EffectiveScalingGeometry/README.md)
and [height and homotopy](../HeightHomotopyArithmeticCounts/README.md).
The existing [renormalized intersection theory](../RenormalizedIntersectionTheory/README.md)
owns its Hodge and scattering constructions; this programme owns arithmetic
counts, critical torsion compensation and completed prime topology.

## Mathematical objective

The governing target is **signed cancellation of the actual local indices at
the square-root scale**. For `S(N)=Σ_p index_p(N)=1−M(N)`, the RH-scale
target is `S(N)=Oε(N^(1/2+ε))` for every `ε>0`; a literal `O(√N)` bound
is stronger and is not silently assumed. Counts, product-formula heights
and completed invariants must supply an independently proved mechanism
controlling this signed sum. Quadratic scaling, local index formulas and
positive absolute counts alone do not meet that target.

Construct an arithmetic count on integer Hecke correspondences independently
of the Weil form `Q`, with quadratic Tate coefficient `Q`. Its geometric
source should be a surface Riemann–Roch theorem, product formula or signed
localization. Reach the critical conductor weight and retain dependence on
the complex parameter. Neither a reformulation of positivity nor an assumed
height is a construction.

An integer-valued Euler characteristic can be negative. A quadratic
Riemann–Roch identity alone therefore supplies no sign: one must prove a
nonnegative count, or a subquadratic bound on the negative cohomological
contribution, independently of `Q`.

## Five construction problems

| Construction | Exact target | First discriminating test |
|---|---|---|
| Surface count | Integer-valued count on correspondences, quadratic under scaling, full-rank Tate coefficient `Q` | Recover curve counts; distinguish probes with identical two degrees |
| Critical torsion | Compensate `L(m,n)=−P(m,n)+[m=n]d(n)` at weight `δ=0` using an independently defined archimedean contribution | Exact prime-star compensation budget; then all conductor interactions |
| Completed topology | An `s`-dependent completion with a proved zero-detection comparison | Determine domains, boundedness of the prime-two contraction and whether the Dirichlet gauge extends |
| Relative localization | A natural pair and signed local indices recovering `M(N)` with an explicit Euler convention | Preserve the isolated-prime correction; no arbitrary attachment chosen from `M(N)` |
| Modular cells | Arithmetic comparison between prime faces and Farey/horocycle cells carrying the modular action | Prove cutoff compatibility or quantify the boundary term |

## Established inputs and normalization

HHAC constructs the actual torsion forms on `Hδ=ℓ²(n^δ)` for every `δ>0`.
The raw forms are positive. Subtracting their divergent self-energy gives a
compact self-adjoint limit `L`; equal prime-pair vectors eventually have
negative energy. The mixed prime row fails square summability at `δ=0`.
These facts do not supply a positive critical count.

ESG classifies ordinary and prime-weighted finite-cutoff homology, including
its actual persistence maps. The [ordinary Dirichlet-weighted chain gauge](../EffectiveScalingGeometry/DirichletPersistenceEquivalence.lean)
makes that persistence independent of `s`. Merely renaming these groups as
completed cohomology would retain the obstruction.

Write `P_N=#{p prime : N/2<p≤N}`. The existing Lean convention is

`E(core)=Σ_faces (−1)^card = M(N)+P_N`.

For `N≥4`, reduced topological Euler characteristic is `−M(N)−P_N`; ordinary Euler
characteristic is `1−M(N)−P_N`. The report calls `E(core)` an Euler
characteristic without this sign convention. Any relative construction must
specify which invariant it recovers. Deleting isolated primes alone does not
remove their arithmetic correction.

## First formalized classification

[Prime-star compensation](../../../docs/drafts/pipeline/3-formalized/riac-prime-star-compensation.md)
classifies the actual corrected torsion matrix on conductor one and primes.
For arbitrary real central diagonal `a` and prime diagonals `D(p)`, positivity
on every finite prime set is equivalent to

`D(p)>0 for every p`, `Σ_p (log p)²/(p D(p))<∞`, and `Σ_p (log p)²/(p D(p))≤a`.

The sum is the exact least payment. Divergence gives explicit finite negative
probes. Any eventual bound `D(p)≤C(log p)²` excludes finite central payment.
For `D(p)=d(p)+p^η`, a positive completion exists exactly for `η>0`.
Here `η` measures added diagonal growth, distinct from the Hilbert weight `δ`.
[PrimeStarCompensation.lean](PrimeStarCompensation.lean) proves the matrix
comparison, classification, minimizing probes and both boundaries.

[LogarithmicStarCompensation.lean](LogarithmicStarCompensation.lean) sharpens
the growth scale: for `D(p)=d(p)+(log p)^α`, finite compensation exists exactly
when `α>2`. The same series gives the least payment; at every `α≤2`, each
central budget has an explicit finite negative probe. Prime-density
summability supplies the full positive range, including exponents where
comparison with all integers would fail. Both classifications are formalized.

The positive survivor is an explicit minimal completion of the prime-star
restriction. Composite interactions and nonlocal archimedean corrections
remain separate; no integer count or full positive form follows.

[Programme card](../../../docs/drafts/pipeline/1-in-progress/renormalized-intersection-arithmetic-counts.md)
records the remaining mathematical targets.

## Completed prime boundary

[CompletedPrimeBoundary.lean](CompletedPrimeBoundary.lean) retains the actual
finite boundary `d_s a=Σ_p p^(−s)a_p` and squared conductor norm
`Σ_p p^δ |a_p|²`. Its normalized embedding in prime `ℓ²` is injective and dense.
For every real `δ`, a bounded extension exists exactly when

`2 Re(s)+δ>1`.

Existence of any closed partial linear extension preserving all finite chains
has the same exact range. In that range the bounded extension is unique,
explicitly a Riesz functional, with squared norm `Σ_p p^(−2 Re(s)−δ)`.
Outside it, finite chains have boundary one with arbitrarily small norm;
`(0,1)` belongs to graph closure, ruling out every closed linear extension.
The formalization retains the exact gauge, finite-chain comparison and norm
identity.

At `δ=0`, the original augmentation therefore cannot survive as a closed
operator on or left of the critical line in this Hilbert model. The positive
survivor is its exact extension classification, norm and explicit packets.
Higher-degree contraction is a separate [construction problem](../../../docs/drafts/pipeline/0-backlog/riac-completed-prime-koszul.md).
No completed homology or zero-detection theorem is asserted.

## Vertical unitary equivalence

[UnitaryPrimeChainGauge.lean](UnitaryPrimeChainGauge.lean) completes every
actual prime exterior degree with squared face weight `∏_(p∈S)p^δ`.
The finite-chain embedding is faithful and dense. Imaginary Dirichlet gauges
extend to explicit unitaries, intertwining the original adjacent-degree
boundaries. These unitaries transport the finite boundary graphs and their
closures exactly along vertical lines, even when those closures are not
operators. Up to this explicit equivalence, the closed relation depends
only on `Re(s)`.

Thus these diagonal Hilbert completions alone cannot distinguish imaginary
zero locations through unitary invariants. The positive survivor is their
exact norm and graph classification. Additional arithmetic structure and a
zero-detection comparison remain necessary.

The [critical exterior theorem](../../../docs/drafts/pipeline/3-formalized/riac-critical-exterior-graph-closure.md)
identifies the closed relation itself: when `2 Re(s)+δ≤1`, the graph on all
finite-support chains is dense in `H_(k+1)×H_k` for every exterior degree,
including the augmented degree. Appending a large prime to a fixed face
forces each continuous graph annihilator to vanish, by square summability
of Hilbert observations and divergence of the prime coefficient squares.
Thus these critical graph closures retain no boundary constraint. This
concerns the union of conductor cutoffs; each fixed finite cutoff remains
finite dimensional. It supplies no signed local-index upper bound.

## Actual prime-vertex dynamics and exit pairs

[PrimeVertexDynamics.lean](PrimeVertexDynamics.lean) constructs
`F(x)_p=(p+1)x_p/Σ_q(q+1)x_q` on the original prime-product complex.
It preserves every face and cutoff, is explicitly homotopic to identity,
and fixes exactly the arithmetic prime vertices.

[PrimeVertexLocalFlow.lean](PrimeVertexLocalFlow.lean) identifies each open
vertex star with its actual nonnegative link cone. Logarithmic diagonal
flow has an explicit compact isolating block, compact exit and radial
block contraction. The exit deformation retracts onto the upper-link
realization. [PrimeVertexSingularIndex.lean](PrimeVertexSingularIndex.lean) defines the local
integer by relative singular homology of this block and exit. For `p≤N≤p³`,
it proves `index_p(N)=1−#{q>p prime : pq≤N}` in the full ambient realization.
Bertrand intervals prove these actual local indices are unbounded below.
The constructions, singular-homology comparison in this range and axiom audits
are complete; see the [formalized result](../../../docs/drafts/pipeline/3-formalized/riac-prime-vertex-exit-indices.md).
[PrimeVertexSignedLocalization.lean](PrimeVertexSignedLocalization.lean) proves the
all-cutoff comparison with the independently defined upper-face count, finite dimensionality
of every rational local relative homology group and exact time-one conjugacy with `F`.
For `N≥1`, the actual local indices satisfy

`Σ_p index_p(N)=1−M(N)`.

For `N≥4`, the core sum is `1−M(N)−P_N`: every removed upper-half prime
has index one. The [singular-homology bridge](../HodgeTheoryWithoutVarieties/FiniteFaceSingularEuler.lean)
proves the alternating face formula by an actual open good cover and relative
excision. No homology finiteness or index comparison is assumed.
The [full localization theorem](../../../docs/drafts/pipeline/3-formalized/riac-prime-vertex-signed-localization.md)
is formalized. [PrimeExitBouquet.lean](PrimeExitBouquet.lean) also classifies every actual exit:
it is empty, or is homotopy equivalent to a finite sphere bouquet. With least
upper neighbour `a`, the sphere labels are prime supports `S` with all `q>a`
and `p·∏S≤N<p·a·∏S`; their dimensions are `|S|−1`. This
[classification](../../../docs/drafts/pipeline/3-formalized/riac-prime-exit-bouquet.md)
is formalized. Quantitative cancellation and a canonical relative pair on the
connected core with Euler number `M(N)` remain separate.

## An integer residue count for the signed local-index sum

[IntegerGluingCounts.lean](IntegerGluingCounts.lean) constructs an actual
integer relation quotient. On generators `e_1,…,e_N`, impose the divisor
relations `Σ_(d|j)e_d=0` for `2≤j≤N`, together with
`Σ_(2≤j≤N)e_j=0`. The presentation uses integer divisibility alone.
Orient the final relation negatively and call its matrix `R_N`.

For `S(N)=Σ_p index_p(N)=1−M(N)`, the [formalized construction](../../../docs/drafts/pipeline/3-formalized/riac-integer-gluing-count.md)
proves

`G_N ≃ₗ[ℤ] ZMod |S(N)|`, `det R_N=S(N)`.

Integral Möbius inversion leaves one relation column. The residue map
`v↦(Uv)_1 mod S(N)` is surjective, and an explicit integral preimage
proves its kernel equals the relation lattice. Thus the group structure
is established independently of the determinant calculation.

The quotient is finite exactly when `S(N)≠0`, with actual cardinality
`C_N=|S(N)|`. When `S(N)=0`, it is infinite cyclic; the Lean convention
`Nat.card=0` does not denote an empty finite group. The finite quotient's
primary factors are `ℤ/p^(v_p(C_N))ℤ`, giving the product-formula height

`H_N=log C_N=Σ_p v_p(C_N)log p=log|Σ_p index_p(N)|`.

This is a direct integer comparison. The unresolved quantitative step is
`H_N≤(1/2+ε)log N+Oε(1)` on finite quotients. The construction records
the aggregate signed charge; a full count on Hecke correspondences and
the surface Riemann–Roch mechanism remain open.

## Divisor lattice volume and transverse height

[DivisorRelationGeometry.lean](DivisorRelationGeometry.lean) constructs the
actual lattice generated by `Σ_(d|j)e_d`, `2≤j≤N`. Integral inversion
identifies it with `ker(v↦Σ μ(j)v_j)` and gives its integral basis
`e_j−μ(j)e_1`. The Gram determinant is the independent squarefree count
`Q(N)=#{1≤j≤N:Squarefree j}`. Thus its Gram volume is

`V_N=√Q(N)≤√N`.

Integer unit changes of this actual basis give Gram entries
`δ_jk+1_Squarefree(j)1_Squarefree(k)`. The squarefree block is `I+11ᵀ`;
the other coordinates are orthogonal unit directions. Möbius signs
disappear from this metric matrix but remain in the distinguished gluing
vector's position.

The real span, explicit orthogonal projection and nearest-point property
are proved using the Euclidean sum of coordinate squares. For the actual
gluing column `b=−Σ_(j≥2)e_j`, let `D_N` be its distance from that span.
The [formalized comparison](../../../docs/drafts/pipeline/3-formalized/riac-divisor-relation-geometry.md)
gives

`|Σ_p index_p(N)|=V_N D_N`,
`H_N=½log Q(N)+log D_N` when the quotient is finite.

The zero-charge infinite cyclic case is recorded separately. The positive
square-root volume is proved; **the signed displacement is uncontrolled**.
An independent bound `D_N=Oε(N^ε)` would supply the RH-scale estimate.
The Gram classification and product formula alone do not supply that bound.

## Integral sections and addition-law height

[IntegralSectionHeight.lean](IntegralSectionHeight.lean) minimizes actual
integral section size `Σv_i²` in `A_N=ℤ^N/L_N`, before imposing the gluing
relation. If the resulting primitive charge is `k=qa+r`, with `q=Q(N)`
and `0≤r<q`, the minimum and its actual section count are

`E_N(c)=k²/q+r(q−r)/q`, `#MinimumSections(c)=binomial(q,r)`.

Every minimizer vanishes off the squarefree coordinates. Its oriented
squarefree values are `a` or `a+1`, with exactly `r` upper values. This
classification comes from integral convexity and an explicit subset
bijection, not a prescribed formula for the count.

Writing `ρ(c)=min(r,q−r)`, the exact addition defect is

`E(c+d)+E(c−d)−2E(c)−2E(d)=−2 min(ρ(c),ρ(d))`.

The normalized sizes `4^(−j)E(2^j c)` decrease to the Tate height `k²/q`,
with error at most `(q/4)4^(−j)`. For the original gluing class, minimum
size is `|Σ_p index_p(N)|` and Tate height is `D_N²`. The
[formalized section theory](../../../docs/drafts/pipeline/3-formalized/riac-integral-section-height.md)
therefore retains the actual signed target and the quotient addition law.

The logarithm of the minimizer count is bounded by `q log 2` and has
zero quadratic Tate limit. It must not be substituted for section size.
The full Gaussian sum below supplies a nonzero logarithmic coefficient.

## Gaussian arithmetic counts and their two limits

[GaussianSectionHeight.lean](GaussianSectionHeight.lean) sums all actual
integral representatives of a quotient class:

`Θ_N(c,t)=Σ_(v representing c) exp(−t Σ_i v_i²)`, `t>0`,
`H_N(c,t)=log Θ_N(0,t)−log Θ_N(c,t)`.

Ambient Gaussian summability proves convergence, and an actual section
proves positivity of the sum. Integral normal translation makes the error
from `tk²/Q(N)` periodic in charge modulo `Q(N)`. One finite arithmetic
dilation already satisfies `H_N(Q(N)c,t)=tQ(N)k²`.

[GaussianSectionPositivity.lean](GaussianSectionPositivity.lean) proves the
finite height comparison, with `q=Q(N)` and `r=k mod q`:

`t k²/q≤H_N(c,t)≤t E_N(c)`,
`0≤H_N(c,t)−t k²/q≤t r(q−r)/q≤tq/4`.

An explicit rational normal extension of the actual divisor lattice
factors its full Gaussian sum into one normal factor and the arithmetic
section sum. Poisson summation and positive dual Gaussian coefficients
prove the lower bound. Pairing opposite zero-class sections after an
actual integral translation proves the upper bound. The finite height
vanishes exactly on the zero arithmetic class.

The actual addition defect lies in `[-tq,tq/2]`. Two operations recover
different arithmetic invariants:

`lim_(j→∞) 4^(−j)H_N(2^j c,t)=t k²/q`,
`lim_(t→∞) H_N(c,t)/t=E_N(c)`.

The [Tate construction](../../../docs/drafts/pipeline/3-formalized/riac-gaussian-section-height.md)
defines the first limit before identifying its coefficient. The
[positive height and large-decay theorem](../../../docs/drafts/pipeline/3-formalized/riac-gaussian-section-positivity.md)
proves the second limit for the full real parameter, with reciprocal
error bounded by `(E_N(c)+log Θ_N(c,1))/t` for `t≥1`.

On the original gluing class these limits are `tD_N²` and `|1−M(N)|`,
and every finite positive rate satisfies
`tD_N²≤H_N([b],t)≤t|1−M(N)|`.
The domain is the rank-one quotient `A_N≃ℤ`; a full height on Hecke
correspondences remains unconstructed. Both limits fix the conductor.
An independent height upper bound controlling `D_N=Oε(N^ε)` remains
necessary for RH-scale signed cancellation.

## Finite Gaussian heights across conductors

[GaussianSectionUniformity.lean](GaussianSectionUniformity.lean) gives a rate
chosen solely from the conductor:

`a_N=π+2log(4(N+1))`, `t_N=π²/(2a_N)`.

For every `N≥1` and every actual quotient class, with charge `k`,

`0≤H_N(c,t_N)−t_N k²/Q(N)≤2/(N+1)`.

On the original gluing class this gives

`0≤H_N([b],t_N)/t_N−D_N²≤4a_N/(π²(N+1))`.

[GaussianDualArithmeticBound.lean](GaussianDualArithmeticBound.lean)
constructs an injective integer coding of the actual dual lattice.
Nearest-integer rounding of its normal coefficient loses at most a factor
of two in squared length. The dual Gaussian sum is consequently bounded
by `θ(a/2)^(N+1)`, where `θ` counts one unrestricted integer coordinate.
Removing the dual zero frequency in Poisson summation bounds all shifted
log-count ratios uniformly. The explicit rate pays for the growing number
of coordinates; the actual section factorization transfers the estimate
to the arithmetic height.

The [formalized bound](../../../docs/drafts/pipeline/3-formalized/riac-uniform-gaussian-height.md)
is a direct finite-count estimate, with no exchange of limits. It controls
the approximation error. The independent upper bound on the distinguished
height `H_N([b],t_N)` needed for signed cancellation remains open.

## Sections preserving conductor multiplication

[HeckeArithmeticSections.lean](HeckeArithmeticSections.lean) constructs
`A/J`, where `A=⊕_(n≥0) ℤe_n` and `J` consists of nonsquarefree coordinates.
Both are defined by integer divisibility. Ordinary conductor multiplication
`T_a e_n=e_(an)` descends to this quotient, which is explicitly the free
integer module on squarefree conductors, with proved rank `ℵ₀`. Residue sections through `N`
have `q^Q(N)` elements for every integer modulus `q≥1`.

[HeckeChargeSeparation.lean](HeckeChargeSeparation.lean) proves
`J=⋂_a ker(C∘T_a)` for `C(v)=Σ μ(n)v_n`. Tests `a≤N` already recover all
squarefree coefficients of a probe supported through `N`: the multiplication
matrix `μ(ab)` is unimodular on that divisor down-set. Thus `J` is the
largest dilation-stable submodule of `ker C`.

The single-charge quotient cannot carry this action:
`C(e₁+e_p)=0`, whereas `C(T_p(e₁+e_p))=−1`. In the full replacement,
`T_p≠0` and `T_p²=0`. Consequently every real function satisfying
`H(0)=0` and `H(T_p x)=pH(x)` is identically zero. Additive class dilation
in the Gaussian Tate construction therefore cannot be identified with
ordinary conductor multiplication. A different geometric correspondence
operator or enlarged arithmetic object remains necessary.

[HeckeGluingComparison.lean](HeckeGluingComparison.lean) retains the original
gluing class `−Σ_(2≤n≤N)e_n` and proves its charge is exactly
`Σ_p index_p(N)=1−M(N)`. The independent section module retains the signed
target and every conductor translate; its unsigned residue count supplies
no square-root estimate. The [construction and obstruction](../../../docs/drafts/pipeline/3-formalized/riac-hecke-stable-arithmetic-sections.md)
include their integral proofs.

## Arithmetic intersection counts and local multiplicities

[ThickenedArithmeticIntersections.lean](ThickenedArithmeticIntersections.lean)
constructs the actual residue ring `ℤ[X]/(P,Q)` for proper monic divisors
on `Spec ℤ[X]`. Monic division identifies its additive group with the
integral Sylvester cokernel. Its cardinality is `C(P,Q)=|Res(P,Q)|`,
with finiteness proved from the nonzero resultant.

Thickening the two equations gives

`C(P^a,Q^b)=C(P,Q)^(ab)`.

Consequently the prime-local order multiplicity `i_p(P,Q)=v_p(C(P,Q))`
is an integer and scales by `ab`; the independent logarithmic height
`H(P,Q)=log C(P,Q)` has the same scaling. Its local-global formula is
`H=log|Res(P,Q)|=Σ_p i_p log p`. Equal thickening gives exact quadratic
local multiplicities and logarithmic height. The residue cardinality itself
has exponential scaling in `k²`.

Distinct cyclotomic divisors satisfy properness arithmetically. Their
thickened logarithmic counts recover `ab·I(n,m)`, the established torsion-orbit
intersection. The count therefore has a proved comparison with the existing
torsion geometry, with no Weil form used in its definition.

These counts construct effective proper intersections. The radial
self-interaction below removes coincident-root factors arithmetically.
The surface Riemann–Roch count and a comparison controlling
`Σ_p index_p(N)=1−M(N)` remain open.

## Literature and novelty boundary

Connes–Consani construct integer dimensions and Riemann–Roch on the Arakelov
compactification of `Spec ℤ`: [2023 paper](https://arxiv.org/abs/2205.01391)
and [2024 refinement](https://www.numdam.org/articles/10.5802/crmath.543/).
This verifies the report’s external lead. Those results concern divisors on
the arithmetic curve. The inference needed here is a new product geometry
with a quadratic count on correspondences; the cited results do not provide
that construction or its required sign.

Completing squares and the Schur complement are classical. Any contribution
here must identify the exact arithmetic restriction, its infinite payment
threshold and what survives the critical obstruction. Existing finite-pair
indefiniteness and counterterm-rank laws remain prior corpus results.
The existing [Möbius gluing identity](../HodgeTheoryWithoutVarieties/TheRenormalizedFormIsGluedFromItsStars.lean)
already completes the root squares at diagonal `Λ(k)` with a cutoff-dependent
Mertens payment. The present branch asks for arbitrary prime diagonals and
a finite payment uniform over every finite prime set.

The existing [prime-face graph gauge](../RHTower/PrimeFaceBoundaryGauge.lean)
trivializes the row-summability graph family in the product topology for all
complex parameters. That topology does not preserve a prescribed Hilbert norm.
The weighted exterior theorem establishes its own norm and graph comparisons;
algebraic or product-topology conjugacy alone does not supply them.

## Calibration and success criteria

Recover Hasse–Weil from heights or counts for elliptic and hyperelliptic
curves without assuming a positive form. Reject Golden, the complex fake,
shifted data with nonnegative Tate coefficients and the genus-two graph in
the regimes where their count law fails. Test the polynomial prime complex
over `𝔽_q[T]`, where Möbius cancellation is exact beyond degree one.

Preserve infinite rank, all probe information, the linear Betti mass,
the isolated fixed-point lower bound and the infinitely recurring square-root
Euler lower bound. A modular comparison must distinguish Eisenstein and
cuspidal contributions. A completed complex must genuinely depend on `s`;
positive weights alone do not reach the critical boundary.

The [Tate count theorem](../CountingHolography/TheTateLimitOfACount.lean)
identifies the full count target with RH. The
[Farey–horocycle comparison](../CountingHolography/TheHorocycleRateIsTheSquareRootFareyLaw.lean)
provides an arithmetic observable, without a prime-core cell action.
The [completed-boundary theorem](../../../docs/drafts/pipeline/3-formalized/riac-completed-prime-boundary.md)
settles the exact augmentation domain before introducing higher homology.

The [logarithmic full-form candidate](../../../docs/drafts/pipeline/1-in-progress/riac-logarithmic-torsion-completion.md)
asks whether the sharp prime-star exponent extends to boundedness and positive
diagonal completion on every conductor. [LogarithmicMangoldtTail.lean](LogarithmicMangoldtTail.lean) proves its
required full Mangoldt tail for every exponent above one. The combined
Schur estimate and completed-form classification remain unverified.

The independent surface count, critical positive completion, zero-detecting
completion, relative core pair and modular cell comparison remain open.
Signed localization is constructed, with no square-root Mertens bound or RH
proof asserted.

## Radial counts and arithmetic self-intersection

[RationalAbelArithmeticCounts.lean](RationalAbelArithmeticCounts.lean)
constructs the finite rings cut out by the monic radial equations
`P_{n,a}=scaleRoots(Φ_n,a)`. For `0≤a<b`, their cardinalities satisfy

`log C_{m,n}(a,b)=φ(m)φ(n)log b−T_{a/b}(m,n)`.

The Abel energy thus comes from independent integral quotient counts.
For self-interaction, the integral divided difference
`P_{n,b}−P_{n,a}=(b−a)D_{a,b}` defines another actual finite ring,
with count `R_n(a,b)`. Multiplication by `b−a` and reduction give the
residual exact sequence and prove

`C_{n,n}(a,b)=(b−a)^φ(n) R_n(a,b)`.

At coincidence `D_{1,1}=φ(n)Φ_n−XΦ_n′`; the residue count is
`R_n(1,1)=|disc Φ_n|`, with logarithm `I(n,n)`. Its dilation degree is
`φ(n)(φ(n)−1)`. The normalized residual height retains the HHAC
nonnegative quadratic radial error and converges, along consecutive integer
radii, to the actual diagonal height.

The [construction and proof](../../../docs/drafts/pipeline/3-formalized/riac-rational-abel-intersection-counts.md)
identify arithmetic self-energy removal and both radius terms. Classical
resultant and `q`-discriminant identities are credited there. These counts
still require a quantitative bridge to signed conductor combinations and
the local-index sum `1−M(N)`; no square-root estimate follows yet.

## Finite-field orientation counts

[FiniteFieldOrientationCounts.lean](FiniteFieldOrientationCounts.lean)
derives the orientation sign of an actual finite extension `K/F`:
Frobenius has characteristic polynomial `X^d−1`, and the quadratic character
of every basis trace discriminant is `(-1)^(d+1)`. Thus its square-root
fibre has two points for odd degree and none for even degree.

For monic `f`, take the product `D(f)` of power-basis trace discriminants
of its irreducible residue fields on the squarefree locus, and zero
elsewhere. This definition uses no Möbius coefficient. Its character is
`χ(D(f))=(-1)^deg(f) μ(f)`. The actual set of pairs
`(f,y)` with `deg(f)=n` and `y²=D(f)` has respectively `2`, `2q`, `q^n`
points in degrees zero, one, and at least two.

The [formalized count](../../../docs/drafts/pipeline/3-formalized/riac-finite-field-orientation-counts.md)
uses the existing derived polynomial Möbius degree sums. The
[cross-resultant comparison](../../../docs/drafts/pipeline/3-formalized/riac-discriminant-cover-signed-counts.md)
also identifies this actual cover with the independently counted root cover.
It consequently derives the polynomial Möbius cancellation from arithmetic
orientation counts. The integer conductor comparison remains open.

## Independent Frobenius orbit count

[FiniteFieldOrbitCounts.lean](FiniteFieldOrbitCounts.lean) constructs the
finite extension of degree `|G|` for any finite permutation action on `n`
labels. Its Frobenius-stable tuple orbits number exactly `q^n`. Explicit
normal-basis bijections give `q^n` solutions to every permutation twist;
transporter torsors then give the orbit total. No Möbius degree sum enters
this proof, and repeated coordinates are retained.

The [formalized construction](../../../docs/drafts/pipeline/3-formalized/riac-independent-frobenius-orbit-counts.md)
supplies an independent finite-field count. Its signed refinement counts
the actual root cover below. The integer local-index comparison remains open.

## Signed Frobenius orbits

[FiniteFieldSignedOrbits.lean](FiniteFieldSignedOrbits.lean) assigns each
actual tuple orbit the difference of its positive and negative transporter
counts, divided by the group order. These orientation weights are proved
to lie in `{-1,0,1}`. Non-fixed orbits and odd stabilizers give zero;
otherwise the weight is the transporter character.

For permutation orbits, repeated coordinates give zero and distinct
coordinates retain Frobenius sign. Independent normal-basis counts prove
that the total weight is exactly zero whenever there are at least two
labels. This holds in every finite characteristic and uses no polynomial
Möbius cancellation theorem.

The [formalized signed count](../../../docs/drafts/pipeline/3-formalized/riac-finite-field-signed-orbits.md)
is a finite-field orientation mechanism. The discriminant comparison below
identifies each weight with `(-1)^deg(f) μ(f)` over odd fields. Identification
with integer relative-homology indices remains open; no bound on `1−M(N)`
follows.

## Arithmetic Vieta correspondence

[FiniteFieldVieta.lean](FiniteFieldVieta.lean) identifies monic degree-`n`
polynomials with Frobenius-stable permutation orbits in the actual extension
of degree `n!`. Every irreducible factor's residue field embeds there, so
all roots exist. Equal root products give equal multiplicity fibres and
hence a permutation, including collisions. The coefficient count and the
independent normal-basis count both give `q^n`, making the injection onto.

The [formalized correspondence](../../../docs/drafts/pipeline/3-formalized/riac-arithmetic-vieta.md)
connects actual coefficient polynomials to the independently counted
arithmetic orbits. The root-cover count below uses this correspondence.
The integral coefficient equation below identifies the root cover with
`Polynomial.discr`. The integer-cutoff estimate remains open.

## Independent root-cover count

[FiniteFieldRootCover.lean](FiniteFieldRootCover.lean) counts actual pairs
`(f,y)` with `f` monic of degree `n`, `y∈F`, and
`(ιy)²=V(x_f)²` in the constructed degree-`n!` extension. Here `x_f`
orders the roots with multiplicities and `V` is their Vandermonde product.
Its square is independent of the ordering.

Collisions give one point. Distinct roots give two or zero points according
to Frobenius orientation. Thus each fibre has cardinality `1+w`, and
independent transporter cancellation proves exactly `q^n` points for
`n≥2` over every odd finite field. No polynomial Möbius degree sum enters
the [formalized count](../../../docs/drafts/pipeline/3-formalized/riac-root-orientation-cover.md).

## Integral discriminant equation and signed fibres

[CoefficientDiscriminantCover.lean](CoefficientDiscriminantCover.lean)
constructs one polynomial `Δ_n ∈ ℤ[c₀,…,c_(n−1)]` in ordinary monic
coefficients. Vieta identifies its value with the squared Vandermonde,
including collisions, and its equation commutes with ring homomorphisms.
Actual affine points `(c,y)` with `y²=Δ_n(c)` are in bijection with the
root-orientation cover.

[ArithmeticDiscriminantCover.lean](ArithmeticDiscriminantCover.lean)
identifies `Δ_n(c)` with `Polynomial.discr(f)` over every integral domain.
The proof evaluates the Sylvester resultant at labelled roots and descends
through splitting and fraction fields. It also identifies each discriminant
character with its signed arithmetic transporter weight. Thus, over every
odd finite field, the actual cover has `2`, `2q`, `q^n` points in degrees
zero, one and at least two; the discriminant-character sum vanishes for
`n≥2`. No polynomial Möbius degree-sum theorem enters the count.

The [formalized construction](../../../docs/drafts/pipeline/3-formalized/riac-integral-discriminant-cover.md)
gives an integral arithmetic family and a pointwise signed comparison.

[FiniteFieldDiscriminantComparison.lean](FiniteFieldDiscriminantComparison.lean)
constructs the product `R(f)` of cross-resultants and proves
`disc(f)=D(f)R(f)²`, where `D(f)` is the factor-trace invariant. On squarefree
fibres `R(f)≠0`; multiplication by it gives an actual fibre bijection. On
ramified fibres both discriminants vanish and the map fixes zero. These maps
assemble into a coefficient-preserving bijection of the two finite covers.

Over odd fields, each actual root-orbit weight equals `(-1)^n μ(f)` in degree
`n`. Independent transporter cancellation gives both `q^n` factor-cover
points and `Σ_(deg f=n) μ(f)=0` for `n≥2`, without using a polynomial
Möbius degree-sum theorem as input. The
[formalized comparison](../../../docs/drafts/pipeline/3-formalized/riac-discriminant-cover-signed-counts.md)
uses a discriminant product law valid over every commutative ring and the
actual residue-field power-basis discriminants. The integer conductor
estimate remains open.

The [general curve construction](../../../docs/drafts/pipeline/3-formalized/riac-curve-orientation-square-root.md)
gives actual orientation counts on odd-degree hyperelliptic curves, with
square-root-scale discrepancy derived from Stepanov's theorem. Its
arithmetic fixed-point and signed coefficient comparisons are proved.
The integer conductor-cutoff comparison with `1−M(N)` remains open.

## Integer prime-quadratic fibres

For `n>0`, form the integral polynomial `F_n(X)=∏_(p^a∥n)(X²+p)^a`
from prime factorization alone. Write `r=Ω(n)` and let `Δ_n` be the product
of pairwise differences in its prime-factor list.
[PrimeQuadraticDiscriminant.lean](PrimeQuadraticDiscriminant.lean) proves

`disc(F_n)=(-4)^r n Δ_n^4`, `sign(disc(F_n))=μ(n)`.

[PrimeQuadraticOrientationCounts.lean](PrimeQuadraticOrientationCounts.lean)
counts actual real solutions of `y²=disc(F_n)`, including one branch point
at repeated factors. Its disjoint union through `N` has `R_N=N+M(N)` points.
For `N≥1`, the original relative singular indices satisfy
`Σ_p index_p(N)=N+1−R_N`.
This is a real-place comparison. Transferring the finite-field square-root
estimate to this integer-conductor family remains open.

[PrimeQuadraticDifferentCounts.lean](PrimeQuadraticDifferentCounts.lean)
uses the same equation to construct `A_n=ℤ[X]/(F_n,F_n')`. At squarefree
conductors this ring is finite with `C_n=#A_n=|disc(F_n)|`, and
`Σ_p v_p(C_n)log p=log|disc(F_n)|`. At repeated factors it is infinite.
The [integral cokernel theorem](../HTGeometry/SingularIntegralCokernel.lean)
extends determinant cardinality to this nonproper case by constructing a
nonzero integral functional on every singular cokernel.

[PrimeQuadraticTraceCounts.lean](PrimeQuadraticTraceCounts.lean) identifies
the actual integral trace cokernel of `ℤ[X]/(F_n)` with `A_n`. The
[residue pairing](../HTGeometry/MonicResiduePairing.lean) is perfect even
at repeated factors: its coefficient-tail dual basis has Casimir `F_n'(t)`,
and `Tr(x)=λ(xF_n'(t))`. Thus the trace cokernel and different intersection
are integrally equivalent, and the absolute trace discriminant equals
`|disc(F_n)|`. Both presentations give the same product-formula height.

Conductor multiplication gives `F_(mn)=F_mF_n` and
`C_(mn)=C_m C_n |Res(F_m,F_n)|²`. Every nontrivial conductor square has an
infinite different quotient, obstructing finite Tate counts under powers
within this family. The actual global rational fibres are classified in
[PrimeQuadraticRationalFibres.lean](PrimeQuadraticRationalFibres.lean): their
total for `N≥1` is `N+2−Q(N)`, where `Q(N)` counts squarefree integers.
They retain squarefree support and lose the Möbius orientation.

The [formalized comparisons](../../../docs/drafts/pipeline/3-formalized/riac-prime-quadratic-counts.md)
construct counts and a product formula independently of the signed sum.
The signed trace-discriminant equality, uniform geometric control, and
an independent bound for `|N+1−R_N|` remain open.

## Actual orientation quotient

[OrientationQuotientCounts.lean](OrientationQuotientCounts.lean) constructs
the action on `X×{±1}` from an orientation character. Its arithmetic stable
orbit count `A` and the ordinary count `B` satisfy
`|G|(A−B)=Σ_x Σ_{g·x=φ(x)} χ(g)`. Thus the normalized local orientation
sum is an integer difference of actual counts. Stabilizers and trivial
characters are retained, including both orientation labels in degrees
zero and one. This [count realization](../../../docs/drafts/pipeline/3-formalized/riac-orientation-quotient-counts.md)
does not itself bound the difference.

[TupleOrientationCounts.lean](TupleOrientationCounts.lean) identifies this
difference for a finite point permutation with the intrinsic signed sum
over invariant `n`-point subsets. Odd swap stabilizers cancel collisions.
Each injective tuple has its support's permutation sign, and an explicit
ordering bijection supplies exactly `n!` tuples per support. This proves
the comparison for the original quotient counts, including degrees zero
and one.

[OrientationDeterminant.lean](OrientationDeterminant.lean) identifies these
independent counts with the actual permutation determinant:
`A_n−B_n=[t^n]det(1+tP_φ)`. Principal minors on invariant supports are
their permutation signs; moving supports have a zero row. Also
`Tr(P_φ^d)=#Fix(φ^d)`. The [formalized identities](../../../docs/drafts/pipeline/3-formalized/riac-orientation-determinant.md)
retain collisions through the tuple comparison and require no simple
spectrum. They expose the precise coefficient problem without assuming
a signed estimate.

[FibrePermutationSigns.lean](FibrePermutationSigns.lean) decomposes the
orientation sign over any invariant finite partition. If every fibre is
nonempty and transitive, the sign is `(-1)^(number of points + number of
fibres)`. Singleton fibres remain in the formula; deleting fixed points
without correcting the fibre count would give the wrong exponent.

## Square-root cancellation of actual elliptic divisor counts

[SquarefreeDivisorCounts.lean](SquarefreeDivisorCounts.lean) constructs
even and odd support counts from finite sets of places with residue
degrees. Their difference is the corresponding inverse Euler coefficient.
[EllipticSquarefreeCounts.lean](EllipticSquarefreeCounts.lean) applies this
construction to the actual closed points of `Y²Z=X³−XZ²` over `F₃`,
including infinity. The degree cutoff omits no divisor. For every `n≥0`,

`|E_n−O_n|≤8(n+1)²(√3)^n`,

`|Σ_(k≤n)(E_k−O_k)|≤24(n+1)²(√3)^n`.

These [formalized bounds](../../../docs/drafts/pipeline/3-formalized/riac-elliptic-squarefree-divisor-cancellation.md)
use the proved actual-place Euler product, curve rationality and actual
Frobenius root bound. No Weil-root, simplicity or cancellation assumption
is added. At norm horizon `N=3^n`, the bound is `√N` times a quadratic
logarithmic loss. The mechanism is classical; the contribution is its
realization by actual finite arithmetic counts with complete Lean proofs.
The integer conductor-height transfer remains open.

[EllipticFrobeniusOrbits.lean](EllipticFrobeniusOrbits.lean) supplies the
geometric fibre comparison. Frobenius is transitive on actual residue-field
embeddings. Two actual projective points map to the same closed place
exactly when a Frobenius power joins them, with infinity fixed. The powers
satisfy the identity and composition laws. Thus the supported closed-place
fibres are the actual arithmetic orbits; the [formalized comparison](../../../docs/drafts/pipeline/3-formalized/riac-elliptic-frobenius-orbits.md)
does not assume an orbit-count identity.

[EllipticStableSubsets.lean](EllipticStableSubsets.lean) identifies actual
Frobenius-stable `n`-point subsets in the degree-`n!` extension with all
squarefree divisors of degree `n`. Every fibre contributes its residue
degree in points. The intrinsic Frobenius orientation is
`ε(T)=(-1)^(|T|+|support(T)|)`, retaining infinity and singleton fibres.
Consequently the independently defined geometric sum `J_n=Σ_T ε(T)`
satisfies `J_n=(-1)^n(E_n−O_n)` and `|J_n|≤8(n+1)²(√3)^n`.
This [signed configuration theorem](../../../docs/drafts/pipeline/3-formalized/riac-elliptic-stable-orientation.md)
is formalized.

[EllipticOrientationCounts.lean](EllipticOrientationCounts.lean) constructs
the original arithmetic counts `A_n` and `B_n` from Frobenius-stable orbits
of actual curve tuples, with and without the two-point orientation label.
They satisfy `A_n−B_n=J_n=(-1)^n(E_n−O_n)` and therefore
`|A_n−B_n|≤8(n+1)²(√3)^n`. Their definitions use no signed divisor count.
The [quotient comparison and bound](../../../docs/drafts/pipeline/3-formalized/riac-elliptic-orientation-quotients.md)
are formalized, with collisions and both low-degree labels retained.

## Square-root cancellation for general hyperelliptic curves

[HyperellipticOrientationCounts.lean](HyperellipticOrientationCounts.lean)
defines the two actual orbit counts for every squarefree odd-degree
polynomial `f` over an odd finite field of cardinality `q`. For
`m=deg f`, they satisfy, in every degree `n≥0`,

`A_n−B_n=[t^n](1+t)(1+qt)∏_i(1+α_i t)⁻¹`,

`|A_n−B_n|≤(2q+2)(n+1)^(m−1)(√q)^n`.

The roots `α_i` come from the actual arithmetic L-polynomial and enter
only the proof. The count definitions use actual point tuples and
orientation labels, with all collisions and low-degree labels retained.

[HyperellipticFixedPoints.lean](HyperellipticFixedPoints.lean) supplies the
general arithmetic fixed-point comparison. An embedded degree-`d` field
is exactly the fixed field of `Frobenius^d`. Coordinate descent identifies
its solutions of `y²=f(x)`, with infinity, with the actual fixed points
in the ambient field. For odd-degree `f`, the count is
`q^d+1−Σαᵢ^d`, with the actual arithmetic L-polynomial roots.
The [formalized comparison](../../../docs/drafts/pipeline/3-formalized/riac-hyperelliptic-fixed-points.md)
discharges degree divisibility for every `1≤d≤n` in the degree-`n!`
extension. It requires no Weil-circle or cancellation input.

[TruncatedTraceComparison.lean](TruncatedTraceComparison.lean) combines
these traces with the actual permutation determinant. Schur triangulation
retains multiplicities. Newton identities through degree `n` compare the
matrix spectrum together with the curve roots to the two polar entries
`1,q`, without equal-cardinality or simple-spectrum assumptions.
Reciprocal multiplication gives the exact signed coefficient. The derived
Stepanov theorem bounds every actual root by `√q`, including nonsplit
polynomials, and gives the displayed estimate.

This [general cancellation theorem](../../../docs/drafts/pipeline/3-formalized/riac-curve-orientation-square-root.md)
is at the square-root scale for `N=q^n`, with a polynomial logarithmic
loss for a fixed curve. It supplies no uniform-genus estimate or
integer-height transfer. Control of the actual integer sum `1−M(N)`
remains the governing open problem.
