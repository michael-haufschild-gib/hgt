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
uses the existing derived polynomial Möbius degree sums. It retains an
arithmetic orientation sign but supplies no independent cancellation
estimate. The independent root-cover count below supplies a separate producer.
Comparisons with the factor-trace invariant, `Polynomial.discr` and the
integer cutoff remain
[construction problems](../../../docs/drafts/pipeline/1-in-progress/riac-discriminant-cover-signed-counts.md).

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
is a finite-field orientation mechanism. Its polynomial factorization
comparison and identification with integer relative-homology indices
remain open; it supplies no bound on `1−M(N)`.

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
Identification with `Polynomial.discr` and the integer-cutoff estimate
remain open.

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
The ordinary polynomial-discriminant comparison remains separate.

A [further construction problem](../../../docs/drafts/pipeline/1-in-progress/riac-curve-orientation-square-root.md)
asks for actual orientation counts on hyperelliptic curves, with
square-root-scale error derived from the existing Stepanov theorem.
That requires an actual curve-count comparison; an abstract tuple of
assumed Weil roots is insufficient. Neither finite-field construction
currently controls the integer conductor cutoff in `1−M(N)`.

## Actual orientation quotient

[OrientationQuotientCounts.lean](OrientationQuotientCounts.lean) constructs
the action on `X×{±1}` from an orientation character. Its arithmetic stable
orbit count `A` and the ordinary count `B` satisfy
`|G|(A−B)=Σ_x Σ_{g·x=φ(x)} χ(g)`. Thus the normalized local orientation
sum is an integer difference of actual counts. Stabilizers and trivial
characters are retained, including both orientation labels in degrees
zero and one. This [count realization](../../../docs/drafts/pipeline/3-formalized/riac-orientation-quotient-counts.md)
does not itself bound the difference.

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
The orientation-quotient comparison and the integer conductor-height
transfer remain open.
