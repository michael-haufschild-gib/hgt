# Effective geometry of the scaling surface

This programme seeks sections, divisors and intersection multiplicities on the
scaling surface of the integers. Its purpose is to supply the geometric reason
for effectivity, rather than rename the Weil quadratic form as a count.
The motivating specification is §2.11 of
[the first obstacles report](../../../docs/reports/review-0611/obstacles-summary.md).

The namespace is `GaloisForLFunctions.EffectiveScalingGeometry`;
the programme umbrella is `EffectiveScalingGeometry.lean`.

## Motivation and position

For a curve over a finite field, sections have zero divisors, distinct effective
curves have nonnegative intersection, and Riemann–Roch supplies sections.
Together these produce the primitive sign in Weil's argument. On the scaling
surface, the corpus already has the intersection pairing, polar directions,
Riemann–Roch identities and equivalences between Hodge index and RH. What is
missing is an independent source of sections and their nonnegative counts.

[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md)
owns the existing surface and sign receivers. This programme owns constructions
of effectivity and geometric invariants which can feed those receivers.
[Arithmetic orientation geometry](../ArithmeticOrientationGeometry/README.md)
studies arithmetic counts and orientation. The companion
[height and homotopy programme](../HeightHomotopyArithmeticCounts/README.md)
studies addition, local heights and fixed-point mechanisms. Their shared objects
do not identify their open inputs: a height needs an addition law; a section
needs a divisor and an independently defined zero set.

## Objects and language

| Object | Intended role |
|---|---|
| Scaling cycle `aH+bV+f` | Two polar degrees and a compactly supported source |
| Window and lattice | Finite aperture and a discrete family of translates |
| Primitive class | Component orthogonal to both polar directions |
| Section | Arithmetic datum whose zero divisor is defined before its count |
| Effective divisor | Actual zero divisor or nonnegative sum of irreducible curves |
| Hecke correspondence | Scaling translate with arithmetic incidence |
| Canonical class, primitive `h¹` | Terms in Riemann–Roch and its vanishing mechanism |
| Predictor and winding | Discrete index of a window, requiring a geometric realization |
| Prime complex and star cover | Arithmetic simplicial objects with height filtration |

“Effective” must mean a constructed object, not membership in a cone defined by
the desired sign. “Degree” must specify whether it means polar degree, support
aperture, or arithmetic height. “Ample” must supply a testable positivity or
vanishing mechanism; an RH-equivalent predicate alone supplies no such mechanism.

## Foundational pillars

The existing corpus provides the following starting points; they are not new
results of this programme.

1. The scaling surface has isotropic polar directions with intersection one;
   its primitive defect is the Weil form.
2. On finite curve windows, the relevant Künneth positivity is equivalent to
   unitarity. Correct formal weights alone do not force purity.
3. Arithmetic sections supported near integer logarithms have positive source
   floors in a restricted spacing regime. Extending that carrier requires
   control of omitted directions and their mixed intersections.
4. The prime complex has linearly many homology generators. Small Euler
   characteristic therefore requires cancellation between degrees, not merely
   a small homotopy model.

New pillars must give actual sections and divisors, functorial restriction and
gluing, negative-degree vanishing, and a count or index formula independent of
the Weil form. These remain construction problems, not assumptions available
to Lean theorems.

The first geometric construction is a prime-height filtration in a fixed
ambient simplex. Its faces are prime supports of product at most `N`.
Coning to vertex `2` gives an explicit nullhomotopy of the actual inclusion
from height `N≥1` to `2N`, compatible with increasing height. This is
[`PrimeHeightFiltration.lean`](PrimeHeightFiltration.lean).

[`ConeFiltrationPersistence.lean`](ConeFiltrationPersistence.lean) supplies
the compatible map calculation for conical-star bouquets. A sphere whose
facet remains outside the larger star survives by a pointed homotopy to
its unchanged inclusion. A facet entering the larger star maps identically
to the basepoint. Thus the construction controls inclusion maps, beyond
the known homotopy type of each individual prime complex.

[`PrimePersistenceIntervals.lean`](PrimePersistenceIntervals.lean) proves
the arithmetic specialization. A prime support of product `m` is a
complementary facet precisely at heights `m≤N<2m`; its label is odd and
squarefree, and its cardinality is `ω(m)`. The actual filtration map preserves
its boundary sphere up to an explicit homotopy while the target height is
below `2m`, and maps it constantly to the basepoint thereafter. The finite
ambient model contains every face of the original prime nerve once the
ambient labels extend beyond the height.

This is a geometric interval law for inclusion maps. The homology persistence
functor below supplies the algebraic object; its natural surviving-coordinate
isomorphism is now established in every augmented exterior degree. The common logarithmic lifespan `log 2` gives no
parity information to lifespan-only
weights; birth locations and sphere dimensions retain arithmetic information.
The law therefore identifies what a richer weighting must use without
claiming an Euler-cancellation bound.

The companion programme's
[component and core theorems](../HeightHomotopyArithmeticCounts/README.md)
give a further constraint on such weights. Upper-half primes are isolated
vertices fixed by every self-map homotopic to the identity. There are eventually
more than `C√N` of them for every constant `C`, so literal small-fixed-set
localization is unavailable. The connected core retains precisely the
positive-dimensional sphere summands, and its reduced Euler characteristic is
`−M(N)−#{N/2<p≤N}`. A cancellation mechanism must compare this core contribution
with the isolated-prime mass.

[`PrimeCutoffComplex.lean`](PrimeCutoffComplex.lean) constructs the actual
augmented exterior-chain complex at every prime-product cutoff, for every
commutative coefficient ring and every vertex boundary functional. Literal
inclusions define the height functor; applying homology gives its persistence
module, including the empty-face degree.

[`DirichletChainGauge.lean`](DirichletChainGauge.lean) multiplies each prime
vertex by `p^s` and extends through exterior powers. The inverse uses `−s`,
and the gauge preserves every cutoff. Contraction naturality gives
`d_s G_s = G_s d_0` for the actual Dirichlet boundary with weights `p^(−s)`.
[`DirichletPersistenceEquivalence.lean`](DirichletPersistenceEquivalence.lean)
makes these maps a natural chain isomorphism and hence a natural homology
persistence isomorphism, for every complex `s` and every degree.

Thus finite complex Dirichlet weights preserve algebraic persistence.
Analytic completion and norm control are separate questions. Integral nonunit
weights need not admit this gauge. Product-weighted homology itself is classical;
see [Ren–Wu–Wu](https://arxiv.org/abs/1708.06722). The contribution here is the
conjugacy on the actual prime-height complexes and their inclusion maps.

[`PrimeChainBasis.lean`](PrimeChainBasis.lean) identifies the tuple-defined
cutoff with the span of increasing prime supports of bounded product, over
any commutative ring. Membership is exactly a condition on the support of
exterior-basis coefficients.

[`PrimeCycleProjection.lean`](PrimeCycleProjection.lean) constructs a natural
retraction from each positive-degree chain module to its cycles at the same
height. The map is `d(2∧·)`. Its complementary term `2∧d` replaces a removed
prime by two, so it cannot increase the prime product. This splits the cycle
submodule before passing to homology and supplies explicit cycle representatives.

[`PrimeBoundaryHeight.lean`](PrimeBoundaryHeight.lean) identifies the boundary
submodule exactly: boundaries at height `N` are cycles at height `⌊N/2⌋`.
Deletion divides the product by at least two; adjoining two fills every cycle
at the smaller cutoff. The identity holds over every commutative ring and
includes the empty augmented degree. For an arbitrary weighted vertex
functional, the forward height decrease still holds.

[`OddPrimeChainProjection.lean`](OddPrimeChainProjection.lean) and
[`PrimeCycleCoordinates.lean`](PrimeCycleCoordinates.lean) give the natural
coordinate equivalence: cycles in positive exterior degree are exactly the
bounded odd-face coordinates. Forgetting two gives one direction; taking
the boundary of the two-cone gives its inverse. Thus both cycles and boundaries
have explicit arithmetic cutoff descriptions over any commutative ring.
[`PrimeCycleBasis.lean`](PrimeCycleBasis.lean) makes these coordinates actual
bases of the odd cutoff and cycle submodules, with basis cycles `d(2∧S)`.

[`PrimeCriticalCoordinates.lean`](PrimeCriticalCoordinates.lean) projects odd
chains onto the coordinates with `m≤N<2m`. This projection is split surjective
and has exactly the half-cutoff kernel. Its quotient is therefore free on the
surviving coordinates. Raising height retains each coefficient until `2m`;
these maps form a persistence functor, and projection commutes with odd-chain
inclusions.

[`PrimeHomologyCoordinates.lean`](PrimeHomologyCoordinates.lean) identifies
actual categorical homology persistence in every positive exterior degree with
the surviving-coordinate functor. It sends actual cycle classes to their odd
coefficients and commutes with all height maps. This supplies the categorical
comparison beyond the geometric interval law and the concrete subquotient.

[`PrimeAugmentedHomology.lean`](PrimeAugmentedHomology.lean) includes degree
zero and combines the comparisons into a natural isomorphism in every degree.
The empty support survives precisely on `[1,2)`.

[`PrimeSquarefreeIndices.lean`](PrimeSquarefreeIndices.lean) identifies each
prime face with its squarefree product, preserving cardinality and parity.
[`PrimeArithmeticPersistence.lean`](PrimeArithmeticPersistence.lean) reindexes
the actual homology functor naturally by odd squarefree integers: `m` contributes
the interval `[m,2m)` in exterior degree `ω(m)`. Every height map retains the
same coefficient until its death. The statement holds over any commutative ring.

[`PrimeIntegralCoefficients.lean`](PrimeIntegralCoefficients.lean) constructs
the canonical maps from integral prime chains to the same chains over any
commutative ring. They preserve every exterior basis face and commute with
actual boundaries, prime cones and height inclusions. The construction uses
the exterior universal property.

[`PrimeHomologyTensorCoordinates.lean`](PrimeHomologyTensorCoordinates.lean)
constructs the actual homology basis and the corresponding tensor equivalence
`R ⊗[ℤ] H_k(C(N);ℤ) ≃ H_k(C(N);R)`. Its pure-tensor coefficients are the
integral coefficients multiplied by the scalar.

[`PrimeHomologyCoefficientMap.lean`](PrimeHomologyCoefficientMap.lean) descends
canonical chain extension through the actual boundary quotient. Its homology
map sends each class to the class of its extended cycle and commutes with
height inclusions. [`PrimeHomologyBaseChange.lean`](PrimeHomologyBaseChange.lean)
identifies the tensor comparison with this actual map: `r⊗x ↦ r·H(ℤ→R)(x)`.
The proof uses the explicit surviving representatives `d(2∧S)`, including
the empty chain in degree zero. Thus coefficient extension commutes with
homology persistence over every commutative ring, without a flatness assumption.
[`PrimeArithmeticBaseChange.lean`](PrimeArithmeticBaseChange.lean) proves
compatibility in the arithmetic labels themselves: each odd-squarefree barcode
coefficient is the canonical image of its integer coefficient.
None of these algebraic interval descriptions bounds Euler cancellation.

Integral prime weights have a different filling law.
[`PrimeWeightedContraction.lean`](PrimeWeightedContraction.lean) uses the
boundary coefficient `p` at prime `p`. The difference of the three-cone and
two-cone satisfies `dh+hd=(3−2)id=id` and preserves height up to a factor of
three. Thus the actual inclusion `N→3N` is nullhomotopic and induces zero on
every augmented homology group, over any commutative ring. The cone commutes
with height inclusions. Over the integers, parity of the empty-chain coefficient
prevents filling the height-one generator at height two. Hence three is the
least uniform integer dilation.

[`PrimeWeightedBoundarySaturation.lean`](PrimeWeightedBoundarySaturation.lean)
identifies the integral boundary saturation exactly. A weighted cycle has a
bounding nonzero multiple at `N` precisely when it lies below `⌊N/2⌋`.
Coordinate cutoffs are saturated in the exterior lattice, and coning with two
fills the double of every such cycle. Thus torsion cycle classes are killed
by two, including the empty augmented degree.
[`PrimeWeightedHomologyTorsion.lean`](PrimeWeightedHomologyTorsion.lean) proves
this for actual categorical homology at every height and degree, and exhibits
a nonzero class of order two at height two. The full torsion classification
and its height maps remain open.

[`PrimeOddCutoffComplex.lean`](PrimeOddCutoffComplex.lean) deletes the
prime-two vertex inside the actual weighted complex. Every remaining deletion
divides height by at least three. This subcomplex, its homology and its
inclusion in the full complex are natural in height. It supplies the smaller
height bound needed to analyze integral weighted cycles.
[`PrimeTwoChainSplitting.lean`](PrimeTwoChainSplitting.lean) gives the actual
chain decomposition `Cₖ₊₁(N) ≃ Oₖ₊₁(N) ⊕ Oₖ(⌊N/2⌋)`. Its maps are odd
projection and contraction by the prime-two coordinate; the inverse adjoins
two to the second component and adds the first.
[`PrimeWeightedCycleHeight.lean`](PrimeWeightedCycleHeight.lean) sharpens the
second component to height `⌊N/3⌋` for integral prime-weighted cycles. The odd
boundary equation `d(Ox)+2δ₂x=0` and saturation of coordinate cutoffs give the
extra decrease. This permits adjoining three to that component within `N`.
[`PrimeWeightedCycleCoordinates.lean`](PrimeWeightedCycleCoordinates.lean)
then identifies integral weighted cycles naturally with bounded odd-face
coordinates. The representative of an odd chain is `d((e₃−e₂)∧·)`; the inverse
is `O+e₃∧δ₂`. Both preserve height. The resulting actual integral cycle basis
has one vector per bounded odd face. The boundary relations are explicit below;
torsion counts and actual persistence transitions still require the quotient comparison.
[`PrimeConeKernel.lean`](PrimeConeKernel.lean) identifies the kernel of adjoining
any prime inside an odd cutoff: it is exactly the span of bounded odd faces
already containing that prime. The proof contracts the same coordinate and
recovers the projection onto faces omitting it. This holds over every
commutative ring and supplies the coordinate description needed at prime three.

[`PrimeWeightedBoundaryCoordinates.lean`](PrimeWeightedBoundaryCoordinates.lean)
identifies the exact integral boundary lattice in positive exterior degree.
In corrected odd coordinates it is
`O(⌊N/3⌋)+2O(⌊N/2⌋)+(O(⌊N/2⌋)∩ker(e₃∧·))`.
The last summand consists of faces containing three. Splitting a filling into
its odd and two-cone parts gives one containment; the Bézout cone and two-cone
supply explicit fillings for all three summands. This is the relation lattice
needed for the free and parity coefficient classification.

[`PrimeWeightedParityCoordinates.lean`](PrimeWeightedParityCoordinates.lean)
projects onto free coefficients on `m≤N<2m` and parity coefficients on
`2m≤N<3m` for odd faces omitting three. The projection is surjective and its
kernel is exactly the relation lattice above. Equivalently, a chain belongs
to that lattice precisely when it has half-height support and even coefficients
in the torsion window. This quotient calculation holds in every exterior
degree; its transport to actual augmented homology and height maps remains open.

[`PrimeWeightedAugmentedBoundary.lean`](PrimeWeightedAugmentedBoundary.lean)
proves the same boundary-lattice formula in empty degree, where coordinates
are the identity. A prime cone is injective on empty chains because coordinate
contraction recovers the chain. Thus the three-cone kernel contributes zero,
and the remaining low and doubled half-height summands give all boundaries.

## Mechanisms and tools

The desired chain is

`section → divisor → arithmetic count → effectivity → primitive sign`.

Riemann–Roch is useful only when its positive term produces a section. A
Bochner identity is useful only when its curvature sign has an arithmetic proof.
Window wall-crossing needs an index defined without the form and a proof of
invariance away from actual degeneracy. Weighted filtrations of the prime
complex must explain cancellation while retaining the large homology.

Concrete tools sought are a section space reading primitive classes, a divisor
map compatible with Hecke translates, vanishing in negative degree, an
arithmetic curvature term, a weighted prime-complex filtration, and an index
formula recovering predictor winding. Each tool must state its compatibility
with window restriction and growth of rank.

## Questions and open research topics

1. What arithmetic object is a section, and where are its zeros?
2. Which correspondences are irreducible, and what counts their intersections?
3. Can a homotopy invariant recover the window index without evaluating the
   Weil form?
4. Which weighted differential accounts for cancellation in the prime complex
   despite its linear Betti mass?
5. Do Hecke correspondences generate an ample cone, and in which topology?
6. How do section spaces glue across windows without assuming a global sign?

The filtration construction addresses part of question 4; it supplies no
cancellation estimate. All six construction questions remain open. No
independent global section construction or arithmetic curvature sign is claimed.

## Calibration and traps

The construction must reproduce Weil's proof on true curves step by step,
including the genus-one primitive correction. Finite curve windows and
Kloosterman fibres test compatibility with known arithmetic purity. Golden and
shifted data with nonnegative Tate coefficients must fail a proved arithmetic
requirement. Correct weights, integral traces and formal functional equations
cannot be the entire requirement.

Finite-rank carriers, separable assemblies, connected-link arguments and natural
Frobenius candidates have obstructions in the corpus. A proposed replacement
must specify which obstruction it escapes. Cutoff curvature is unbounded below;
discarding that term is not a Bochner proof. Two polar degrees do not determine
the source. A count defined from `Q`, or an assumed nonnegative intersection,
would insert the desired conclusion into the construction.

## Success and contribution criteria

Success means constructing the tools above, answering the five questions in
the motivating report, and recovering the curve proof with a valid integer
analogue. The limiting theory must have infinite rank and detect the full test.
Neither a finite positive window nor a new RH equivalence completes it.

A contribution must establish an unconditional theorem about a specified
arithmetic object, identify its gain over existing corpus results, and explain
its role in the construction. Obstructions must retain their strongest positive
survivor. Paper arguments require Lean formalization and transitive axiom audits;
open existence assertions remain explicit research questions.
