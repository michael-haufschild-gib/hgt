# Effective geometry of the scaling surface

This programme seeks sections, divisors and intersection multiplicities on the
scaling surface of the integers. Its purpose is to supply the geometric reason
for effectivity, rather than rename the Weil quadratic form as a count.
The motivating specification is §2.11 of
[the first obstacles report](../../../docs/reports/review-0611/obstacles-summary.md).

The namespace is `GaloisForLFunctions.EffectiveScalingGeometry`;
the programme umbrella is `EffectiveScalingGeometry.lean`.

## Motivation and position

The shared quantitative target is **signed cancellation of the actual local
indices at the square-root scale**. [RIAC](../RenormalizedIntersectionArithmeticCounts/README.md)
constructs their sum `Σ_p index_p(N)=1−M(N)`. Sections, heights and topology
must provide a mechanism controlling that sum; the localization identity
and the size of individual contributions do not provide the cancellation.

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

The scaling-surface receiver in the existing corpus has two isotropic polar
directions with intersection one; its primitive defect is the Weil form.
Riemann–Roch and the equivalence between ample effectivity and RH identify the
required sign, but do not construct effective objects. Restricted-aperture
arithmetic sections have positive source floors; their omitted directions and
mixed intersections still require control. Finite curve windows provide a
calibration: the relevant Künneth positivity is equivalent to unitarity.

The following constructions supply actual filtered complexes, representatives,
relations and maps. They develop the prime-complex part of the programme.

### Prime-height geometry and the unweighted barcode

Let `Cₖ(N;R)` be the exterior lattice on prime faces of cardinality `k` and
product at most `N`, over a commutative ring `R`. Exterior degree zero is the
empty augmented face. Contraction by a vertex functional defines a boundary
on each cutoff; literal inclusions give the height functor.

For the augmentation `d(e_p)=1`, coning with two contracts the actual inclusion
`N→2N`. Cycles have height-preserving odd-face coordinates: an odd face `S`
represents the cycle `d(e₂∧S)`. Boundaries at `N` are exactly cycles at
`⌊N/2⌋`. Consequently actual augmented homology is naturally the arithmetic
interval system

`Hₖ(C(−);R) ≅ ⊕ₘ R[m,2m)`,

indexed by odd squarefree `m` with `ω(m)=k`. Height maps retain each coefficient
until its doubled birth height; the empty support contributes `[1,2)`.
[PrimeArithmeticPersistence.lean](PrimeArithmeticPersistence.lean) proves the
natural comparison with the original homology functor.

The geometric construction also controls the sphere maps themselves. A sphere
whose complementary facet remains outside the larger prime-two star survives
by a pointed homotopy to its unchanged inclusion; a facet entering the star
maps constantly to the basepoint. This is the actual inclusion law in
[PrimePersistenceIntervals.lean](PrimePersistenceIntervals.lean), compatible
with the classical prime-complex homotopy type and rank formulas of
[Björner](https://arxiv.org/abs/1101.5704).

These common logarithmic lifespans `log 2` carry no parity information by
themselves. Birth locations and exterior degrees retain the arithmetic data.
The companion programme's [component and core theorems](../HeightHomotopyArithmeticCounts/README.md)
sharpen the constraint: upper-half primes are isolated and individually fixed
by every identity-homotopic self-map, with count eventually exceeding `C√N`
for every constant `C`. The connected core retains the positive-dimensional
sphere summands and has reduced Euler characteristic
`−M(N)−#{N/2<p≤N}`. A cancellation mechanism must compare that core with the
isolated-prime contribution.

### Coefficient extension and complex Dirichlet weights

Canonical extension of integral chains to `R` preserves exterior faces,
boundaries, cones and cutoffs. On actual homology it sends `[c]` to `[c_R]`,
and the natural tensor comparison sends `r⊗[c]` to `r[c_R]`. Thus

`R ⊗[ℤ] Hₖ(C(N);ℤ) ≃ Hₖ(C(N);R)`

for the unweighted system over every commutative ring, without a flatness
assumption. The free surviving representatives provide the proof.
[PrimeHomologyBaseChange.lean](PrimeHomologyBaseChange.lean) identifies the
comparison with the actual chain-induced map;
[PrimeArithmeticBaseChange.lean](PrimeArithmeticBaseChange.lean) proves that
each squarefree-label coefficient is its canonical scalar image.

For complex Dirichlet weights `d_s(e_p)=p^(−s)`, multiplying vertex `p` by
`p^s` gives an inverse-compatible gauge preserving every cutoff. Contraction
naturality makes it an isomorphism of the actual chain and homology persistence
functors for every complex `s`.
[DirichletPersistenceEquivalence.lean](DirichletPersistenceEquivalence.lean)
formalizes this comparison. Analytic completion and norm control remain
separate questions.

### Integral prime weights and their torsion transitions

Give each prime vertex its integer value as boundary coefficient: `d(e_p)=p`.
The cone on `u=e₃−e₂` satisfies `dh+hd=id` and costs at most a factor of three
in product height. The actual inclusion `N→3N` is therefore nullhomotopic.
Over the integers this uniform dilation is sharp: the empty generator at
height one cannot be filled at height two.
[PrimeWeightedContraction.lean](PrimeWeightedContraction.lean) proves both facts.

In positive exterior degree, integral weighted cycles have a natural basis
on bounded odd faces.
The representative and inverse coordinate maps are

`P(y)=d(u∧y)`,  `Q(x)=O(x)+e₃∧δ₂(x)`.

Here `O` discards faces containing two and `δ₂` contracts that coordinate.
The cycle equation `d(Ox)+2δ₂x=0` puts `δ₂x` below `⌊N/3⌋`: the odd differential
has that height bound, and the integral coordinate cutoff is saturated.
Thus the correction in `Q` preserves height. This yields the actual natural
cycle equivalence in
[PrimeWeightedCycleCoordinates.lean](PrimeWeightedCycleCoordinates.lean).

In these coordinates, the boundary lattice in every augmented degree is

`Dₖ(N)=Oₖ(⌊N/3⌋)+2Oₖ(⌊N/2⌋)+(Oₖ(⌊N/2⌋)∩ker(e₃∧·))`.

The last summand consists exactly of faces containing three. Splitting a
filling into its odd and two-cone parts proves one containment; the Bézout cone
and two-cone fill the three summands. The empty-degree cone kernel is zero.
The [boundary-lattice theorem](../../../docs/drafts/pipeline/3-formalized/esg-prime-weighted-boundary-lattice.md)
records the exact relations, coefficient kernel and their formal declarations.

Actual integral homology is naturally the pair of finitely supported
coefficient spaces indexed as follows:

| Coefficients | Arithmetic label | Height window |
|---|---|---|
| `ℤ` | Odd squarefree `m`, `ω(m)=k` | `m≤N<2m` |
| `ℤ/2` | Squarefree `m` coprime to six, `ω(m)=k` | `2m≤N<3m` |

A height map retains the old free coefficients in the new free window. Its
new parity part is the restriction of `cast₂(old free)+old parity` to the new
torsion window. Hence a label coprime to six contributes
`ℤ[m,2m)→ℤ/2[2m,3m)→0`, with reduction modulo two at the transition.
An odd label containing three contributes only `ℤ[m,2m)`.
[PrimeWeightedArithmeticPersistence.lean](PrimeWeightedArithmeticPersistence.lean)
proves this for the original augmented homology functor, including its maps.

The canonical free quotient has no natural section already in empty degree:
the height-one generator becomes a nonzero parity class at height two while
its free quotient dies. Every lift has the same transition.
[PrimeWeightedPersistenceExtension.lean](PrimeWeightedPersistenceExtension.lean)
proves the nonsplitting for actual homology. Objectwise free-plus-torsion
decomposition therefore loses essential persistence information.

Weighted simplicial homology itself is classical; see
[Ren–Wu–Wu](https://arxiv.org/abs/1708.06722). The arithmetic contribution here
is the explicit integral prime-product classification and its actual height
maps. These theorems do not bound signed Euler cancellation or establish the
scaling-surface sign.

### A two-prime normal form over every coefficient ring

The full prime-valued chain persistence admits a natural isomorphism to the
complex whose only nonzero vertex weights are `d₀(e₂)=2`, `d₀(e₃)=3`.
This preserves each product cutoff and canonical extension from integer
coefficients to every commutative ring.
[PrimeTwoPrimeNormalForm.lean](PrimeTwoPrimeNormalForm.lean) constructs the
actual chain and homology persistence isomorphisms.

Let `ψ` retain the weights of primes above three and vanish at two and three.
With `t=ιψ` and `h=(e₃−e₂)∧`, Cartan's identities give
`dh+hd=1`, `th+ht=0` and `t²=0`. Consequently `H=ht` is square-zero,
and `1−H` intertwines `d₀=d−t` with `d`, with inverse `1+H`.
A nonzero tail deletion lowers product height enough to pay for either small
prime cone. This gives an all-ring chain comparison without dividing by two
or three. [PrimeTwoPrimeBlocks.lean](PrimeTwoPrimeBlocks.lean) transports the
actual face basis through this gauge, retaining exactly its product cutoffs.
Its boundary deletes only two and three. A large-prime core is closed, its
two small-prime cones have coefficients `2,3`, and their joint cone has
boundary `2e₃−3e₂`. [PrimeTwoPrimeFaces.lean](PrimeTwoPrimeFaces.lean) gives the
unique core/tag partition in each degree and cutoff: a core of product `m`
has tag births `m,2m,3m,6m` and degree increments `0,1,1,2`.
[PrimeTwoPrimeBlockCoordinates.lean](PrimeTwoPrimeBlockCoordinates.lean)
constructs the corresponding basis of the actual cutoff chain modules.
Literal height inclusion extends its coefficients by zero at newly born
labels. The original differential on these tagged basis vectors is exactly
the row `(2,3)` and column `(-3,2)`.

For one truncated block, the original categorical homology has exact
coefficient windows:

| Branch | First window | Second window | Death |
|---|---|---|---|
| Lower | `R` on `[m,2m)` | `R/2R` on `[2m,3m)` | `3m` |
| Upper | `Ann_R(2)` on `[2m,3m)` | `R` on `[3m,6m)` | `6m` |

The kernel of `(2,3)` is parametrized by `c↦(3c,−2c)`, with inverse
`(a,b)↦a+b`; the top column fills this kernel injectively. These identities
hold even over rings with torsion. The
[block homology comparison](PrimeTwoPrimeBlockHomology.lean) identifies
original cycle classes with their scalar cosets; the
[persistence comparison](PrimeTwoPrimeBlockPersistence.lean) is natural in
height. [The window equivalences](PrimeTwoPrimeBlockWindows.lean) identify
these quotients with the modules in the table.

The original complex has natural orthogonal core projections: they commute
with the boundary, and their finite sum recovers every chain.
[PrimeTwoPrimeHomologyCoreSum.lean](PrimeTwoPrimeHomologyCoreSum.lean)
identifies actual augmented homology with the direct sum of their ranges.
Each coordinate is the original core projection and retains the actual
height map. Coordinate extraction and realization recover that projection
in all three tagged chain degrees; their reverse composite is identity.
[PrimeTwoPrimeBlockRetractions.lean](PrimeTwoPrimeBlockRetractions.lean)
therefore realizes each upper block as an actual short-complex retract.
[PrimeTwoPrimeUpperCoreHomology.lean](PrimeTwoPrimeUpperCoreHomology.lean)
identifies the actual middle-degree range with the upper scalar quotient
through its original cycle classes.
[PrimeTwoPrimeCoreDegrees.lean](PrimeTwoPrimeCoreDegrees.lean) proves that
only bottom and middle degrees can contribute: no other tags occur, and
the top differential stays injective over every ring.
[PrimeTwoPrimeLowerCoreHomology.lean](PrimeTwoPrimeLowerCoreHomology.lean)
identifies the bottom range with the lower scalar quotient, including the
empty core.
[PrimeTwoPrimeCorePersistence.lean](PrimeTwoPrimeCorePersistence.lean) proves
that both quotient comparisons preserve every original height map.
[PrimeTwoPrimeBlockTransitions.lean](PrimeTwoPrimeBlockTransitions.lean)
identifies the lower transition as reduction `R→R/2R` and the upper transition
as inclusion `Ann_R(2)→R`; within each window, coefficients persist unchanged.
[PrimeTwoPrimeBinaryPersistence.lean](PrimeTwoPrimeBinaryPersistence.lean)
specializes actual core homology over `𝔽₂` to `[m,3m)` and `[2m,6m)` in
consecutive degrees. Internal maps retain their coefficient, including across
the intermediate tag births; both branches vanish outside these intervals.
[PrimeWeightedIntegralCoefficients.lean](PrimeWeightedIntegralCoefficients.lean)
constructs canonical integer extension on original cycles and homology,
commuting with core projections and height inclusions.
[PrimeTwoPrimeIntegralPersistence.lean](PrimeTwoPrimeIntegralPersistence.lean)
identifies both extracted quotient coefficients with their canonical scalar
images. Newly present annihilator classes over a target ring need not come
from integral homology.
[PrimeTwoPrimeArithmeticCores.lean](PrimeTwoPrimeArithmeticCores.lean) identifies
all core supports with squarefree integers coprime to six, preserving product
height and the number of prime factors. Together these comparisons classify
actual prime-weighted homology persistence over every commutative ring.

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
