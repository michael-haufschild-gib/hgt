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

This is a geometric interval law for inclusion maps. A separate persistent
homology object and barcode isomorphism are not constructed here. The common
logarithmic lifespan `log 2` gives no parity information to lifespan-only
weights; birth locations and sphere dimensions retain arithmetic information.
The law therefore identifies what a richer weighting must use without
claiming an Euler-cancellation bound.

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
