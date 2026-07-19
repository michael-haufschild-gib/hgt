# Uniform positive multiplier summability transfer

- **ID:** `uniform-positive-multiplier-summability-transfer`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / GENERAL LAW / PROP-INTERFACE CONSOLIDATION
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/PositiveSummabilityComparison.lean`
- **Statement:** For a nonnegative real family `f_i`, multiplication by any real weight `w_i`
  bounded uniformly between a positive constant and a finite constant preserves and reflects
  summability.  This one law subsumes the comparison cores of the canonical Möbius, every fixed
  continuous aperture, the first source tangent, and the reflected cubic innovation.

## General law

Let `i` range over an arbitrary type.  Suppose

```text
0 <= f_i,
0 < c <= w_i <= C.                                     (1)
```

Then

```text
Summable (w_i f_i) iff Summable (f_i).                 (2)
```

## Proof

If `sum_i w_i f_i` converges, nonnegativity and the lower bound in `(1)` give

```text
0 <= c f_i <= w_i f_i.                                 (3)
```

Comparison makes `sum_i c f_i` summable, and multiplication by the nonzero scalar `c` reflects
summability, proving the forward implication.

Conversely, if `sum_i f_i` converges, then `sum_i C f_i` converges.  The upper bound in `(1)` gives

```text
0 <= w_i f_i <= C f_i,                                 (4)
```

so comparison proves summability of the weighted family.  No countability, nonemptiness, or
strictness assumption on the upper constant is needed.

## Project specializations

Composing `(2)` with the already formalized all-log-moment damping law gives the RHTower
source-multiplier aperture law.  For every logarithmic order `m`, damping exponent `theta`, real
parameter `sigma`, and prime weight satisfying `(1)`,

```text
Summable_p [w_p |log p|^m p^(-theta) E_p(sigma)]
  iff sigma=1/2 or |2sigma-1|<theta.                    (5)
```

Indeed the bracketed family is `w_p` times the nonnegative base moment, so `(2)` removes `w_p`
and the all-moment law supplies the right side.  This corollary is unconditional: it requires no
sign hypothesis on `theta`, no countability hypothesis beyond the concrete prime index in the
specialization, and no separate positivity hypothesis on the upper constant.

The exact source/value factorizations already proved in RHTower have the form

```text
sourceEnergy_p = w_p * reflectedLogMoment_p,            (6)
```

with the following uniform bounds:

```text
canonical Möbius Schur metric:       1/27 <= w_p <= 1,
fixed continuous aperture a>0:      c_a  <= w_(a,p) <= 1,
zero-aperture tangent:               1/32 <= w_p <= 1,
cubic aperture pair a,b>0:           c_(a,b)/4 <= w_(a,b,p) <= c_(a,b).
```

Thus their exact aperture classifications are direct instances of `(5)`.  The new interface
removes four duplicated lower-scaling and upper-comparison proofs while preserving all
unconditional theorem statements.

The exported Lean interface is

```text
HTGeometry.summable_mul_iff_of_nonneg_of_uniform_pos_le_of_le.
RHTower.summable_mul_weightedPrimeClockReflectionLogMomentEnergy_iff.
RHTower.summable_mul_weightedPrimeClockReflectionEnergy_iff.
```

## Novelty and significance

The theorem is elementary comparison theory and is not new scientific knowledge.  Its value is
formal consolidation: it exposes the invariant law behind several independently developed
source/value bridges and makes later aperture families discharge the same Prop interface without
reproving summability plumbing.

## Gates

- [x] live corpus searched for an existing bounded-positive multiplier equivalence
- [x] dependency-closed paper proof
- [x] four current source/value instances identified
- [x] formalize the general law in HTGeometry
- [x] formalize the bounded-source all-moment aperture corollary in RHTower
- [x] refactor the four RHTower classification proofs to use the aperture corollary directly
- [x] exact deepest-leaf target build through all four specializations
- [x] representative axiom audit

## Log

- 2026-07-19 — extracted after the fixed, tangent, and cubic Möbius reflection classifications
  repeated the same two-sided positive comparison argument.
- 2026-07-19 — formalized the arbitrary-index law, rewrote the canonical Schur, fixed continuous,
  tangent, and cubic classifications as direct instances, and verified the deepest cubic target.
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the general law
  and all four classifications.
- 2026-07-19 — strengthened the interface to the exact bounded-source all-log-moment aperture law
  for arbitrary order and damping exponent.  All four classifications now consume this theorem
  directly after their exact value factorizations; the deepest cubic target rebuild passes.
