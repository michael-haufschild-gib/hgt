# Ordinary dimensions cannot equal the real box defect

- **ID:** biarithmetic-literal-dimension-euler-characteristic
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Source:** report `docs/reports/review-2410/opus.md`, literal B1; [programme](../1-in-progress/biarithmetic-geometry-foundations.md).
- **Retired claim:** finite-dimensional ordinary cohomology satisfies `dim H⁰(s)-dim H¹(s)=E(s)` for every nonnegative aperture.

## Killing theorem

At `s=log(3/2)`, the actual box defect is `1/2+log(3/2)`, strictly between zero and one.
It cannot be the difference of two natural-number dimensions. Lean declaration
`BiarithmeticGeometry.no_dimension_model_for_boxDefect` proves the obstruction without an
analytic hypothesis.

## Positive survivor

For `N=floor(exp s)≥1`, let `Q_N=lcm(1,...,N)/N`. This is a positive integer, and the finite
cyclic group `Z/Q_N Z` gives the exact formula

`E(s)=(N-1)-log #(Z/Q_N Z)+(exp(s)-N)+(s-log N)`.

The strongest replacement covers every nonnegative aperture, separating integer degree,
logarithmic torsion, and continuous evolution. It improves the integer-horizon identity by
retaining the full between-horizon remainder. Its dependency-closed paper proof and Lean
formalization are recorded in [Arithmetic degree and exact horizon torsion](../3-formalized/biarithmetic-degree-and-horizon-torsion.md).

Lean module: `GaloisForLFunctions/BiarithmeticGeometry/ArithmeticEulerCharacteristic.lean`.
Main declarations: `boxDefect_eq_degree_sub_log_card`, `boxDefect_all_apertures`.
Direct leaf check passed. Transitive axiom audits of the killing theorem and both positive
identities report only `propext`, `Classical.choice`, `Quot.sound`.

## Scope and insight

Real arithmetic mass and integer cohomological index must be distinct invariants. Arithmetic
degree is a type-correct replacement; calling a real mass a dimension cannot repair B1.
The least-common-multiple identity is classical, so no novelty is claimed for that identity.
The general payment-cohomology programme remains open: this result does not construct a
payment complex, restriction maps, Mayer–Vietoris, duality, or certified-window vanishing.
