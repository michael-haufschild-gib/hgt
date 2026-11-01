# Algebraic differential–Mahler equations over theta–Gamma coefficients

- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Exact obstruction

For every positive real algebraic `q≠1`, no nonzero finite polynomial in
the actual functions `ζ(q^j s)` and their physical derivatives vanishes over
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩`. Both expanding and contracting orbits are covered.
The sole exceptional multiplier is `q=1`, which repeats one coordinate.

## Strongest positive survivor

All actual positive real algebraic dilates `ζ(rs)` are jointly differentially
independent over this concrete coefficient field. This classifies every
positive algebraic Mahler multiplier and controls arbitrary finite mixtures
of algebraic dilation parameters, beyond single orbits.

The decisive source law is exact frequency collision control: Baker linear
independence balances algebraic prime-log weights prime by prime. A target
on `D` distinct primes cannot come from fewer positive prime terms; every
`D`-term representation permutes the same prime–weight pairs. This isolates
the highest polynomial degree. Triangular positive-integer incidence and
prime-jet multilinear separation force that component to vanish. Physical
analytic continuation and Bohr recurrence then discharge Gamma separation;
theta differential-algebraic base change supplies the stated field.

## Certificate and scope

[Dependency-closed paper proof and exact Lean declarations](../3-formalized/algebraic-dilation-theta-gamma-independence.md).
Both obstruction and positive survivor are formalized in
`GammaAlgebraic.zetaDilation_differentialIndependent_thetaGamma`,
`GammaAlgebraic.mahlerZetaMero_differentialIndependent_iff`, and
`GammaAlgebraic.mahlerZeta_no_polynomial_relation`.
Twelve direct production checks passed without diagnostics; 78 transitive
axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
All twelve modules have umbrella imports.

Transcendental multipliers, arbitrary variable period coefficients,
special-value relations, and other nonlinear Böttcher realizations remain
outside this theorem. The broad paradigm is not retired. No RH conclusion follows.
