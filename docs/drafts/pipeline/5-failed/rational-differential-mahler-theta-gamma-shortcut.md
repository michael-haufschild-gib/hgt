# Rational differential–Mahler equations over theta–Gamma coefficients

- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Exact obstruction

For every positive rational `q≠1`, no nonzero finite polynomial in
`ζ(q^j s)` and its physical derivatives vanishes over
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩`. This excludes the specified differential–Mahler
realization for both expanding and contracting rational orbits.

The sole degenerate positive rational multiplier is `q=1`, where all orbit
coordinates coincide. That repetition supplies no zero-location equation.

## Positive survivor

The entire family `ζ(rs)`, `r∈ℚ_{>0}`, is jointly differentially independent
over the concrete theta–Gamma field. The exact multiplier classification
is stronger than exclusion of any single proposed relation.

A finite mixed jet packet has one positive common denominator `D`.
Its line `Re s=2D` and exact nonzero chain factors transport the proved
integer independence. Gamma coefficient separation applies on that line
without changing the coefficient field's physical variable. Finite-subfamily
independence handles arbitrarily small dilation parameters.

## Certificate and scope

[Dependency-closed paper proof and Lean declarations](../3-formalized/rational-dilation-theta-gamma-independence.md).
Both obstruction and positive survivor are formalized. The direct production
check has no diagnostics; all seven transitive axiom audits use only
`propext`, `Classical.choice`, `Quot.sound`.

[The positive algebraic extension](algebraic-differential-mahler-theta-gamma-shortcut.md)
now covers irrational algebraic dilations. Transcendental multipliers,
arbitrary variable period coefficients, special-value relations, and other
nonlinear Böttcher realizations remain outside these results. The broad
paradigm is not retired; no RH conclusion follows.
