# Integer differential–Mahler equations over theta–Gamma coefficients

- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Exact obstruction

Fix an integer `q≥2`. No nonzero finite polynomial in the functions
`ζ(q^j s)` and their derivatives vanishes with coefficients in the concrete
field `ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩`. This excludes the proposed nonlinear
algebraic differential–Mahler equation in this coefficient class.

It does not exclude arbitrary variable period coefficients, special-value
relations, noninteger dilation parameters, or an independently specified
Böttcher realization outside this class.

## Positive survivor

All positive integer dilates `ζ(ms)` are jointly differentially algebraically
independent over the same theta–Gamma field. The theorem treats every finite
mixed jet polynomial, not only one function or one dilation orbit.

The new separation mechanism upgrades constant-coefficient independence
of almost-periodic line functions to independence over the actual Gamma
field. Dominant Gamma asymptotics and simultaneous recurrence discharge
all coefficient ratios. Actual analytic rotation, including its jet factors,
connects the physical zeta functions to the independent arithmetic carriers.

## Certificate

[Paper proof and exact Lean declarations](../3-formalized/integer-dilation-theta-gamma-independence.md).
The production module passed its direct Lean check without diagnostics;
all five transitive axiom audits use only `propext`, `Classical.choice`,
`Quot.sound`. Both the obstruction and the stronger positive survivor are
formalized, with the actual analytic representatives identified.
