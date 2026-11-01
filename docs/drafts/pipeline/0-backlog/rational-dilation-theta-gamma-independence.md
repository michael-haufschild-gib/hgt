# Rational-dilation theta–Gamma independence

- **Stage:** 0-backlog
- **Type:** Conjecture
- **Parent:** [integer-dilation theorem](../3-formalized/integer-dilation-theta-gamma-independence.md).

## Target

All actual positive rational dilates `ζ(rs)`, `r∈ℚ_{>0}`, are jointly
differentially algebraically independent over the same concrete field
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩`. This would exclude finite differential–Mahler
relations for every positive rational `q≠1`, including contracting orbits.

## Mechanism to audit

Each finite rational set has a common denominator `D`. After Gamma
coefficient collapse on a sufficiently far-right physical line, scale the
constant relation by `s=Dz`; the zeta dilates then have distinct positive
integer multipliers and nonzero derivative factors. The Gamma coefficients
have already disappeared, so this argument does not require an automorphism
of the Gamma field under scaling.

The whole rational family has no single line of absolute convergence.
Formalization must reduce each polynomial to its finite variable support
before choosing the line. The existing generic Gamma separation theorem
requires one common line for its entire input family.

The corpus query surfaced the integer theorem and adjacent integer-dilation
independence, but no checked rational mixed-field theorem. Novelty and
paper dependency audits remain open; no proof certificate is claimed.
