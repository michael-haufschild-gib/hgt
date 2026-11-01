# Rational-dilation theta–Gamma independence

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [integer-dilation theorem](../3-formalized/integer-dilation-theta-gamma-independence.md).

## Target

All actual positive rational dilates `ζ(rs)`, `r∈ℚ_{>0}`, are jointly
differentially algebraically independent over the same concrete field
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩`. This would exclude finite differential–Mahler
relations for every positive rational `q≠1`, including contracting orbits.

## Finite-family mechanism

For a finite set of positive rationals, choose a positive common denominator
`D` and distinct positive integers `m_r=Dr`. Use the physical line `Re s=2D`.
For every jet order `k`, the chain rule gives

`(ζ(rs))^(k)(2D+it)=D^(−k)(ζ(m_r z))^(k)(2+i t/D)`.

The checked integer theorem supplies continuity, almost periodicity, and
algebraic independence of all integer-dilation jets on `Re z=2`.
Invertible rescaling of the real line and the nonzero factors `D^(−k)`
transfer these three properties to the chosen rational family on `Re s=2D`.
Apply `GammaJoint.algebraicIndependent_gamma_of_line` to that finite dilation
family and all its jets; the Gamma coefficients remain in the physical
variable throughout. The checked theta base-change equivalence then applies.

Algebraic relations involve only finitely many dilation indices, so finite
restriction proves independence of the full rational family. There is no
single line of absolute convergence for all positive rationals, and none
is required. The proof needs no scaling automorphism of the Gamma field.

Checked corpus inputs also include the finite-subfamily algebraic-independence
theorem and the finite common-denominator theorem.

Lean obligations: positive common-denominator realization, exact jet reparametrization,
independence under invertible line reparametrization, and passage from finite
dilation families to all positive rational dilates.

The corpus query surfaced the integer theorem and adjacent integer-dilation
independence, but no checked rational mixed-field theorem. Novelty and
paper dependency audits remain open; no proof certificate is claimed.
