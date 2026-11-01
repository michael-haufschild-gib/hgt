# Finite differential equations over the actual theta–Gamma field

- **Status:** This coefficient-field shortcut is excluded; the broader arithmetic-period route remains open.
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

Zeta and every Dirichlet `L`-function admit no nonzero finite algebraic
differential equation over `ℂ(τ)⟨Γ,θ₂,θ₃,θ₄,E₂⟩`. The theta constants vary
with their modulus, and all functions are realized in the same meromorphic
field with ordinary complex differentiation.

**Mechanism:** The four actual theta/Eisenstein coordinates satisfy a closed
polynomial differential system. Their ordinary field is therefore closed under differentiation and
has finite ordinary transcendence degree. Every element is differentially algebraic.
Adjoining them cannot change the existing Gamma-field HT boundary.

**Strongest positive survivor:** Adjoining these concrete coefficients
preserves and reflects every indexed joint differential independence, for
all upper-end meromorphic observables. Their ordinary four-generator field
already contains every derivative. This supplies an exact finite model for
the coefficient field, not only a negative statement about zeta.

**New insight:** Variable theta coefficients do not unlock differential
relations when paired with Gamma. A surviving period construction must use
a relation outside this finite algebraic differential framework; the result
does not exclude special-value or q-difference relations.

**Proof and Lean status:** [Dependency-closed paper proof and theorem list](../3-formalized/jacobi-theta-gamma-differential-coefficient-boundary.md).
Module `ArithmeticHarmonicAnalysis/JacobiThetaGammaCoefficientBoundary.lean`;
main survivor `ModularThetaCoefficients.thetaGamma_differentialIndependent_iff`.
Direct source check and all six transitive axiom audits pass, using only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import is wired.
