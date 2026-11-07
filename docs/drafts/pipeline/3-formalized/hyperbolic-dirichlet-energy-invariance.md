# Hyperbolic invariance of scalar Dirichlet energy density

- **ID:** hyperbolic-dirichlet-energy-invariance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every `g∈SL₂(ℂ)` acts on positive-height Euclidean coordinates by a differentiable map whose derivative scales norms by the height ratio. Its pullback preserves height-squared scalar gradient energy.

Translations have identity derivative. Diagonal matrices have constant norm
scale `|b|²`. Inversion has derivative `‖p‖⁻²` times a reflection; the Weyl
reflection preserves norm. These factors satisfy
`‖Dg(p)u‖ p₂=‖u‖ (gp)₂`, and the chain rule preserves this identity under
composition. Bruhat decomposition covers every matrix.

A linear map scaling norms by `r>0` is `r` times a linear isometry. In
finite dimension that isometry is onto, so precomposition scales every
scalar functional norm by `r`. Thus
`p₂² ‖D(F∘g)(p)‖²=(gp)₂² ‖DF(gp)‖²`.
For invariant `F`, its scalar Dirichlet density is invariant.

Lean: `MetaplecticMobiusDescent/HyperbolicActionPreservesEnergy.lean`,
`hyperbolicDifferentialIsometry`, `hyperbolic_cotangent_energy_comp`, and
`euclideanScalarDirichletDensity_invariant`.
Direct source and transitive axiom audits passed; only `propext`,
`Classical.choice`, and `Quot.sound`.

Adapted from OpenAI `GaussSum/ReflectedBranches.lean`; no spectral input is assumed.
