# Dirichlet form on the actual cubic quotient

- **ID:** cubic-quotient-dirichlet-form
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Compact smooth tests on the actual cubic quotient carry a nonnegative Hermitian Dirichlet form obtained by integrating their hyperbolic gradient pairing.

Pull a test to upper half-space. Möbius cotangent invariance makes
`v²(|∇ Re f|²+|∇ Im f|²)` invariant under the arithmetic kernel.
Its descended density is continuous and supported in the test's compact
support, hence integrable. Polarization agrees pointwise with the complex
inner product of the three height-weighted partial derivatives. Integration
therefore gives sesquilinearity, conjugate symmetry, and nonnegativity.

Lean: `MetaplecticMobiusDescent/TheCubicDirichletForm.lean`,
`kernelTestEnergyDensity_invariant`, `kernelQuotientEnergyDensity_integrable`,
`kernelDirichletForm_add_right`, `kernelDirichletForm_smul_right`,
`kernelDirichletForm_conj`, and `kernelDirichletForm_self_nonneg`.
Transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

Adapted from OpenAI `GaussSum/ReflectedBranches.lean` and
`Eisenstein/DirichletForm.lean`. Closure of the gradient and compact-core
restriction remain separate analytic inputs.
