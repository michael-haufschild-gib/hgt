# Green identity for the actual cubic quotient Laplacian

- **ID:** cubic-quotient-green-identity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [exterior coercivity](../1-in-progress/cubic-quotient-exterior-coercivity.md)
- **Statement:** The quotient Dirichlet form satisfies Green's identity for the positive coordinate expression `−v²(∂ₓ²+∂ᵧ²+∂ᵥ²)+v∂ᵥ`. A square-integrable global coordinate equation represents the actual variational Laplacian graph and action.

In an injective chart, extend compact smooth tests by zero and integrate
Schwartz derivatives against density `v⁻³`. Differentiating `v⁻¹` in the
energy pairing supplies the vertical first derivative. Exact restricted
measure transport gives the quotient chart identity. A finite smooth
partition subordinate to injective chart cores preserves test support;
summing gives the global identity even when the differential equation
holds only on that support. Density of the smooth energy core extends
the pairing to every energy vector. Uniqueness of the coercive weak
solution then identifies the variational operator graph and action.

Lean: `MetaplecticMobiusDescent/GreenIdentityOnTheCubicQuotient.lean`
`TheCubicLaplacianHasItsCoordinateExpression.lean`, and
`HyperbolicAxisLaplacian.lean`, namespace
`CubicEisenstein`:

- `upperHyperbolic_green`, `kernelDirichletForm_eq_chart_laplacian`.
- `kernelDirichletForm_supported_equation`.
- `kernelEnergyLaplacian_graph_of_coordinate`.
- `kernelEnergyLaplacian_apply_of_coordinate`.
- `positiveEuclideanLaplacian_eq_axis` identifies the sign of iterated axis derivatives.

Direct source and transitive audits pass with only `propext`,
`Classical.choice`, and `Quot.sound`. The conditional graph representation
does not supply an unproved coordinate equation. The actual cusp barrier
and exterior coercivity remain open. Adapted from OpenAI
`CubicSieve/RadialProfiles.lean`, `Eisenstein/CoordinateLaplacian.lean`,
and `MeanSquare/UnitRows.lean`.
