# The variational cubic quotient Laplacian

- **ID:** cubic-quotient-variational-laplacian
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** The actual quotient Dirichlet energy defines a closed, densely defined, nonnegative self-adjoint Laplacian on quotient `L²`.

Let `M` be the faithful dense mass embedding of the completed energy graph.
Its adjoint `M*` uniquely solves the coercive weak equation because the
energy inner product is mass pairing plus gradient pairing. The resolvent
`R=MM*` is positive, self-adjoint, injective, and has dense range.
Define the Laplacian graph by `R(u+f)=u`. Injectivity makes this a graph;
continuity makes it closed. Its domain contains the dense range of `R`.
The weak equation gives symmetry and nonnegativity. Pairing an adjoint
graph vector against all resolvent vectors proves self-adjointness.

Lean: `MetaplecticMobiusDescent/TheCubicVariationalLaplacian.lean`,
namespace `CubicEisenstein`:

- `kernelVariationalSolution_existsUnique`.
- `kernelVariationalResolvent_injective`.
- `kernelEnergyLaplacian_closed`, `kernelEnergyLaplacian_dense_domain`.
- `kernelEnergyLaplacian_nonnegative`, `kernelEnergyLaplacian_selfAdjoint`.

Direct source and transitive audits pass with only `propext`,
`Classical.choice`, and `Quot.sound`. No analytic property is assumed.
The [coordinate Green identity](cubic-quotient-green-identity.md) is formalized;
[exterior coercivity](cubic-quotient-exterior-coercivity.md) is also formalized.
Adapted from OpenAI `Eisenstein/VariationalLaplacian.lean`.
