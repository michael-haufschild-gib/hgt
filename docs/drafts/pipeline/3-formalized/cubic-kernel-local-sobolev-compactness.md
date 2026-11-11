# Local Sobolev compactness on the cubic quotient

- **ID:** cubic-kernel-local-sobolev-compactness
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** Mass restriction to every compact subset of the actual cubic quotient is compact on its completed energy space.

For an injective positive-height cutoff, the Leibniz and measure estimates
bound localized Euclidean `H¹` norm by quotient mass plus Dirichlet energy.
Real Euclidean Rellich applies separately to real and imaginary parts;
continuous complex reassembly gives precompact localized masses. Density
extends compactness from smooth tests to the completed energy graph.

Cover a compact quotient set by finitely many chart regions `{χ>1/2}`.
On each, bounded hyperbolic density bounds mass by a constant times
localized Euclidean mass. The finite product of localizations is compact;
norm domination makes quotient mass restriction compact.

Lean: `MetaplecticMobiusDescent/CompactCubicEnergyLocalizations.lean` and
`CompactRestrictionOfTheCubicEnergy.lean`, namespace `CubicEisenstein`:

- `kernelEnergyLocalizeL2_isCompact`.
- `kernelCompact_mass_bound`.
- `kernelEnergyMassRestriction_isCompact`.

Both direct source audits and transitive theorem audits pass with only
`propext`, `Classical.choice`, and `Quot.sound`. The actual quotient volume,
smooth cutoff cover, Euclidean Rellich theorem, and localization estimates
are proved inputs. No compactness assumption remains in this endpoint.

[Exterior coercivity](cubic-quotient-exterior-coercivity.md) and a
[nonzero residual eigenvector](cubic-constant-term-nonvanishing.md) are formalized.
Gauss-coefficient identification and arithmetic descent remain open.
Adapted from OpenAI `CubicSieve/ReopenedFibers.lean` and
`Eisenstein/CompactEnergyFamilies.lean`. The final compact domination and
measurable restriction maps reuse corpus theorems.
