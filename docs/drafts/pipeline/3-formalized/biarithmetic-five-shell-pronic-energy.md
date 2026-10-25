# Shell energy equals bounded ordinary pronic energy

- **ID:** biarithmetic-five-shell-pronic-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Intrinsic golden module](../1-in-progress/biarithmetic-intrinsic-golden-module.md)
- **Statement:** A sequence extended constantly on each positive base-five shell has bounded pronic norms at every integer cutoff exactly when its weighted shell square sum is finite. Every complete signed block pairing has the exact factor `(4/5)5^(-M)`.

The reciprocal pronic weights telescope on each shell. Complete prefixes
therefore equal four fifths of the corresponding shell energy. Nonnegative
cell energies make the ordinary prefix energy monotone; enclosing any
cutoff in its next complete shell controls every partial final block.
Conversely, a common cutoff bound controls every finite shell sum.

Lean: `BiarithmeticGeometry/FiveShellPronicEnergy.lean`.
Audited declarations: `fiveShell_pronicBlock_pairing`,
`fiveShellPronicEnergyTo_complete`, `bounded_fiveShellPronicEnergy_iff`,
and `bounded_pronicNorm_fiveShellRow_iff`.

- [x] Direct check: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/FiveShellPronicEnergy.lean`.
- [x] All four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Default proof limits; umbrella import wired; umbrella not compiled.

This identifies the norms and domains. The intrinsic source decomposition,
shift identities, and tangent classification are separate obligations.
