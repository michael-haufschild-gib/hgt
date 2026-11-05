# The logarithmic cutoff kernel is bounded

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For a real Lipschitz function `χ` with constant `Λ`, the literal kernel `Kχ(x,y)=(χ(x)-χ(y))exp(-|x-y|)/(2|x-y|)` defines a Schur operator of norm at most `Λ`. If `|f|≤C` almost everywhere, then `|Kχf|≤ΛC` almost everywhere.

## Proof

Lipschitz cancellation gives `|Kχ(x,y)|≤(Λ/2)exp(-|x-y|)`, including
the totalized diagonal value zero. The exponential has integral two, so
both Schur bounds are `Λ`. The same integrable majorant bounds the literal
operator integral against an essentially bounded L² source.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicCutoffCommutatorHasABoundedKernel.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `norm_logarithmicCutoffKernel_le`
- `logarithmicCutoffSchurKernel`
- `norm_logarithmicCutoffSchurKernel_op_le`
- `logarithmicCutoffSchurKernel_preserves_boundedness`

The full-domain commutator identity is a separate theorem.

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Umbrella imports the module.
