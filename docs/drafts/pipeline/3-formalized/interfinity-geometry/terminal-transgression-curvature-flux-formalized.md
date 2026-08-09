# Terminal transgression curvature flux — formalized

- **ID:** `terminal-transgression-curvature-flux-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `terminal-transgression-curvature-flux.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/TerminalTransgression.lean` | terminal data, curvature, the Bianchi identity, the residue and its flux laws |
| `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/TerminalResidueModels.lean` | the free affine model with arbitrary residues and the parity model with curved residue `2` |

## Audited declarations

Namespace `GaloisForLFunctions.HTGeometry.Interfinity`, section `TerminalDatum` where applicable.

- `bianchi` — the Bianchi identity for the curvature of an arbitrary one-cochain;
- `tendsto_residue_curved`, `tendsto_residue_flat` — the residue is the limit of the ordered
  commutator along the terminal ray, in the curved and the cocycle case;
- `tendsto_curvature_flux` — the curved bulk-boundary flux law;
- `radial_coboundary`, `tendsto_radial_primitive`, `stable_primitive_unique` — a radially flat,
  radially convergent cochain is a coboundary with a unique stable radial primitive;
- `residue_eq_zero_of_eventually_commutes` — cofinal-normalizer rigidity;
- `freeCochain_residue_gen` — free-source universality: the terminal residue takes arbitrary
  prescribed values on the generators of `Monoid.Coprod (Multiplicative ℝ≥0) (FreeMonoid (Fin n))`;
- `parityCochain_residue_involution`, `parityCochain_flux`, `parityCochain_not_isCocycle` — an
  explicit parity model whose curved residue is `2`, so the curved law is not vacuous.

Every listed declaration is unconditional: `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry.InterfinityGeometry
```

## Boundary

The terminal datum is packaged as a structure carrying the ray, the time character and the stable
subspace; every field is discharged at instantiation by the two explicit models, so no hypothesis
is left standing.
