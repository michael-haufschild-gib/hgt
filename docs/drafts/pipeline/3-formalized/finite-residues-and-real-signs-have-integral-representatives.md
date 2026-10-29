# Finite residues and real signs have integral representatives

- **ID:** hecke-ray-reduction-surjective
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke L-functions and class field theory](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL1 and HL7
- **Statement:** for every number field `K`, modulus `𝔪`, invertible residue `ρ mod 𝔪.fin`,
  and sign pattern `σ` on `𝔪.inf`, there is a nonzero integral `γ` with residue `ρ` and signs `σ`.
  Consequently `rayHom 𝔪` is surjective onto the full residue/sign product.

## Paper proof

The common ray-class density is positive. Its formula is a finite cardinal times the volume
of the positive sign sector, divided by an explicit scalar. If that volume were zero, the
density would be zero. Hence the volume is positive. Sign flips preserve volume, so every
sign sector has the same positive volume `V`.

Let `Λ` be a full lattice in the mixed embedding space and `v` any translation. The existing
translated lattice count supplies `C` such that, for `T ≥ 1`,

`|#((v + T^(1/n) Y_σ) ∩ Λ) covol(Λ) − TV| ≤ C T^(1−1/n)`.

Since `n = [K:ℚ] > 0`, choose `T ≥ 1` with `C T^(−1/n) < V`. If the intersection were empty,
the bound would imply `TV ≤ C T^(1−1/n)`, contradicting this choice. Thus every translate
meets some positive dilate of every sign sector.

Apply this to the lattice of `𝔪.fin` and the translation by the negative mixed embedding of
an integral representative of `ρ`. The previously proved `conePoints_eq_image`, with the
unit ideal, identifies a resulting point with an integral `γ` having residue `ρ` and signs
`σ`. This identity accepts arbitrary residue/sign data; it does not assume those data lie in
`rayHom.range`. Membership in the fundamental cone makes `γ` nonzero. Its invertible residue
makes it prime to the modulus. The explicit reduction and sign identities then give
`rayHom γ = (ρ,σ)`.

No approximation theorem or reciprocity assumption is introduced. The inputs are the already
formalized signed lattice counts and positive ray-class density.

## Lean declarations

In [EveryRayResidueAndSignHasAnIntegralRepresentative.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/EveryRayResidueAndSignHasAnIntegralRepresentative.lean):

- `signedNormBall_volume_pos`
- `exists_lattice_point_in_signedNormBall_coset`
- `exists_integral_residue_sign`
- `rayHom_surjective`

## Validation

- Proof check and olean generation pass. The olean is needed by the character-decomposition module.
- Transitive axiom audits of the positive-volume, integral-representative, and surjectivity
  results use only `propext`, `Classical.choice`, and `Quot.sound`.
- Imported by `HeckeLFunctions.lean`; no umbrella is compiled.
- Final direct source audit with `lake --old env lean` passes without warnings.

## Consequence for the remaining programme

The principal ray-class map can now be extended from `rayHom.range` to the full product.
This allows a Hecke character's finite residue component and real-place parities to be
constructed independently. Full continuation and the functional equation remain open.
