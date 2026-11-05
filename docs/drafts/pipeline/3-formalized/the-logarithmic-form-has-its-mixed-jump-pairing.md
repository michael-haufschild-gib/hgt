# The logarithmic form has its mixed jump pairing

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** On the complete whole-line logarithmic energy domain, `q(f,g)=⟨f,g⟩+∫₀∞ν(t)⟨τ_tf-f,τ_tg-g⟩dt`, with an absolutely convergent mixed integral. Physical translation preserves domain and form.

## Proof

The actual Fourier factor identifies the energy domain with the range of causal
convolution. In these coordinates the form is the ordinary L² inner product.
Complex polarization of the proved extended jump-energy identity gives the
mixed integral and its absolute convergence. Translations commute with every
translation loss and act unitarily, proving domain and form invariance.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicFormHasItsMixedJumpPairing.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `hasLogarithmicEnergy_iff_range_convolution`
- `integrable_logarithmicJumpMixed`
- `logarithmicFullForm_eq_inner_add_jump`
- `hasLogarithmicEnergy_translation`
- `logarithmicFullForm_translation`

Transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.
Production plain audit passed. Umbrella imports the module.
