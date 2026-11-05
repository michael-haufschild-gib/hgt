# The logarithmic energy has its literal jump form

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every whole-line L² source, the extended energy `∫₀∞ν(t)‖τ_tu-u‖²dt`, `ν(t)=exp(-t)/(2t)`, equals `∫(Ψ(2πξ)-1)|û(ξ)|²dξ`. Finiteness is exactly the actual logarithmic multiplier domain.

## Proof

Plancherel identifies each squared translation loss with its cosine-defect
integral. The literal Abel identity gives
`∫₀∞ν(t)(2-2cos(2πtξ))dt=Ψ(2πξ)-1`. Positivity and joint measurability
permit Tonelli without a finite-energy premise. Ordinary L² mass is finite;
adding it identifies finite jump energy with integrability of
`Ψ(2πξ)|û(ξ)|²`, the actual factor graph condition.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicEnergyHasItsLiteralJumpForm.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logarithmicJumpEnergyL_eq_fourier`
- `hasLogarithmicEnergy_iff_jumpEnergy_ne_top`
- `hasLogarithmicEnergy_iff_integrable_jump`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Umbrella imports the module.
