# Bounded Lipschitz cutoffs preserve logarithmic energy

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every bounded real Lipschitz multiplier preserves the actual complete logarithmic Fourier domain. For `|χ|≤M` and Lipschitz constant `Λ`, its translation loss is at most `M‖τ_tu-u‖+Λ|t|‖u‖`.

## Proof

Subtract `χ(τ_tu-u)` from the translated cutoff loss. The remaining literal
coefficient is `(χ(x+t)-χ(x))u(x+t)`, whose L² norm is at most `Λ|t|‖u‖`.
The bounded multiplier controls the first term. Squaring gives a sum of twice
the two squared terms. The first is integrable against the exact Lévy density
by the source's finite energy; the second is integrable because
`ν(t)t²=(t/2)exp(-t)≤exp(-t/2)` for `t>0`.

The concrete cutoff `min(max(3-2x/a,0),1)` is one for `x≤a`, zero for
`x≥3a/2`, bounded between zero and one, and Lipschitz with constant `2/a`.

## Lean

Module `CanonicalSystemOfTheWindowTower/BoundedLipschitzCutoffsPreserveLogarithmicEnergy.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logarithmicCutoff_translation_loss_le`
- `hasLogarithmicEnergy_cutoff`
- `inner_logarithmicCutoffMultiplier`
- `logarithmicEndpointCutoff_eq_one`, `logarithmicEndpointCutoff_eq_zero`
- `logarithmicEndpointCutoff_lipschitz`

Production plain audit passed. Transitive axioms of the domain theorem are
exactly `[propext, Classical.choice, Quot.sound]`. Umbrella imports the module.
The literal complete-domain generator commutator remains a separate obligation.
