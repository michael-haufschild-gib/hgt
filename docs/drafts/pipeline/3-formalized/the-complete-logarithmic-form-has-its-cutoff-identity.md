# The complete logarithmic form has its cutoff identity

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every bounded real Lipschitz cutoff and every pair in the complete logarithmic energy domain, `q(v,χu)-q(χv,u)=⟨v,Kχu⟩`, where `Kχ(x,y)=(χ(x)-χ(y))exp(-|x-y|)/(2|x-y|)`.

## Proof

Put `C_t=Pχτ_t-τ_tPχ`. Unitarity of translation and symmetry of real
multiplication turn the difference of mixed translation losses into
`⟨v,(C_t+C_-t)u⟩`. The literal Schur pairing is absolutely integrable.
The measure-preserving shear `(x,t)↦(x,x+t)` therefore identifies it with
`∫ℝν(|t|)⟨v,C_tu⟩dt`. Splitting positive and negative lags gives precisely
the mixed jump-form difference. Cutoff-domain preservation admits all vectors
used in this calculation.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicFormHasItsCutoffIdentity.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logarithmicCutoffTranslationCommutator_coeFn`
- `logarithmicFullForm_cutoff_identity`

Transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.
Production plain audit passed. Umbrella imports the module.
