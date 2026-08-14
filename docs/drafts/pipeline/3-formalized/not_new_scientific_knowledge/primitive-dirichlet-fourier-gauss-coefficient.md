# Primitive Dirichlet Fourier coefficient as a Gauss sum

## Status

- Pipeline: formalized in Lean 4
- Novelty: `[LITERATURE]`
- Proof status: `[PAPER-PROVED]`
- Lean status: `[LEAN-PROVED]`
- Role: primitive-conductor case of Kaczorowski–Perelli 2024, Lemma 1, equation (3.2)

## Exact claim

Let `χ` be a primitive Dirichlet character modulo `D`, let `a∈Z/DZ`, and define
`f_a(x)=e(-ax/D)` using the standard additive character. Then

`∑_{x mod D} χ⁻¹(x)e(-ax/D) = χ(a) overline(τ(χ))`,

where `τ(χ)=∑_{x mod D}χ(x)e(x/D)`.

## Proof

The negative shifted additive character satisfies

`e.mulShift(-a) = e⁻¹.mulShift(a)`.

Therefore the left side is `gaussSum χ⁻¹ (e⁻¹.mulShift a)`. Since conductor is invariant under
character inversion, `χ⁻¹` is primitive. The primitive Gauss-shift identity gives

`gaussSum χ⁻¹ (e⁻¹.mulShift a)
 = (χ⁻¹)⁻¹(a) gaussSum χ⁻¹ e⁻¹`.

Double character inversion gives `(χ⁻¹)⁻¹(a)=χ(a)`, while conjugation of Gauss sums gives
`gaussSum χ⁻¹ e⁻¹=overline(gaussSum χ e)`. Combining them proves the formula.

## Boundary

This is exactly the case `f_χ=D` of the published coefficient. For imprimitive `χ`, the remaining
factor is

`μ(D/f_χ) overline(χ*(D/f_χ))`,

and its proof requires the full induced-character Gauss-sum calculation. This card does not claim
that case.

## Lean realization

Module: `GaloisForLFunctions.RHTower.SelbergClass.DirichletFourierGauss`

Declaration: `RHTower.primitive_dirichletCharacterFourierCoeff_negativeAdditivePhase`.

Targeted source check and named-module build passed. `#print axioms` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.
