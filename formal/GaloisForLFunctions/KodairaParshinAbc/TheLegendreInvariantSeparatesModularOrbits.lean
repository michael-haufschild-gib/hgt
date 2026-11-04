import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfTheArakelovCoordinate
import GaloisForLFunctions.RHTower.ModularLambdaOrbitSeparation

/-!
# The Legendre invariant separates modular orbits

The level-one modular function `J(λ(τ))` built from the Legendre invariant
`J(λ) = 256 (λ² - λ + 1)³ / (λ²(λ - 1)²)` takes equal values exactly on `SL(2, ℤ)`-orbits:

  `J(λ(τ₁)) = J(λ(τ₂)) ⟺ τ₁ ∈ SL(2, ℤ) · τ₂`.

Three inputs combine.  The fibres of `J` are the anharmonic orbits
(`legendreInvariant_eq_iff`); the six words `1, S, T, ST, TS, STS` move `λ(τ)` through its whole
anharmonic orbit (`λ ↦ λ, 1-λ, λ/(λ-1), 1/(1-λ), (λ-1)/λ, 1/λ`); and `λ` separates `Γ(2)`-orbits
(`RHTower.ModularLambdaWinding.exists_gamma2_smul_eq_of_modularLambda_eq`).  So `J ∘ λ` is
injective on `SL(2, ℤ) \ ℍ`: it is a coordinate on the modular curve of level one, as the
`j`-invariant must be.
-/

noncomputable section

open Complex UpperHalfPlane Bottcher
open scoped MatrixGroups

namespace GaloisForLFunctions.KodairaParshinAbc

theorem modularLambda_S_smul (τ : ℍ) :
    modularLambda ((ModularGroup.S • τ : ℍ) : ℂ) = 1 - modularLambda (τ : ℂ) :=
  congrArg Subtype.val (lambdaPunct_smul_S τ)

theorem modularLambda_T_smul (τ : ℍ) :
    modularLambda ((ModularGroup.T • τ : ℍ) : ℂ) =
      modularLambda (τ : ℂ) / (modularLambda (τ : ℂ) - 1) :=
  congrArg Subtype.val (lambdaPunct_smul_T τ)

/-- **The six words realise the anharmonic orbit**: every value in the orbit of `λ(τ)` is `λ(r τ)`
for one of `r = 1, S, T, ST, TS, STS`. -/
theorem exists_word_modularLambda_eq (τ : ℍ) {y : ℂ}
    (hy : y = modularLambda (τ : ℂ) ∨ y = 1 - modularLambda (τ : ℂ) ∨
      y = (modularLambda (τ : ℂ))⁻¹ ∨ y = (1 - modularLambda (τ : ℂ))⁻¹ ∨
      y = modularLambda (τ : ℂ) / (modularLambda (τ : ℂ) - 1) ∨
      y = (modularLambda (τ : ℂ) - 1) / modularLambda (τ : ℂ)) :
    ∃ r : SL(2, ℤ), modularLambda ((r • τ : ℍ) : ℂ) = y := by
  obtain ⟨h0, h1⟩ := modularLambda_ne_zero_ne_one τ
  set x := modularLambda (τ : ℂ) with hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hx0 : (1 - x) - 1 ≠ 0 := by rw [sub_sub_cancel_left]; exact neg_ne_zero.mpr h0
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by rw [one_smul]⟩
  · exact ⟨ModularGroup.S, modularLambda_S_smul τ⟩
  · refine ⟨ModularGroup.S * ModularGroup.T * ModularGroup.S, ?_⟩
    rw [mul_smul, mul_smul, modularLambda_S_smul, modularLambda_T_smul, modularLambda_S_smul,
      ← hx]
    field_simp
    ring
  · refine ⟨ModularGroup.S * ModularGroup.T, ?_⟩
    rw [mul_smul, modularLambda_S_smul, modularLambda_T_smul, ← hx]
    field_simp
    ring
  · exact ⟨ModularGroup.T, modularLambda_T_smul τ⟩
  · refine ⟨ModularGroup.T * ModularGroup.S, ?_⟩
    rw [mul_smul, modularLambda_T_smul, modularLambda_S_smul, ← hx]
    field_simp
    ring

/-- **`J ∘ λ` separates `SL(2, ℤ)`-orbits**: `J(λ(τ₁)) = J(λ(τ₂))` iff `τ₁ = g τ₂` for some
`g ∈ SL(2, ℤ)`. -/
theorem lambdaInvariant_eq_iff (τ₁ τ₂ : ℍ) :
    lambdaInvariant τ₁ = lambdaInvariant τ₂ ↔ ∃ g : SL(2, ℤ), g • τ₂ = τ₁ := by
  constructor
  · intro h
    obtain ⟨hx0, hx1⟩ := modularLambda_ne_zero_ne_one τ₂
    obtain ⟨hy0, hy1⟩ := modularLambda_ne_zero_ne_one τ₁
    have horb := (legendreInvariant_eq_iff hx0 hx1 hy0 hy1).mp h
    obtain ⟨r, hr⟩ := exists_word_modularLambda_eq τ₂ horb
    obtain ⟨γ, -, hγ⟩ :=
      RHTower.ModularLambdaWinding.exists_gamma2_smul_eq_of_modularLambda_eq
        (η₁ := τ₁) (η₂ := r • τ₂) hr.symm
    exact ⟨γ * r, by rw [mul_smul, hγ]⟩
  · rintro ⟨g, rfl⟩
    exact lambdaInvariant_smul g τ₂

end GaloisForLFunctions.KodairaParshinAbc
