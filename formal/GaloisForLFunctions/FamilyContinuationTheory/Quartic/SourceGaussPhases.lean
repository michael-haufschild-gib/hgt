import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.CubicGaussReflection
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualGlobalArtinEpsilon

/-!
# Quartic reflection of the Q8 residue characters

The residue characters at five and forty-one already occur in the Q8 local
root numbers. Cubic-frequency reflection preserves each character up to the
phase `conj(G)² / q`. The phase has norm one; no choice of a square root or
orientation of a Gaussian prime is needed.
-/

noncomputable section

open scoped BigOperators
open RHTower GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.FamilyContinuationTheory.Quartic

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

private theorem inv_cube {F : Type*} [Field F] (χ : MulChar F ℂ)
    (hχ : χ ^ 4 = 1) : χ ^ 3 = χ⁻¹ :=
  eq_inv_of_mul_eq_one_left (by simpa only [← pow_succ] using hχ)

private theorem gauss_conj {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    star (gaussSum χ ψ) = χ (-1) * gaussSum χ⁻¹ ψ := by
  rw [star_gaussSum_eq]
  have hψ : ψ⁻¹ = ψ.mulShift (-1) := by ext x; simp
  rw [hψ]
  have h := gaussSum_mulShift_eq χ⁻¹ ψ (-1 : Fˣ)
  simpa only [Units.val_neg, Units.val_one, inv_inv] using h

private theorem reflection_eq {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ^ 4 = 1) (hχ1 : χ ≠ 1)
    (ψ : AddChar F ℂ) (u : F) :
    reflectedCubicGauss χ ψ u =
      ((Fintype.card F : ℂ)⁻¹ * star (gaussSum χ ψ) ^ 2) * χ u := by
  rw [reflectedCubicGauss_eq, if_neg hχ1, add_zero, inv_cube χ hχ,
    gaussSum_mulShift_with_zero_term, inv_inv]
  have hi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  rw [if_neg (fun h => hi h.2), add_zero,
    show -u = -1 * u by ring, map_mul]
  have hg := gauss_conj χ ψ
  rw [hg]
  ring

private theorem reflection_phase_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖(Fintype.card F : ℂ)⁻¹ * star (gaussSum χ ψ) ^ 2‖ = 1 := by
  have hg := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at hg
  have hn := congrArg norm hg
  simp only [norm_mul, norm_star, Complex.norm_natCast] at hn
  rw [norm_mul, norm_inv, norm_pow, norm_star, Complex.norm_natCast, pow_two, hn]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Cubic-frequency reflection of the actual quartic residue source at five. -/
theorem five_reflection (u : ZMod 5) :
    reflectedCubicGauss deningerQ8FiveResidueQuarticChar ZMod.stdAddChar u =
      ((5 : ℂ)⁻¹ * star (gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar) ^ 2) *
        deningerQ8FiveResidueQuarticChar u := by
  simpa only [ZMod.card, Nat.cast_ofNat] using reflection_eq deningerQ8FiveResidueQuarticChar
    deningerQ8FiveResidueQuarticChar_fourth_eq_one
    deningerQ8FiveResidueQuarticChar_ne_one ZMod.stdAddChar u

/-- The reflection coefficient at five has exact unit norm. -/
theorem five_reflection_phase_norm :
    ‖(5 : ℂ)⁻¹ * star (gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar) ^ 2‖ = 1 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using reflection_phase_norm deningerQ8FiveResidueQuarticChar
    deningerQ8FiveResidueQuarticChar_ne_one ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar 5)

private theorem fortyOne_fourth : deningerQ8FortyOneResidueQuarticChar ^ 4 = 1 := by
  rw [← deningerQ8FortyOneResidueQuarticChar_orderOf]
  exact pow_orderOf_eq_one _

private theorem fortyOne_ne_one : deningerQ8FortyOneResidueQuarticChar ≠ 1 := by
  intro h
  have ho := deningerQ8FortyOneResidueQuarticChar_orderOf
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- Cubic-frequency reflection of the actual quartic residue source at forty-one. -/
theorem fortyOne_reflection (u : ZMod 41) :
    reflectedCubicGauss deningerQ8FortyOneResidueQuarticChar ZMod.stdAddChar u =
      ((41 : ℂ)⁻¹ * star (gaussSum deningerQ8FortyOneResidueQuarticChar ZMod.stdAddChar) ^ 2) *
        deningerQ8FortyOneResidueQuarticChar u := by
  simpa only [ZMod.card, Nat.cast_ofNat] using reflection_eq deningerQ8FortyOneResidueQuarticChar
    fortyOne_fourth fortyOne_ne_one ZMod.stdAddChar u

/-- The reflection coefficient at forty-one has exact unit norm. -/
theorem fortyOne_reflection_phase_norm :
    ‖(41 : ℂ)⁻¹ * star (gaussSum deningerQ8FortyOneResidueQuarticChar ZMod.stdAddChar) ^ 2‖ = 1 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using reflection_phase_norm deningerQ8FortyOneResidueQuarticChar
    fortyOne_ne_one ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar 41)

end GaloisForLFunctions.FamilyContinuationTheory.Quartic
