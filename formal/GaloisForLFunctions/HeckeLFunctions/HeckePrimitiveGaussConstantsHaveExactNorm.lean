import GaloisForLFunctions.HeckeLFunctions.HeckeFourierSupportIsIdealCoprimality

/-!
# Primitive Hecke Gauss constants have exact norm

A coprime representative of the inverse trace-dual class supplies a
nonzero reference frequency and its integral ideal. Multiply its actual
finite Fourier coefficient by the real sign character and that ideal's
Hecke value. Both correction factors have norm one, so the corrected
Gauss constant has squared norm equal to the finite conductor norm.
Dividing by its positive square root gives a constant on the unit circle.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- A nonzero primitive trace frequency obtained from an actual coprime ordinary-class representative. -/
def heckeReferenceFrequency :
    FractionalIdeal.dual ℤ ℚ ((𝔪.fin * ⊤ : Ideal (𝓞 K)) : FI) :=
  (exists_heckeDualFrequencyIdeal_coprime 𝔪 (b := ⊤) (by simp)).choose

theorem heckeReferenceFrequency_ne_zero : (heckeReferenceFrequency 𝔪 : K) ≠ 0 :=
  (exists_heckeDualFrequencyIdeal_coprime 𝔪 (b := ⊤) (by simp)).choose_spec.1

/-- The integral ideal paired with the chosen primitive trace frequency. -/
def heckeReferenceIdeal : Ideal (𝓞 K) :=
  heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) (heckeReferenceFrequency 𝔪)

theorem heckeReferenceIdeal_coprime : heckeReferenceIdeal 𝔪 ⊔ 𝔪.fin = ⊤ :=
  (exists_heckeDualFrequencyIdeal_coprime 𝔪 (b := ⊤) (by simp)).choose_spec.2

theorem heckeReferenceIdeal_ne_bot : heckeReferenceIdeal 𝔪 ≠ ⊥ := by
  rw [heckeReferenceIdeal, ne_eq, heckeDualFrequencyIdeal_eq_bot_iff]
  exact heckeReferenceFrequency_ne_zero 𝔪

/-- The class and sign correction of the actual primitive finite Gauss coefficient. -/
def heckeGaussConstant (ψ : HeckeCharacter 𝔪) : ℂ :=
  finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (heckeReferenceFrequency 𝔪 : K) *
    (infiniteSignCharacter 𝔪 ψ
      (signAtInf 𝔪 (Units.mk0 _ (heckeReferenceFrequency_ne_zero 𝔪))) : ℂ) *
    heckeValue 𝔪 ψ (heckeReferenceIdeal 𝔪)

/-- The arithmetic Gauss constant has exact squared norm equal to the finite conductor norm. -/
theorem norm_heckeGaussConstant_sq (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    ‖heckeGaussConstant 𝔪 ψ‖ ^ 2 = (Ideal.absNorm 𝔪.fin : ℝ) := by
  have hs : ‖(infiniteSignCharacter 𝔪 ψ
      (signAtInf 𝔪 (Units.mk0 _ (heckeReferenceFrequency_ne_zero 𝔪))) : ℂ)‖ = 1 :=
    norm_char_eq_one _ _
  have hI : ‖heckeValue 𝔪 ψ (heckeReferenceIdeal 𝔪)‖ = 1 := by
    rw [heckeValue_of_mem 𝔪 ψ (heckeReferenceIdeal_ne_bot 𝔪)
      ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr (heckeReferenceIdeal_coprime 𝔪))]
    exact norm_char_eq_one _ _
  have hc : heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp)
      (heckeReferenceFrequency 𝔪) ⊔ 𝔪.fin = ⊤ := heckeReferenceIdeal_coprime 𝔪
  rw [heckeGaussConstant, norm_mul, norm_mul, hs, hI, mul_one, mul_one,
    norm_finiteHeckeFourierCoefficient_sq_eq_coprime 𝔪 (b := ⊤) (by simp) (by simp) ψ hψ,
    if_pos hc]

theorem norm_heckeGaussConstant (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    ‖heckeGaussConstant 𝔪 ψ‖ = Real.sqrt (Ideal.absNorm 𝔪.fin : ℝ) := by
  rw [← norm_heckeGaussConstant_sq 𝔪 ψ hψ, Real.sqrt_sq (norm_nonneg _)]

/-- Unit normalization of the actual arithmetic Gauss constant. -/
def heckeNormalizedGaussConstant (ψ : HeckeCharacter 𝔪) : ℂ :=
  heckeGaussConstant 𝔪 ψ / (Real.sqrt (Ideal.absNorm 𝔪.fin : ℝ) : ℂ)

theorem norm_heckeNormalizedGaussConstant (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    ‖heckeNormalizedGaussConstant 𝔪 ψ‖ = 1 := by
  have hn : 0 < (Ideal.absNorm 𝔪.fin : ℝ) := by
    letI : Finite (𝓞 K ⧸ 𝔪.fin) := 𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
    change 0 < (Nat.card (𝓞 K ⧸ 𝔪.fin) : ℝ)
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (𝓞 K ⧸ 𝔪.fin))
  rw [heckeNormalizedGaussConstant, norm_div, norm_heckeGaussConstant 𝔪 ψ hψ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_self (Real.sqrt_pos.mpr hn).ne']

end GaloisForLFunctions.HeckeLFunctions
