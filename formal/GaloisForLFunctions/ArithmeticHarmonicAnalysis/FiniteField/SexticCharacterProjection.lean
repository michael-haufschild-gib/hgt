import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A target-preserving sextic character projection

A multiplicative character of order six separates residue-field samples into
six character modes. Weighting by the character extracts the inverse mode.
Its geometric resolvent contribution is exactly `Y^5 / (1 - Y^6)`.
Normalization by the number of units makes the projection a contraction for
uniform sample errors, including the actual zero-weight at the zero residue.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.SexticCharacterProjection
variable {F : Type*} [Field F] [Fintype F]

/-- The normalized character-weighted average over actual residue-field samples. -/
def projection (χ : MulChar F ℂ) : (F → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * f a
  map_add' f g := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z f := by
    change (Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * (z * f a) =
      z * ((Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * f a)
    have he (a : F) : χ a * (z * f a) = z * (χ a * f a) := mul_left_comm _ _ _
    simp_rw [he]
    rw [← Finset.mul_sum]
    ring

/-- Exact orthogonality of positive character powers on the residue field. -/
theorem power_sum (χ : MulChar F ℂ) (hχ : orderOf χ = 6) (k : ℕ) (hk : 0 < k) :
    ∑ a : F, χ a ^ k = if 6 ∣ k then (Fintype.card Fˣ : ℂ) else 0 := by
  classical
  simp_rw [← MulChar.pow_apply' χ (Nat.ne_of_gt hk)]
  by_cases hd : 6 ∣ k
  · have he : χ ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (hχ.symm ▸ hd)
    rw [he, if_pos hd, MulChar.sum_one_eq_card_units]
  · rw [if_neg hd]
    apply MulChar.sum_eq_zero_of_ne_one
    intro he
    exact hd (hχ ▸ orderOf_dvd_iff_pow_eq_one.mpr he)

/-- The principal residue mode is annihilated. -/
theorem projection_const (χ : MulChar F ℂ) (hχ : orderOf χ = 6) (c : ℂ) :
    projection χ (fun _ => c) = 0 := by
  have h := power_sum χ hχ 1 (by omega)
  norm_num only [pow_one, Nat.reduceDvd, if_false] at h
  change (Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * c = 0
  rw [← Finset.sum_mul, h, zero_mul, mul_zero]

/-- The forward character mode is annihilated by the inverse-mode extractor. -/
theorem projection_character (χ : MulChar F ℂ) (hχ : orderOf χ = 6) :
    projection χ (fun a => χ a) = 0 := by
  have h := power_sum χ hχ 2 (by omega)
  norm_num only [Nat.reduceDvd, if_false] at h
  change (Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * χ a = 0
  simp only [← pow_two, h, mul_zero]

/-- The inverse character mode is recovered with coefficient one. -/
theorem projection_inverse (χ : MulChar F ℂ) :
    projection χ (fun a => (χ a)⁻¹) = 1 := by
  classical
  have hp (a : F) : χ a * (χ a)⁻¹ = (1 : MulChar F ℂ) a := by
    by_cases ha : a = 0
    · simp [ha, MulChar.map_zero]
    · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
      rw [MulChar.one_apply hu, mul_inv_cancel₀ (hu.map χ).ne_zero]
  change (Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * (χ a)⁻¹ = 1
  simp_rw [hp]
  rw [MulChar.sum_one_eq_card_units]
  exact inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero (α := Fˣ)))

private theorem weighted_geometric_expansion (ρ Y : ℂ) (hρ : ρ ^ 6 = 1)
    (hY : 1 - Y ^ 6 ≠ 0) :
    ρ * (ρ * Y * (1 - ρ * Y)⁻¹) =
      (1 - Y ^ 6)⁻¹ * ∑ j ∈ Finset.range 6, ρ ^ (j+2) * Y ^ (j+1) := by
  have hp : (ρ*Y)^6 = Y^6 := by rw [mul_pow, hρ, one_mul]
  have hd : 1 - ρ * Y ≠ 0 := by
    intro h
    have hh : ρ * Y = 1 := (sub_eq_zero.mp h).symm
    rw [hh, one_pow] at hp
    exact hY (sub_eq_zero.mpr hp)
  have hs : (∑ j ∈ Finset.range 6, (ρ*Y)^j) * (1-ρ*Y) = 1-Y^6 := by
    have h := geom_sum_mul (ρ*Y) 6
    rw [hp] at h
    linear_combination -h
  have hi : (1-ρ*Y)⁻¹ = (1-Y^6)⁻¹ * ∑ j ∈ Finset.range 6, (ρ*Y)^j := by
    apply (mul_left_cancel₀ hY)
    rw [← mul_assoc, mul_inv_cancel₀ hY, one_mul, ← hs]
    rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]
  rw [hi]
  rw [Finset.mul_sum]
  have he : ρ * (ρ * Y * ∑ j ∈ Finset.range 6, (1-Y^6)⁻¹ * (ρ*Y)^j) =
      ∑ j ∈ Finset.range 6, (1-Y^6)⁻¹ * (ρ^(j+2)*Y^(j+1)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [pow_add, pow_one, mul_pow]
    ring
  rw [he, ← Finset.mul_sum]

/-- The sole geometric contribution surviving the inverse sextic mode. -/
theorem projection_geometric (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (Y : ℂ) (hY : 1-Y^6 ≠ 0) :
    projection χ (fun a => χ a * Y * (1-χ a*Y)⁻¹) = Y^5 * (1-Y^6)⁻¹ := by
  classical
  have h6 : χ^6=1 := orderOf_dvd_iff_pow_eq_one.mp (hχ.symm ▸ dvd_refl 6)
  have hexp (a : F) : χ a * (χ a * Y * (1-χ a*Y)⁻¹) =
      (1-Y^6)⁻¹ * ∑ j ∈ Finset.range 6, χ a^(j+2)*Y^(j+1) := by
    by_cases ha : a=0
    · simp [ha, MulChar.map_zero]
    · have hp := congrArg (fun ψ : MulChar F ℂ => ψ a) h6
      simp only [MulChar.pow_apply' _ (by decide : 6 ≠ 0),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)] at hp
      exact weighted_geometric_expansion _ _ hp hY
  change (Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a * (χ a*Y*(1-χ a*Y)⁻¹) = _
  simp_rw [hexp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hp (j : ℕ) := power_sum χ hχ (j+2) (by omega)
  simp_rw [← Finset.sum_mul, hp]
  have hs : ∑ j ∈ Finset.range 6,
      (if 6 ∣ j+2 then (Fintype.card Fˣ : ℂ) else 0) * Y^(j+1) =
      (Fintype.card Fˣ : ℂ) * Y^5 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hs]
  have hn : (Fintype.card Fˣ : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := Fˣ))
  field_simp

/-- Unit residues have unit character norm; the zero residue has zero weight. -/
theorem norm_weights_sum (χ : MulChar F ℂ) :
    ∑ a : F, ‖χ a‖ = (Fintype.card Fˣ : ℝ) := by
  classical
  have he (a : F) : ‖χ a‖ = ((1 : MulChar F ℂ) a).re := by
    by_cases ha : a=0
    · simp [ha, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr ha), Complex.one_re]
      exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity (Units.mk0 a ha))
  simp_rw [he]
  rw [← Complex.re_sum, MulChar.sum_one_eq_card_units]
  simp

/-- Exact weighted error bound for the arithmetic projection. -/
theorem norm_projection_le (χ : MulChar F ℂ) (f : F → ℂ) :
    ‖projection χ f‖ ≤ (Fintype.card Fˣ : ℝ)⁻¹ * ∑ a : F, ‖χ a‖ * ‖f a‖ := by
  change ‖(Fintype.card Fˣ : ℂ)⁻¹ * ∑ a : F, χ a*f a‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset F) (fun a => χ a*f a)

/-- Uniform sample errors do not grow under normalized residue projection. -/
theorem norm_projection_le_bound (χ : MulChar F ℂ) (f : F → ℂ) (B : ℝ)
    (hf : ∀ a, ‖f a‖ ≤ B) : ‖projection χ f‖ ≤ B := by
  have hs : ∑ a : F, ‖χ a‖ * ‖f a‖ ≤ ∑ a : F, ‖χ a‖ * B :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a) (norm_nonneg _))
  have h := (norm_projection_le χ f).trans
    (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg _)))
  rw [← Finset.sum_mul, norm_weights_sum] at h
  have hn : (Fintype.card Fˣ : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α := Fˣ))
  simpa only [← mul_assoc, inv_mul_cancel₀ hn, one_mul] using h

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.SexticCharacterProjection
