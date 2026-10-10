import GaloisForLFunctions.RHTower.WeilLogShiftMomentBarycentric
import GaloisForLFunctions.RHTower.WeilLogShiftMomentProbabilities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Pairwise node distortion controls reciprocal nodal weights and normalized mass. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilMomentWeights_abs_product {n : ℕ} (h : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    |finiteWeilMomentWeights h i| = ∏ j ∈ Finset.univ.erase i, |h i - h j|⁻¹ := by
  simp only [finiteWeilMomentWeights, Lagrange.nodalWeight, Finset.abs_prod, abs_inv]

/-- Multiplying all pairwise gap comparisons reverses their direction for nodal weights. -/
theorem finiteWeilMomentWeights_scaled_gap_comparison {n : ℕ}
    (h g : Fin (n + 1) → ℝ) (hh : Function.Injective h) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 ≤ a)
    (hgap : ∀ i j, i ≠ j → a * |h i - h j| ≤ b * |g i - g j|)
    (i : Fin (n + 1)) :
    a ^ n * |finiteWeilMomentWeights g i| ≤ b ^ n * |finiteWeilMomentWeights h i| := by
  have hp : (∏ j ∈ Finset.univ.erase i, a * |g i - g j|⁻¹) ≤
      ∏ j ∈ Finset.univ.erase i, b * |h i - h j|⁻¹ := by
    apply Finset.prod_le_prod
    · intro j _
      exact mul_nonneg ha (inv_nonneg.mpr (abs_nonneg _))
    · intro j hj
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hhij : 0 < |h i - h j| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hij (hh he)))
      have hgij : 0 < |g i - g j| := abs_pos.mpr (sub_ne_zero.mpr (fun he => hij (hg he)))
      simpa only [div_eq_mul_inv] using (div_le_div_iff₀ hgij hhij).mpr (hgap i j hij)
  rw [finiteWeilMomentWeights_abs_product, finiteWeilMomentWeights_abs_product]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel] using hp

theorem finiteWeil_scaled_abs_norm_le {ι : Type} [Fintype ι] (f g : ι → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ i, a * |f i| ≤ b * |g i|) : a * ‖f‖ ≤ b * ‖g‖ := by
  have hn : ‖a • f‖ ≤ b * ‖g‖ :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg g))).mpr fun i => by
      change ‖a * f i‖ ≤ b * ‖g‖
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
      exact (h i).trans (mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g i) hb)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] using hn

/-- Two pointwise magnitude bounds give both directions of mass-ratio control. -/
theorem finiteWeil_abs_mass_ratio_comparison {ι : Type} [Fintype ι]
    (f g : ι → ℝ) (hf : 0 < ‖f‖) (hg : 0 < ‖g‖)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ i, a * |f i| ≤ |g i| ∧ |g i| ≤ b * |f i|) :
    a * (finiteWeilAbsMass f / ‖f‖) ≤ b * (finiteWeilAbsMass g / ‖g‖) ∧
    a * (finiteWeilAbsMass g / ‖g‖) ≤ b * (finiteWeilAbsMass f / ‖f‖) := by
  have hmf : 0 ≤ finiteWeilAbsMass f := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmg : 0 ≤ finiteWeilAbsMass g := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsl : a * finiteWeilAbsMass f ≤ finiteWeilAbsMass g := by
    simpa only [finiteWeilAbsMass, Finset.mul_sum] using
      Finset.sum_le_sum (fun i _ => (h i).1)
  have hsu : finiteWeilAbsMass g ≤ b * finiteWeilAbsMass f := by
    simpa only [finiteWeilAbsMass, Finset.mul_sum] using
      Finset.sum_le_sum (fun i _ => (h i).2)
  have hnl : a * ‖f‖ ≤ ‖g‖ := by
    simpa only [one_mul] using finiteWeil_scaled_abs_norm_le f g a 1 ha (by norm_num)
      (fun i => by simpa only [one_mul] using (h i).1)
  have hnu : ‖g‖ ≤ b * ‖f‖ := by
    simpa only [one_mul] using finiteWeil_scaled_abs_norm_le g f 1 b (by norm_num) hb
      (fun i => by simpa only [one_mul] using (h i).2)
  constructor
  · rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ hf hg).mpr
    calc
      _ ≤ (a * finiteWeilAbsMass f) * (b * ‖f‖) :=
        mul_le_mul_of_nonneg_left hnu (mul_nonneg ha hmf)
      _ ≤ finiteWeilAbsMass g * (b * ‖f‖) :=
        mul_le_mul_of_nonneg_right hsl (mul_nonneg hb hf.le)
      _ = _ := by ring
  · rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ hg hf).mpr
    calc
      _ = finiteWeilAbsMass g * (a * ‖f‖) := by ring
      _ ≤ finiteWeilAbsMass g * ‖g‖ := mul_le_mul_of_nonneg_left hnl hmg
      _ ≤ (b * finiteWeilAbsMass f) * ‖g‖ := mul_le_mul_of_nonneg_right hsu hg.le

theorem finiteWeilNormalizedMomentDual_abs_mass {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hh : Function.Injective h) :
    finiteWeilAbsMass (finiteWeilNormalizedMomentDual h) =
      finiteWeilAbsMass (finiteWeilMomentWeights h) / ‖finiteWeilMomentWeights h‖ := by
  unfold finiteWeilAbsMass finiteWeilNormalizedMomentDual
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr (finiteWeilMomentWeights_norm_pos h hh)), ← Finset.mul_sum,
    div_eq_mul_inv]
  ring

theorem finiteWeilNormalizedMomentDual_mass_comparison {n : ℕ}
    (h g : Fin (n + 1) → ℝ) (hh : Function.Injective h) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : ∀ i, a * |finiteWeilMomentWeights h i| ≤ |finiteWeilMomentWeights g i| ∧
      |finiteWeilMomentWeights g i| ≤ b * |finiteWeilMomentWeights h i|) :
    a * finiteWeilAbsMass (finiteWeilNormalizedMomentDual h) ≤
      b * finiteWeilAbsMass (finiteWeilNormalizedMomentDual g) ∧
    a * finiteWeilAbsMass (finiteWeilNormalizedMomentDual g) ≤
      b * finiteWeilAbsMass (finiteWeilNormalizedMomentDual h) := by
  simpa only [finiteWeilNormalizedMomentDual_abs_mass h hh,
    finiteWeilNormalizedMomentDual_abs_mass g hg] using
    finiteWeil_abs_mass_ratio_comparison (finiteWeilMomentWeights h) (finiteWeilMomentWeights g)
      (finiteWeilMomentWeights_norm_pos h hh) (finiteWeilMomentWeights_norm_pos g hg) a b ha hb hw

end RHTower
