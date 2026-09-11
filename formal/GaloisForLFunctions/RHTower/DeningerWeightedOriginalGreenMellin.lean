import GaloisForLFunctions.RHTower.DeningerL1GreenCellCalculus

/-!
# Weighted Mellin admission of the original Green sum

Exponential weighting makes the literal future translation series absolutely
summable in L1. Its integral retains the original geometric denominator.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem geometricTranslate_norm_integral (F : ℝ → ℂ) (q : ℂ)
    (L : ℝ) (j : ℕ) :
    (∫ t, ‖q ^ j * F (t + (j : ℝ) * L)‖) =
      ‖q‖ ^ j * ∫ t, ‖F t‖ := by
  simp only [norm_mul, norm_pow, integral_const_mul]
  rw [integral_add_right_eq_self (fun t : ℝ => ‖F t‖)]

private theorem geometricTranslate_norm_summable (F : ℝ → ℂ)
    {q : ℂ} (hq : ‖q‖ < 1) (L : ℝ) :
    Summable (fun j : ℕ => ∫ t, ‖q ^ j * F (t + (j : ℝ) * L)‖) := by
  have hnorm : ‖(‖q‖ : ℝ)‖ < 1 := by simpa only [norm_norm] using hq
  have hs : Summable (fun j : ℕ => ‖q‖ ^ j) := summable_geometric_of_norm_lt_one hnorm
  simpa only [geometricTranslate_norm_integral] using hs.mul_right (∫ t, ‖F t‖)

private theorem geometricTranslate_integrable {F : ℝ → ℂ} (hF : Integrable F)
    {q : ℂ} (hq : ‖q‖ < 1) (L : ℝ) :
    Integrable (fun t => ∑' j : ℕ, q ^ j * F (t + (j : ℝ) * L)) := by
  apply integrable_tsum_of_summable_integral_norm
  · intro j
    exact (hF.comp_add_right ((j : ℝ) * L)).const_mul (q ^ j)
  · exact geometricTranslate_norm_summable F hq L

private theorem geometricTranslate_integral {F : ℝ → ℂ} (hF : Integrable F)
    {q : ℂ} (hq : ‖q‖ < 1) (L : ℝ) :
    (∫ t, ∑' j : ℕ, q ^ j * F (t + (j : ℝ) * L)) =
      (∫ t, F t) / (1 - q) := by
  have hi (j : ℕ) : Integrable (fun t => q ^ j * F (t + (j : ℝ) * L)) :=
    (hF.comp_add_right ((j : ℝ) * L)).const_mul (q ^ j)
  have hn := geometricTranslate_norm_summable F hq L
  rw [← integral_tsum_of_summable_integral_norm hi hn]
  simp only [integral_const_mul, integral_add_right_eq_self, tsum_mul_right,
    tsum_geometric_of_norm_lt_one hq, div_eq_mul_inv, mul_comm]

private theorem weightedGreen_term (f : ℝ → ℂ) (L t : ℝ) (s : ℂ) (j : ℕ) :
    Complex.exp (s * (t : ℂ)) * f (t + (j : ℝ) * L) =
      Complex.exp (-s * (L : ℂ)) ^ j *
        (Complex.exp (s * ((t + (j : ℝ) * L : ℝ) : ℂ)) * f (t + (j : ℝ) * L)) := by
  symm
  rw [← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

private theorem weightedGreen_eq (f : ℝ → ℂ) (L : ℝ) (s : ℂ) :
    (fun t : ℝ => Complex.exp (s * (t : ℂ)) * deningerL1OriginalGreenSum f L t) =
      (fun t => ∑' j : ℕ, Complex.exp (-s * (L : ℂ)) ^ j *
        (Complex.exp (s * ((t + (j : ℝ) * L : ℝ) : ℂ)) * f (t + (j : ℝ) * L))) := by
  funext t
  rw [deningerL1OriginalGreenSum, ← tsum_mul_left]
  exact tsum_congr (weightedGreen_term f L t s)

/-- The actual original shift is strictly contractive after any positive real weight. -/
theorem deningerOriginalGreen_weight_norm_lt_one {L : ℝ} (hL : 0 < L)
    {s : ℂ} (hs : 0 < s.re) : ‖Complex.exp (-s * (L : ℂ))‖ < 1 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) hL

/-- The original geometric denominator does not vanish in the admitted half-plane. -/
theorem deningerOriginalGreen_denominator_ne_zero {L : ℝ} (hL : 0 < L)
    {s : ℂ} (hs : 0 < s.re) : 1 - Complex.exp (-s * (L : ℂ)) ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  have hn := deningerOriginalGreen_weight_norm_lt_one hL hs
  rw [← he, norm_one] at hn
  exact (lt_irrefl 1) hn

/-- Positive weighting admits the same literal future sum, with no boundary subtraction. -/
theorem deningerL1OriginalGreenSum_weighted_integrable {f : ℝ → ℂ}
    {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 0 < s.re)
    (hf : Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * f t)) :
    Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * deningerL1OriginalGreenSum f L t) := by
  rw [weightedGreen_eq]
  exact geometricTranslate_integrable hf (deningerOriginalGreen_weight_norm_lt_one hL hs) L

/-- The literal weighted integral retains the original prime-translation denominator. -/
theorem deningerL1OriginalGreenSum_mellin {f : ℝ → ℂ}
    {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 0 < s.re)
    (hf : Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * f t)) :
    (∫ t : ℝ, Complex.exp (s * (t : ℂ)) * deningerL1OriginalGreenSum f L t) =
      (∫ t : ℝ, Complex.exp (s * (t : ℂ)) * f t) / (1 - Complex.exp (-s * (L : ℂ))) := by
  change (∫ t, (fun t : ℝ => Complex.exp (s * (t : ℂ)) * deningerL1OriginalGreenSum f L t) t) = _
  rw [weightedGreen_eq]
  exact geometricTranslate_integral hf (deningerOriginalGreen_weight_norm_lt_one hL hs) L

end RHTower
