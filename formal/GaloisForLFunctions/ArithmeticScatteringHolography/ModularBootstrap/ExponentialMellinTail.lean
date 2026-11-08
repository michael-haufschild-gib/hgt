import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential errors from truncating Mellin boundaries

Splitting the real line into a finite interval and two tails gives an explicit
truncation bound from an exponential envelope.
-/

open Complex Set Filter MeasureTheory
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- An exponential envelope controls both tails of a full vertical integral. -/
theorem norm_integral_sub_truncated_le {f : ℝ → ℂ} (hf : Integrable f)
    {T a C : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hb : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ C * Real.exp (-(a * |t|))) :
    ‖(∫ t : ℝ, f t) - ∫ t : ℝ in (-T)..T, f t‖ ≤
      (2 * C / a) * Real.exp (-(a * T)) := by
  have hright : ‖∫ t in Ioi T, f t‖ ≤ (C / a) * Real.exp (-(a * T)) := by
    have hmajor := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) T).const_mul C
    have h := norm_integral_le_of_norm_le (f := f) hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := hT.trans ht.le
      have h := hb t (by rw [abs_of_nonneg ht0]; exact ht.le)
      simpa only [abs_of_nonneg ht0, neg_mul] using h)
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha) T] at h
    simp only [neg_mul, neg_div_neg_eq] at h
    exact h.trans_eq (by ring)
  have hleft : ‖∫ t in Iic (-T), f t‖ ≤ (C / a) * Real.exp (-(a * T)) := by
    have hmajor := (integrableOn_exp_mul_Iic ha (-T)).const_mul C
    have h := norm_integral_le_of_norm_le (f := f) hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      change t ≤ -T at ht
      have ht0 : t ≤ 0 := ht.trans (neg_nonpos.mpr hT)
      have ht' : T ≤ |t| := by rw [abs_of_nonpos ht0]; linarith only [ht]
      have h := hb t ht'
      simpa only [abs_of_nonpos ht0, mul_neg, neg_neg] using h)
    rw [integral_const_mul, integral_exp_mul_Iic ha (-T), mul_neg] at h
    exact h.trans_eq (by ring)
  have hsplit : (∫ t in Iic T, f t) + ∫ t in Ioi T, f t = ∫ t : ℝ, f t := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hf.integrableOn hf.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have hdisj : Disjoint (Iic (-T)) (Ioc (-T) T) := by
    apply disjoint_left.mpr
    intro t ht hs
    exact (not_lt_of_ge ht) hs.1
  have hunion : Iic (-T) ∪ Ioc (-T) T = Iic T := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioc]
    constructor
    · rintro (ht | ht)
      · linarith only [ht, hT]
      · exact ht.2
    · intro ht
      by_cases hlow : t ≤ -T
      · exact Or.inl hlow
      · exact Or.inr ⟨lt_of_not_ge hlow, ht⟩
  have hsplit' : (∫ t in Iic (-T), f t) + ∫ t in Ioc (-T) T, f t =
      ∫ t in Iic T, f t := by
    rw [← setIntegral_union hdisj measurableSet_Ioc hf.integrableOn hf.integrableOn, hunion]
  have heq : (∫ t : ℝ, f t) - ∫ t : ℝ in (-T)..T, f t =
      (∫ t in Iic (-T), f t) + ∫ t in Ioi T, f t := by
    rw [intervalIntegral.integral_of_le (by linarith only [hT] : -T ≤ T)]
    linear_combination -hsplit - hsplit'
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

#print axioms norm_integral_sub_truncated_le
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
