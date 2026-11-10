import GaloisForLFunctions.SelectiveArithmetic.InTheMeanOverTheHeightsTheContactsCancel

/-!
# The contact polynomial has few large heights

The mean square on `[T,2T]` bounds the measure of heights at which the contact
polynomial exceeds a fixed fraction of `log T`. At aperture `a ≥ 1` the bound is
`33 T a³/(c log T)²`, provided the polynomial's length fits in the height interval.
This is a statement about the contact polynomial; full window positivity has a
separate quantifier over packet frequencies.
-/

open Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

/-- Markov's inequality turns the contact mean square into a large-height bound. -/
theorem measureReal_large_contactPoly_le {a T V : ℝ} (ha : 0 ≤ a) (hV : 0 < V)
    (hT : 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 ≤ T) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | V ≤ |contactPoly ⌊Real.exp (2 * a)⌋₊ t|} ≤
      T * (2 * a * (2 + 2 * a) ^ 2 + 1) / V ^ 2 := by
  let D := contactPoly ⌊Real.exp (2 * a)⌋₊
  have hDc : Continuous D := continuous_contactPoly _
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4).trans hT
  have hint : Integrable (fun t => D t ^ 2) (volume.restrict (Ioc T (2 * T))) :=
    ((hDc.pow 2).integrableOn_Icc (a := T) (b := 2 * T)).mono_set Ioc_subset_Icc_self
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Ioc T (2 * T)))
    (Filter.Eventually.of_forall fun t => sq_nonneg (D t)) hint (V ^ 2)
  have hset : {t | V ≤ |D t|} = {t | V ^ 2 ≤ D t ^ 2} := by
    ext t
    simp only [mem_setOf_eq]
    constructor
    · intro h
      simpa only [sq_abs] using pow_le_pow_left₀ hV.le h 2
    · intro h
      by_contra hn
      have hlt := pow_lt_pow_left₀ (lt_of_not_ge hn) (abs_nonneg (D t)) (by norm_num : 2 ≠ 0)
      rw [sq_abs] at hlt
      exact (not_lt.mpr h) hlt
  change (volume.restrict (Ioc T (2 * T))).real {t | V ≤ |D t|} ≤ _
  rw [hset, le_div_iff₀ (sq_pos_of_pos hV), mul_comm]
  have hmom := integral_contactPoly_window_sq_le ha hT
  rw [intervalIntegral.integral_of_le (by linarith only [hT0])] at hmom
  exact hmark.trans hmom

/-- The exceptional contact heights have measure at most `33 T a³/(c log T)²`. -/
theorem measureReal_contactPoly_log_heights_le {a T c : ℝ}
    (ha : 1 ≤ a) (hT1 : 1 < T) (hc : 0 < c)
    (hT : 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 ≤ T) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | c * Real.log T ≤ |contactPoly ⌊Real.exp (2 * a)⌋₊ t|} ≤
      33 * T * a ^ 3 / (c * Real.log T) ^ 2 := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hpoly : 2 * a * (2 + 2 * a) ^ 2 + 1 ≤ 33 * a ^ 3 := by
    have hs : (2 + 2 * a) ^ 2 ≤ (4 * a) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [ha]) 2
    have hcube : 1 ≤ a ^ 3 := one_le_pow₀ ha
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * a)
    nlinarith only [hm, hcube]
  refine (measureReal_large_contactPoly_le ha0 (mul_pos hc (Real.log_pos hT1)) hT).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hpoly (zero_lt_one.trans hT1).le
  nlinarith only [hm]

end GaloisForLFunctions.SelectiveArithmetic
