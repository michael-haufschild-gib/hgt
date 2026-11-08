import Mathlib

/-!
Symmetric interval means preserve even-kernel identities and vary continuously under exponential weighting.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

lemma integral_symmetric_even_eq_two_mul {T : ℝ} {f : ℝ → ℝ}
    (hneg : IntervalIntegrable f volume (-T) 0)
    (hpos : IntervalIntegrable f volume 0 T)
    (heven : ∀ t, f (-t) = f t) :
    (∫ t in (-T)..T, f t) = 2 * ∫ t in (0 : ℝ)..T, f t := by
  have hreflect := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := T)
  simp only [neg_zero] at hreflect
  have heq : (∫ t in (0 : ℝ)..T, f (-t)) = ∫ t in (0 : ℝ)..T, f t :=
    intervalIntegral.integral_congr fun t _ => heven t
  have hleft : (∫ t in (-T)..(0 : ℝ), f t) = ∫ t in (0 : ℝ)..T, f t := by
    rw [← hreflect, heq]
  rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos, hleft]
  ring

lemma continuous_exponential_mean {K : ℝ → ℝ} (hK : Continuous K) (T : ℝ) :
    Continuous (fun w : ℝ => ∫ t in (-T)..T, K t * Real.exp (w * t / 2)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hK.comp continuous_snd).mul
    (Real.continuous_exp.comp
      ((continuous_fst.mul continuous_snd).div_const (2 : ℝ)))

lemma abs_exponential_mean_sub_le {K : ℝ → ℝ} {T A w : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hK : ContinuousOn K (Set.Icc (-T) T))
    (hbound : ∀ t ∈ Set.Icc (-T) T, |K t| ≤ A) (hw : |w| * T ≤ 1 / 2) :
    |(∫ t in (-T)..T, K t * Real.exp (w * t / 2)) - ∫ t in (-T)..T, K t| ≤
      2 * A * T ^ 2 * |w| := by
  have hab : -T ≤ T := by linarith only [hT]
  have hprod : IntervalIntegrable (fun t => K t * Real.exp (w * t / 2)) volume (-T) T :=
    (hK.mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).div_const (2 : ℝ))).continuousOn).intervalIntegrable_of_Icc hab
  have hplain : IntervalIntegrable K volume (-T) T := hK.intervalIntegrable_of_Icc hab
  rw [← intervalIntegral.integral_sub hprod hplain]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T) (C := A * (|w| * T)) (f := fun t => K t * Real.exp (w * t / 2) - K t)
    (fun t ht => by
      rw [Set.uIoc_of_le hab] at ht
      have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hwt : |w * t / 2| ≤ |w| * T / 2 := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htT (abs_nonneg w)) (by norm_num)
      have he := Real.abs_exp_sub_one_le (hwt.trans (by linarith only [hw]))
      rw [Real.norm_eq_abs, show K t * Real.exp (w * t / 2) - K t =
        K t * (Real.exp (w * t / 2) - 1) by ring, abs_mul]
      exact (mul_le_mul (hbound t ⟨ht.1.le, ht.2⟩)
        (he.trans (by linarith only [hwt])) (abs_nonneg _) hA))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hT] : 0 ≤ T - -T)] at hb
  exact hb.trans_eq (by ring)

#print axioms integral_symmetric_even_eq_two_mul
#print axioms continuous_exponential_mean
#print axioms abs_exponential_mean_sub_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
