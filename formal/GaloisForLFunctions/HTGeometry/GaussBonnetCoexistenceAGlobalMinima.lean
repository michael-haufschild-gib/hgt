import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAStationaryRoots
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Global phase stability for logarithmic Gauss–Bonnet entropy

The actual free-energy derivative has three positive roots. Its exact
factorization proves four strict monotonicity branches and precisely two
global minima. The intermediate stationary point is a strict barrier.
This is an analytic global audit of the coexistence construction.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceAReducedLogGibbs_left_strictAnti (τ θ : ℝ) :
    StrictAntiOn (egbCoexistenceAReducedLogGibbs τ θ) (Iic (log (thermalRatio τ))) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _) (egbCoexistenceAReducedLogGibbs_continuous τ θ).continuousOn
  intro x hx
  rw [interior_Iic, mem_Iio] at hx
  have hz := thermalRatio_pos τ
  have hzw := egbCoexistenceAMiddleRadius_bounds τ θ
  have hxz : exp x < thermalRatio τ := by simpa only [exp_log hz] using exp_lt_exp.mpr hx
  have hxw : exp x < egbCoexistenceAMiddleRadius τ θ := lt_trans hxz hzw.1
  have hx1 : exp x < 1 := lt_trans hxw hzw.2
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ x).deriv, egbCoexistenceARadialPolynomial_full_factorization]
  apply div_neg_of_neg_of_pos _ (by positivity)
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp (sub_neg.mpr hxz))
      (sub_neg.mpr hxw)) (sub_neg.mpr hx1)) (by positivity)

theorem egbCoexistenceAReducedLogGibbs_lower_middle_strictMono (τ θ : ℝ) :
    StrictMonoOn (egbCoexistenceAReducedLogGibbs τ θ)
      (Icc (log (thermalRatio τ)) (log (egbCoexistenceAMiddleRadius τ θ))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (egbCoexistenceAReducedLogGibbs_continuous τ θ).continuousOn
  intro x hx
  rw [interior_Icc, mem_Ioo] at hx
  have hz := thermalRatio_pos τ
  have hw := egbCoexistenceAMiddleRadius_pos τ θ
  have hxz : thermalRatio τ < exp x := by simpa only [exp_log hz] using exp_lt_exp.mpr hx.1
  have hxw : exp x < egbCoexistenceAMiddleRadius τ θ := by simpa only [exp_log hw] using exp_lt_exp.mpr hx.2
  have hx1 : exp x < 1 := lt_trans hxw (egbCoexistenceAMiddleRadius_bounds τ θ).2
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ x).deriv, egbCoexistenceARadialPolynomial_full_factorization]
  apply div_pos _ (by positivity)
  exact mul_pos (mul_pos_of_neg_of_neg
    (mul_neg_of_pos_of_neg (mul_pos hp (sub_pos.mpr hxz)) (sub_neg.mpr hxw))
      (sub_neg.mpr hx1)) (by positivity)

theorem egbCoexistenceAReducedLogGibbs_upper_middle_strictAnti (τ θ : ℝ) :
    StrictAntiOn (egbCoexistenceAReducedLogGibbs τ θ)
      (Icc (log (egbCoexistenceAMiddleRadius τ θ)) 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (egbCoexistenceAReducedLogGibbs_continuous τ θ).continuousOn
  intro x hx
  rw [interior_Icc, mem_Ioo] at hx
  have hw := egbCoexistenceAMiddleRadius_pos τ θ
  have hxw : egbCoexistenceAMiddleRadius τ θ < exp x := by simpa only [exp_log hw] using exp_lt_exp.mpr hx.1
  have hxz : thermalRatio τ < exp x := lt_trans (egbCoexistenceAMiddleRadius_bounds τ θ).1 hxw
  have hx1 : exp x < 1 := by simpa only [exp_zero] using exp_lt_exp.mpr hx.2
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ x).deriv, egbCoexistenceARadialPolynomial_full_factorization]
  apply div_neg_of_neg_of_pos _ (by positivity)
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
    (mul_pos (mul_pos hp (sub_pos.mpr hxz)) (sub_pos.mpr hxw)) (sub_neg.mpr hx1)) (by positivity)

theorem egbCoexistenceAReducedLogGibbs_right_strictMono (τ θ : ℝ) :
    StrictMonoOn (egbCoexistenceAReducedLogGibbs τ θ) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (egbCoexistenceAReducedLogGibbs_continuous τ θ).continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hx1 : 1 < exp x := by simpa only [exp_zero] using exp_lt_exp.mpr hx
  have hxw : egbCoexistenceAMiddleRadius τ θ < exp x := lt_trans (egbCoexistenceAMiddleRadius_bounds τ θ).2 hx1
  have hxz : thermalRatio τ < exp x := lt_trans (egbCoexistenceAMiddleRadius_bounds τ θ).1 hxw
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ x).deriv, egbCoexistenceARadialPolynomial_full_factorization]
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos hp (sub_pos.mpr hxz))
    (sub_pos.mpr hxw)) (sub_pos.mpr hx1)) (by positivity)) (by positivity)

/-- Every radius other than the two phase radii has strictly higher free energy. -/
theorem egbCoexistenceAReducedLogGibbs_gap_pos_iff (τ θ u : ℝ) :
    egbCoexistenceAReducedLogGibbs τ θ 0 < egbCoexistenceAReducedLogGibbs τ θ u ↔
      u ≠ log (thermalRatio τ) ∧ u ≠ 0 := by
  have hb := egbCoexistenceAMiddleRadius_log_bounds τ θ
  have he := egbCoexistenceAReducedLogGibbs_balance τ θ
  constructor
  · intro h
    constructor
    · rintro rfl
      rw [he] at h
      exact (lt_irrefl _ h)
    · rintro rfl
      exact (lt_irrefl _ h)
  · rintro ⟨hz, h0⟩
    rcases lt_or_gt_of_ne hz with hleft | hright
    · rw [← he]
      exact egbCoexistenceAReducedLogGibbs_left_strictAnti τ θ (le_of_lt hleft) (by simp) hleft
    · by_cases hm : u ≤ log (egbCoexistenceAMiddleRadius τ θ)
      · rw [← he]
        exact egbCoexistenceAReducedLogGibbs_lower_middle_strictMono τ θ
          ⟨le_rfl, le_of_lt hb.1⟩ ⟨le_of_lt hright, hm⟩ hright
      · rcases lt_or_gt_of_ne h0 with hn | hp
        · exact egbCoexistenceAReducedLogGibbs_upper_middle_strictAnti τ θ
            ⟨le_of_lt (lt_of_not_ge hm), le_of_lt hn⟩ ⟨le_of_lt hb.2, le_rfl⟩ hn
        · exact egbCoexistenceAReducedLogGibbs_right_strictMono τ θ (by simp) (le_of_lt hp) hp

theorem egbCoexistenceAReducedLogGibbs_global_minimum (τ θ u : ℝ) :
    egbCoexistenceAReducedLogGibbs τ θ 0 ≤ egbCoexistenceAReducedLogGibbs τ θ u := by
  by_cases hz : u = log (thermalRatio τ)
  · rw [hz, egbCoexistenceAReducedLogGibbs_balance]
  by_cases h0 : u = 0
  · rw [h0]
  exact le_of_lt ((egbCoexistenceAReducedLogGibbs_gap_pos_iff τ θ u).2 ⟨hz, h0⟩)

theorem egbCoexistenceAReducedLogGibbs_minimizers_iff (τ θ u : ℝ) :
    egbCoexistenceAReducedLogGibbs τ θ u = egbCoexistenceAReducedLogGibbs τ θ 0 ↔
      u = log (thermalRatio τ) ∨ u = 0 := by
  constructor
  · intro he
    by_contra hn
    have hz : u ≠ log (thermalRatio τ) := fun h => hn (Or.inl h)
    have h0 : u ≠ 0 := fun h => hn (Or.inr h)
    have h := (egbCoexistenceAReducedLogGibbs_gap_pos_iff τ θ u).2 ⟨hz, h0⟩
    rw [he] at h
    exact lt_irrefl _ h
  · rintro (rfl | rfl)
    · exact egbCoexistenceAReducedLogGibbs_balance τ θ
    · rfl

/-- The unique stationary radius between the two phases lies strictly above both minima. -/
theorem egbCoexistenceAReducedLogGibbs_barrier_pos (τ θ : ℝ) :
    0 < egbCoexistenceAReducedLogGibbs τ θ (log (egbCoexistenceAMiddleRadius τ θ)) -
      egbCoexistenceAReducedLogGibbs τ θ 0 := by
  rw [sub_pos]
  exact (egbCoexistenceAReducedLogGibbs_gap_pos_iff τ θ _).2
    ⟨ne_of_gt (egbCoexistenceAMiddleRadius_log_bounds τ θ).1,
      ne_of_lt (egbCoexistenceAMiddleRadius_log_bounds τ θ).2⟩

end GaloisForLFunctions.HTGeometry
