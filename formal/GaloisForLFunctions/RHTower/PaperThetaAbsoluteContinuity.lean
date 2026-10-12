import GaloisForLFunctions.RHTower.PaperThetaQuantileDerivative
import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity

/-! # Exact absolute-continuity admission for the closed quantile mode

The actual derivative primitive pays absolute continuity across the seam.
The converse is the already-proven exact bounded-variation selector.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

theorem absolutelyContinuousOnInterval_closedQuantileMode
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    AbsolutelyContinuousOnInterval (closedQuantileMode z.val) 0 1 := by
  have hp := GaloisForLFunctions.HTGeometry.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
      (intervalIntegrable_deriv_closedQuantileMode z) (c := 0) (by norm_num)
  rw [AbsolutelyContinuousOnInterval] at hp ⊢
  apply hp.congr'
  have hevent : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin 0 1),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 1 :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hevent] with E hE
  obtain ⟨hpoints, -⟩ := hE
  apply Finset.sum_congr rfl
  intro i hi
  have ha : (E.2 i).1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using (hpoints i hi).1
  have hb : (E.2 i).2 ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using (hpoints i hi).2
  rw [closedQuantileMode_eq_integral_deriv z ⟨_, ha⟩,
    closedQuantileMode_eq_integral_deriv z ⟨_, hb⟩, dist_eq_norm, dist_eq_norm]
  congr 1
  ring

/-- Absolute continuity has exactly the same native divisor-or-zero domain. -/
theorem absolutelyContinuousOnInterval_closedQuantileMode_iff (z : ℂ) :
    AbsolutelyContinuousOnInterval (closedQuantileMode z) 0 1 ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    apply (boundedVariationOn_closedQuantileMode_iff z).mp
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using h.boundedVariationOn
  · intro hz
    exact absolutelyContinuousOnInterval_closedQuantileMode ⟨z, hz⟩

end RHTower.PaperThetaEndpoint
