import GaloisForLFunctions.RHTower.PaperThetaQuantileVariation
import GaloisForLFunctions.RHTower.PaperThetaEverywhereFourier

/-! # Continuity of the original circle mode with its common seam trace -/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

theorem seamCorrectedCircleMode_eq_closedQuantileMode (z : ℂ) (x : Torus) :
    seamCorrectedCircleMode z x = closedQuantileMode z (Period.coord x) := by
  have hcoord : Period.circle (Period.coord x) = x := by
    unfold Period.circle Period.coord
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ Real.two_pi_pos.ne']
    exact AddCircle.coe_equivIco
  by_cases hx : x = Period.circle 0
  · subst x
    rw [Period.coord_circle_eq (by norm_num [Period.unitInt]),
      (closedQuantileMode_endpoints z).1]
    simp [seamCorrectedCircleMode]
  · have hm := (AddCircle.measurableEquivIco (2*Real.pi) 0 x).property
    have hnonneg : 0 ≤ Period.coord x := div_nonneg hm.1 Real.two_pi_pos.le
    have hlt : Period.coord x < 1 := by
      apply (div_lt_one Real.two_pi_pos).mpr
      simpa only [zero_add] using hm.2
    have hn : Period.coord x ≠ 0 := by
      intro he
      exact hx (by rw [← hcoord, he])
    have ht : Period.coord x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hnonneg (Ne.symm hn), hlt⟩
    rw [closedQuantileMode_interior z ⟨Period.coord x, ht⟩]
    simp only [seamCorrectedCircleMode, if_neg hx, circleMode]

/-- The admitted native mode is continuous across the circle seam. -/
theorem continuous_seamCorrectedCircleMode (z : {z : ℂ // z = 0 ∨ XiC z = 0}) :
    Continuous (seamCorrectedCircleMode z.val) := by
  let f : ℝ → ℂ := fun r => closedQuantileMode z.val (r/(2*Real.pi))
  have hf : ContinuousOn f (Icc (0 : ℝ) (2*Real.pi)) := by
    apply (continuousOn_closedQuantileMode z).comp (continuous_id.div_const _).continuousOn
    intro r hr
    exact ⟨div_nonneg hr.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hr.2⟩
  have he : f 0 = f (2*Real.pi) := by
    dsimp only [f]
    rw [zero_div, div_self Real.two_pi_pos.ne',
      (closedQuantileMode_endpoints z.val).1, (closedQuantileMode_endpoints z.val).2]
  have hfun : seamCorrectedCircleMode z.val = AddCircle.liftIco (2*Real.pi) 0 f := by
    funext x
    rw [seamCorrectedCircleMode_eq_closedQuantileMode]
    rfl
  rw [hfun]
  exact AddCircle.liftIco_zero_continuous he hf

/-- Actual continuity of the corrected circle mode has the same exact native selector. -/
theorem continuous_seamCorrectedCircleMode_iff (z : ℂ) :
    Continuous (seamCorrectedCircleMode z) ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    have hm := h.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) circleMeasure
    exact (memLp_top_circleMode_iff z).mp
      ((memLp_congr_ae (seamCorrectedCircleMode_ae z)).mp hm)
  · intro hz
    exact continuous_seamCorrectedCircleMode ⟨z, hz⟩

end RHTower.PaperThetaEndpoint
