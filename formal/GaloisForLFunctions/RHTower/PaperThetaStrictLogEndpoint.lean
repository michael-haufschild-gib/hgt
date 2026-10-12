import GaloisForLFunctions.RHTower.PaperThetaHighTiltSource
import GaloisForLFunctions.HTGeometry.PaperStrongLpLogPower

/-! # Theta endpoint reconstruction outside every Lᵖ with p > 1 -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

/-- The high-tilt family escapes every strong Lᵖ admission, including L∞. -/
theorem not_memLp_highTilt_strong (z : HighTiltPoint) (p : StrongLpExponent) :
    ¬ MemLp (circleMode z.val) p.val circleMeasure := by
  intro hp
  let a : ℝ≥0 := ⟨|z.val.im| + 1, by positivity⟩
  have h := integrable_logPower_strongLp circleMeasure p (hp.toLp (circleMode z.val)) a
  have hc : Integrable (fun x => ‖circleMode z.val x‖ *
      Real.log (2 + ‖circleMode z.val x‖) ^ (a : ℝ)) circleMeasure := by
    refine h.congr ?_
    filter_upwards [hp.coeFn_toLp] with x hx
    rw [hx]
  rcases (integrable_circle_logPower_iff z.val a).mp hc with h0 | hXi | hlt
  · exact not_memLp_highTilt z ((memLp_circleMode_iff_all z.val).mpr (Or.inl h0))
  · exact not_memLp_highTilt z ((memLp_circleMode_iff_all z.val).mpr (Or.inr hXi))
  · change 2 * (|z.val.im| + 1) < z.val.im at hlt
    linarith [le_abs_self z.val.im, abs_nonneg z.val.im]

/-- Proven endpoint recovery for a family outside the union of all Lᵖ, p > 1. -/
theorem highTilt_strict_log_endpoint (z : HighTiltPoint) :
    MemLLogL (circleMode z.val) ∧
      (∀ p : StrongLpExponent, ¬ MemLp (circleMode z.val) p.val circleMeasure) ∧
      ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
        Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N x)
          atTop (𝓝 (circleMode z.val x)) :=
  ⟨memLLogL_highTilt z, not_memLp_highTilt_strong z, circle_recovery_highTilt z⟩

end RHTower.PaperThetaEndpoint
