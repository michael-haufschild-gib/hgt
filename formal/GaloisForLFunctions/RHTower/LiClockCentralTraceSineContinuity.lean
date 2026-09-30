import GaloisForLFunctions.RHTower.LiClockCentralSineContourStability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the central trace sine contour in its complex clock

A continuous source on one positive-radius circle gives a jointly continuous angle-parametrized
sine kernel. The installed continuity theorem for parametric interval integrals then proves
continuity of the literal normalized negative contour at every complex clock. The source need
only be continuous on the integration circle.
-/

open Complex Set Metric Filter Topology MeasureTheory

namespace RHTower

/-- Continuity in every complex clock needs only a continuous source on its integration circle. -/
theorem continuous_liClockCentralTraceSineContour {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : ContinuousOn T (sphere (0 : ℂ) r)) :
    Continuous (fun t : ℂ => liClockCentralTraceSineContour T r t) := by
  have hTc : Continuous (fun θ : ℝ => T (circleMap 0 r θ)) :=
    hT.comp_continuous (continuous_circleMap 0 r) (fun θ => by
      simpa only [abs_of_pos hr] using circleMap_mem_sphere' 0 r θ)
  have hnz (θ : ℝ) : circleMap 0 r θ ≠ 0 := by
    intro hzero
    have hnorm := norm_circleMap_zero r θ
    rw [hzero, norm_zero, abs_of_pos hr] at hnorm
    exact hr.ne' hnorm.symm
  have hc : Continuous (fun p : ℂ × ℝ => circleMap 0 r p.2) :=
    (continuous_circleMap 0 r).comp continuous_snd
  have hsource : Continuous (fun p : ℂ × ℝ => T (circleMap 0 r p.2)) :=
    hTc.comp continuous_snd
  have hquot : Continuous (fun p : ℂ × ℝ => p.1 / circleMap 0 r p.2) :=
    continuous_fst.div hc (fun p => hnz p.2)
  have hkernel : Continuous (fun p : ℂ × ℝ =>
      (circleMap 0 r p.2 * I) *
        (T (circleMap 0 r p.2) * Complex.sin (p.1 / circleMap 0 r p.2) /
          circleMap 0 r p.2)) :=
    (hc.mul_const I).mul
      ((hsource.mul (Complex.continuous_sin.comp hquot)).div hc (fun p => hnz p.2))
  have hint : Continuous (fun t : ℂ => ∫ θ : ℝ in 0..2 * Real.pi,
      (circleMap 0 r θ * I) *
        (T (circleMap 0 r θ) * Complex.sin (t / circleMap 0 r θ) / circleMap 0 r θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hkernel
      0 (2 * Real.pi)
  simpa only [liClockCentralTraceSineContour, circleIntegral, deriv_circleMap,
    smul_eq_mul] using hint.const_mul (-(2 * (Real.pi : ℂ) * I)⁻¹)

end RHTower
