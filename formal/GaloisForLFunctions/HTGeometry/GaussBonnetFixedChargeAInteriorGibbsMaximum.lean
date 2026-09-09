import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsBounds
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAIntervalGibbsMaximum

/-!
# Exact location of the maximum in the physical interior profile

The full barrier is attained precisely at the moving intermediate
coordinate. The leading symmetric profile has its maximum at zero;
the exact finite-state coordinate retains the asymmetric displacement.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInteriorRadius_middle_iff (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ ψ = egbFixedChargeAMiddleRadius w φ τ ↔
      sin ψ = egbFixedChargeAMiddleGapCoordinate τ φ := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMiddleRadius_mean_formula]
  unfold egbFixedChargeAInteriorRadius egbFixedChargeAMiddleGapCoordinate
  constructor
  · intro h
    have he := mul_left_cancel₀ hm.ne' h
    apply (eq_div_iff hd.ne').2
    nlinarith only [he]
  · intro h
    have hc := (eq_div_iff hd.ne').1 h
    have he : 1 + egbCoexistenceASymmetricRatio τ * sin ψ = egbFixedChargeAMiddleMeanRatio τ φ := by
      nlinarith only [hc]
    rw [he]

theorem egbFixedChargeAInteriorGibbsGap_maximizer_iff (w φ τ l ψ : ℝ) :
    egbFixedChargeAInteriorGibbsGap w φ τ l ψ = egbFixedChargeAGibbsBarrier w φ τ l ↔
      sin ψ = egbFixedChargeAMiddleGapCoordinate τ φ := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hx := egbFixedChargeAInteriorReducedRadius_pos τ ψ
  have hm := egbCoexistenceAMiddleRadius_pos τ (egbFixedChargeAAngle τ φ)
  have hb := egbFixedChargeAInteriorReducedRadius_log_bounds τ ψ
  have hmax := egbCoexistenceAReducedLogGibbs_interval_maximizer_iff τ (egbFixedChargeAAngle τ φ)
    (log (egbFixedChargeAInteriorReducedRadius τ ψ))
  rw [egbFixedChargeAInteriorGibbsGap_reduced_formula, egbFixedChargeAGibbsBarrier_reduced_formula]
  have he : (egbCoexistenceAReducedLogGibbs τ (egbFixedChargeAAngle τ φ) (log (egbFixedChargeAInteriorReducedRadius τ ψ)) =
      egbCoexistenceAReducedLogGibbs τ (egbFixedChargeAAngle τ φ) (log (egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)))) ↔
      log (egbFixedChargeAInteriorReducedRadius τ ψ) = log (egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)) := by
    constructor
    · intro h; exact hmax.mp ⟨hb, h⟩
    · intro h; rw [h]
  have hlog : log (egbFixedChargeAInteriorReducedRadius τ ψ) = log (egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)) ↔
      egbFixedChargeAInteriorReducedRadius τ ψ = egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ) := by
    constructor
    · intro h
      simpa only [exp_log hx, exp_log hm] using congrArg exp h
    · intro h; rw [h]
  have hradius : egbFixedChargeAInteriorReducedRadius τ ψ = egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ) ↔
      egbFixedChargeAInteriorRadius w φ τ ψ = egbFixedChargeAMiddleRadius w φ τ := by
    rw [egbFixedChargeAInteriorRadius_reduced_formula]
    unfold egbFixedChargeAMiddleRadius
    constructor
    · intro h; rw [h]
    · intro h; exact mul_left_cancel₀ hR.ne' h
  rw [← egbFixedChargeAInteriorRadius_middle_iff w φ τ ψ, ← hradius, ← hlog, ← he]
  constructor
  · intro h
    have hc := mul_left_cancel₀ hR.ne' h
    linarith only [hc]
  · intro h; rw [h]

theorem egbFixedChargeAInteriorGibbsGap_ratio_eq_one_iff (w φ τ l ψ : ℝ) :
    egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbFixedChargeAGibbsBarrier w φ τ l = 1 ↔
      sin ψ = egbFixedChargeAMiddleGapCoordinate τ φ := by
  rw [div_eq_iff (egbFixedChargeAGibbsBarrier_pos w φ τ l).ne', one_mul,
    egbFixedChargeAInteriorGibbsGap_maximizer_iff]

end GaloisForLFunctions.HTGeometry
