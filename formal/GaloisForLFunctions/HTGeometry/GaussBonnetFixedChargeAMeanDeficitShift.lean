import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleCriticalRate
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierPath

/-!
# Quadratic coordinates for the mean-to-middle energy deficit

The normalized middle displacement has an already proved finite limit.
Its eventual bounds supply the uniform estimates needed on the shorter
mean-to-middle integration path.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMiddleQuadraticShift (τ φ : ℝ) : ℝ :=
  (egbFixedChargeAMiddleMeanRatio τ φ - 1) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)

theorem egbFixedChargeAMiddleQuadraticShift_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMiddleQuadraticShift τ φ) atBot (𝓝 (egbFixedChargeAMiddleMeanCorrection φ)) :=
  egbFixedChargeAMiddleMeanRatio_quadratic_limit φ

theorem egbFixedChargeAMiddleQuadraticShift_cross (τ φ : ℝ) :
    egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ = egbFixedChargeAMiddleMeanRatio τ φ - 1 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMiddleQuadraticShift
  field_simp

theorem egbFixedChargeAMiddleQuadraticShift_gap (τ φ : ℝ) :
    egbCoexistenceASymmetricRatio τ * egbFixedChargeAMiddleQuadraticShift τ φ = egbFixedChargeAMiddleGapCoordinate τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMiddleQuadraticShift egbFixedChargeAMiddleGapCoordinate
  field_simp

theorem egbFixedChargeAMiddleMeanCorrection_gt_neg_one (φ : ℝ) : -1 < egbFixedChargeAMiddleMeanCorrection φ := by
  have hb := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMiddleMeanCorrection
  apply (lt_div_iff₀ (show 0 < 20 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) by positivity)).2
  linarith

theorem egbFixedChargeAMiddleQuadraticShift_eventually_bounds (φ : ℝ) :
    ∀ᶠ τ in atBot, -1 < egbFixedChargeAMiddleQuadraticShift τ φ ∧ egbFixedChargeAMiddleQuadraticShift τ φ < 0 := by
  have hlo := (egbFixedChargeAMiddleQuadraticShift_critical_limit φ).eventually_const_lt
    (egbFixedChargeAMiddleMeanCorrection_gt_neg_one φ)
  have hhi := (egbFixedChargeAMiddleQuadraticShift_critical_limit φ).eventually_lt_const
    (egbFixedChargeAMiddleMeanCorrection_neg φ)
  filter_upwards [hlo, hhi] with τ hlo hhi
  exact ⟨hlo, hhi⟩

theorem egbFixedChargeAMiddleRadius_quadratic_displacement (w φ τ : ℝ) :
    egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ =
      egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ := by
  rw [egbFixedChargeAMiddleRadius_mean_formula]
  have h := egbFixedChargeAMiddleQuadraticShift_cross τ φ
  nlinarith only [congrArg (fun x : ℝ => egbFixedChargeAMeanRadius w φ τ * x) h]

end GaloisForLFunctions.HTGeometry
