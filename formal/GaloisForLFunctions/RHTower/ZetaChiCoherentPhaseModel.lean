import GaloisForLFunctions.RHTower.HardyPhaseOffset
import GaloisForLFunctions.RHTower.ZetaChiIntegerGradeOscillation
import GaloisForLFunctions.RHTower.BourgainPhasePerturbation

open Complex
noncomputable section
namespace RHTower

/-- One fixed unit gives the actual conductor phase model for every integer
chi grade. The error retains the grade and physical-height dependence. -/
theorem exists_zetaChi_coherent_integerGrade_model :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ k : ℤ, ∀ t : ℝ, 4 ≤ t →
      ‖zetaChi (linePt t) ^ k - κ ^ k *
        Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)‖ ≤
          26 * |(k : ℝ)| / t := by
  let κ := bourgainOscillation (-2 * gammaHardyPhaseOffset)
  refine ⟨κ, norm_bourgainOscillation _, ?_⟩
  intro k t ht
  have hactual : zetaChi (linePt t) ^ k =
      bourgainOscillation (-2 * (k : ℝ) * gammaHardyTheta t) := by
    rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_int_mul]
    dsimp only [bourgainOscillation]
    congr 1
    push_cast
    ring
  have hmodel : κ ^ k *
      Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I) =
        bourgainOscillation (-2 * (k : ℝ) * (gammaHardyThetaMain t + gammaHardyPhaseOffset)) := by
    dsimp only [κ, bourgainOscillation]
    rw [← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    dsimp only [gammaHardyThetaMain]
    push_cast
    ring
  rw [hactual, hmodel]
  have he : -2 * (k : ℝ) * gammaHardyTheta t -
      (-2 * (k : ℝ) * (gammaHardyThetaMain t + gammaHardyPhaseOffset)) =
        (-2 * (k : ℝ)) * (gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset) := by
    ring
  calc
    _ ≤ |-2 * (k : ℝ) * gammaHardyTheta t -
        (-2 * (k : ℝ) * (gammaHardyThetaMain t + gammaHardyPhaseOffset))| :=
      norm_bourgainOscillation_sub_le _ _
    _ = 2 * |(k : ℝ)| * |gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset| := by
      rw [he, abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * |(k : ℝ)| * (13 / t) :=
      mul_le_mul_of_nonneg_left (abs_gammaHardyTheta_sub_main_sub_offset_le ht) (by positivity)
    _ = _ := by ring

end RHTower
