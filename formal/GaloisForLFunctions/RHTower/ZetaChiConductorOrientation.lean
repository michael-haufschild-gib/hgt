import GaloisForLFunctions.RHTower.ZetaChiDuplicationPhase
import GaloisForLFunctions.RHTower.ZetaChiCoherentPhaseModel

open Complex MeasureTheory Filter Topology
noncomputable section
namespace RHTower

private theorem continuous_bourgain_phase : Continuous bourgainOscillation := by
  unfold bourgainOscillation
  fun_prop

/-- Gamma duplication fixes the conductor phase unit exactly; no absolute
Stirling constant or branch choice is assumed. -/
theorem bourgainOscillation_hardyPhaseOffset :
    bourgainOscillation (-2 * gammaHardyPhaseOffset) =
      bourgainOscillation (Real.pi / 4) := by
  let φ : ℝ → ℝ := fun t => t - t * Real.log (t / (2 * Real.pi))
  let F : ℝ → ℂ := fun t => zetaChi (linePt t) * bourgainOscillation (-φ t)
  let κ := bourgainOscillation (-2 * gammaHardyPhaseOffset)
  have hF (t : ℝ) : F t =
      bourgainOscillation (-2 * (gammaHardyTheta t - gammaHardyThetaMain t)) := by
    dsimp only [F]
    rw [zetaChi_line_eq_exp_neg_two_theta]
    unfold bourgainOscillation
    rw [← Complex.exp_add]
    congr 1
    dsimp only [φ, gammaHardyThetaMain]
    push_cast
    ring
  have hlim : Tendsto F atTop (𝓝 κ) := by
    have h := continuous_bourgain_phase.continuousAt.tendsto.comp
      (tendsto_gammaHardyTheta_sub_main_offset.const_mul (-2))
    exact h.congr fun t => (hF t).symm
  let E : ℝ → ℝ := fun t => -2 *
    ((gammaHorizontalLogShift (1 / 4) (1 / 2) (t / 2)).im -
      (gammaHorizontalLogShift (1 / 4) (1 / 4) t).im)
  have hU := (tendsto_gammaHorizontalLogShift_im
    (σ := 1 / 4) (lam := 1 / 2) (by norm_num) (by norm_num)).comp
      ((tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).atTop_div_const
        (by norm_num : (0 : ℝ) < 2))
  have hV := tendsto_gammaHorizontalLogShift_im
    (σ := 1 / 4) (lam := 1 / 4) (by norm_num) (by norm_num)
  have hE : Tendsto E atTop (𝓝 (-(Real.pi / 4))) := by
    have h := (hU.sub hV).const_mul (-2)
    change Tendsto E atTop (𝓝 ((-2 : ℝ) *
      ((1 / 2) * (Real.pi / 2) - (1 / 4) * (Real.pi / 2)))) at h
    have he : (-2 : ℝ) * ((1 / 2) * (Real.pi / 2) - (1 / 4) * (Real.pi / 2)) =
        -(Real.pi / 4) := by ring
    rw [he] at h
    exact h
  have hB := continuous_bourgain_phase.continuousAt.tendsto.comp hE
  have hd (t : ℝ) (ht : 0 < t) :
      F (2 * t) = (F t) ^ 2 * bourgainOscillation (E t) := by
    have hφ : φ (2 * t) = 2 * φ t - 2 * t * Real.log 2 := by
      dsimp only [φ]
      have hx : (2 * t) / (2 * Real.pi) = 2 * (t / (2 * Real.pi)) := by ring
      rw [hx, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : t / (2 * Real.pi) ≠ 0)]
      ring
    dsimp only [F]
    rw [zetaChi_line_double_phase, hφ]
    change zetaChi (linePt t) ^ 2 * bourgainOscillation (-2 * t * Real.log 2) *
        bourgainOscillation (E t) * bourgainOscillation (-(2 * φ t - 2 * t * Real.log 2)) = _
    have he : bourgainOscillation (-2 * t * Real.log 2) *
        bourgainOscillation (-(2 * φ t - 2 * t * Real.log 2)) =
        bourgainOscillation (-φ t) ^ 2 := by
      unfold bourgainOscillation
      rw [← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc
      _ = zetaChi (linePt t) ^ 2 *
          (bourgainOscillation (-2 * t * Real.log 2) *
            bourgainOscillation (-(2 * φ t - 2 * t * Real.log 2))) *
          bourgainOscillation (E t) := by ring
      _ = _ := by rw [he]; ring
  have hdouble : Tendsto (fun t : ℝ => F (2 * t)) atTop (𝓝 κ) :=
    hlim.comp (Filter.Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  have hrhs : Tendsto (fun t : ℝ => F t ^ 2 * bourgainOscillation (E t)) atTop
      (𝓝 (κ ^ 2 * bourgainOscillation (-(Real.pi / 4)))) := (hlim.pow 2).mul hB
  have hid : κ = κ ^ 2 * bourgainOscillation (-(Real.pi / 4)) := by
    apply tendsto_nhds_unique hdouble
    exact hrhs.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun t ht => (hd t ht).symm)
  have hk : κ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [show ‖κ‖ = 1 from norm_bourgainOscillation _]
    norm_num
  have hunit : bourgainOscillation (-(Real.pi / 4)) *
      bourgainOscillation (Real.pi / 4) = 1 := by
    unfold bourgainOscillation
    rw [← Complex.exp_add]
    have he : I * ((-(Real.pi / 4) : ℝ) : ℂ) + I * ((Real.pi / 4 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [he, Complex.exp_zero]
  have heq := congrArg (fun z : ℂ => z * bourgainOscillation (Real.pi / 4)) hid
  have heq' : κ * bourgainOscillation (Real.pi / 4) = κ * κ := by
    calc
      _ = (κ ^ 2 * bourgainOscillation (-(Real.pi / 4))) *
          bourgainOscillation (Real.pi / 4) := heq
      _ = κ ^ 2 * (bourgainOscillation (-(Real.pi / 4)) *
          bourgainOscillation (Real.pi / 4)) := by ring
      _ = κ * κ := by rw [hunit]; ring
  exact (mul_left_cancel₀ hk heq').symm


/-- Every integer chi grade has its fully identified conductor phase,
with the same quantitative physical-height remainder. -/
theorem norm_zetaChi_integerGrade_sub_explicit_model_le (k : ℤ) {t : ℝ} (ht : 4 ≤ t) :
    ‖zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
      Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)‖ ≤
        26 * |(k : ℝ)| / t := by
  rw [← bourgainOscillation_hardyPhaseOffset]
  have hactual : zetaChi (linePt t) ^ k =
      bourgainOscillation (-2 * (k : ℝ) * gammaHardyTheta t) := by
    rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_int_mul]
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  have hmodel : bourgainOscillation (-2 * gammaHardyPhaseOffset) ^ k *
      Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I) =
      bourgainOscillation (-2 * (k : ℝ) * (gammaHardyThetaMain t + gammaHardyPhaseOffset)) := by
    unfold bourgainOscillation
    rw [← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    unfold gammaHardyThetaMain
    push_cast
    ring
  rw [hactual, hmodel]
  calc
    _ ≤ |-2 * (k : ℝ) * gammaHardyTheta t -
        (-2 * (k : ℝ) * (gammaHardyThetaMain t + gammaHardyPhaseOffset))| :=
      norm_bourgainOscillation_sub_le _ _
    _ = 2 * |(k : ℝ)| * |gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset| := by
      rw [show -2 * (k : ℝ) * gammaHardyTheta t -
        (-2 * (k : ℝ) * (gammaHardyThetaMain t + gammaHardyPhaseOffset)) =
        (-2 * (k : ℝ)) * (gammaHardyTheta t - gammaHardyThetaMain t - gammaHardyPhaseOffset) by ring,
        abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * |(k : ℝ)| * (13 / t) :=
      mul_le_mul_of_nonneg_left (abs_gammaHardyTheta_sub_main_sub_offset_le ht) (by positivity)
    _ = _ := by ring

end RHTower
