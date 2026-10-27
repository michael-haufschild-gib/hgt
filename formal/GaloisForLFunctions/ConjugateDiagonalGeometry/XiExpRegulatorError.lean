import GaloisForLFunctions.ConjugateDiagonalGeometry.XiLogSquareIntegral
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiArbitraryRegulator
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceCutoffControl
import GaloisForLFunctions.HTGeometry.LogRegularizationSquareError

/-!
# Prescribed exponential regulation of the xi source

The logarithmic scale absorbs all derivatives of the fixed source cutoff.
A polynomial bound for the square of the actual xi logarithm controls its
local potential error, including neighborhoods of multiple zeros.
-/

open Complex MeasureTheory Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower HTGeometry

/-- The logarithmic regulator scale uses only the fixed cutoff and its derivative control. -/
def explicitSourceLogScale (n : ℕ) : ℝ :=
  Real.exp (((n : ℝ) + 1) ^ 4) * sourceCutoffControl n

/-- A prescribed positive regulator with no source-error test or divisor coordinates. -/
def explicitSourceRegulator (n : ℕ) : ℝ := Real.exp (-explicitSourceLogScale n)

theorem explicitSourceRegulator_pos (n : ℕ) : 0 < explicitSourceRegulator n := Real.exp_pos _

theorem one_le_sourceCutoffControl (n : ℕ) : 1 ≤ sourceCutoffControl n := by
  unfold sourceCutoffControl
  linarith only [norm_nonneg (sourceCutoffDerivative n 1),
    norm_nonneg (sourceCutoffDerivative n Complex.I), norm_nonneg (sourceCutoffLaplacian n)]

lemma source_radius_fourth_ge_sixteen {n : ℕ} (hn : 1 ≤ n) :
    16 ≤ ((n : ℝ) + 1) ^ 4 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (show 2 ≤ (n : ℝ) + 1 by linarith only [hn']) 4
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at h
  exact h

lemma explicitSourceLogScale_ge_four {n : ℕ} (hn : 1 ≤ n) :
    4 ≤ explicitSourceLogScale n := by
  have hx := source_radius_fourth_ge_sixteen hn
  have h := Real.log_le_sub_one_of_pos (Real.exp_pos (((n : ℝ) + 1) ^ 4))
  rw [Real.log_exp] at h
  have hm := le_mul_of_one_le_right (Real.exp_pos (((n : ℝ) + 1) ^ 4)).le
    (one_le_sourceCutoffControl n)
  unfold explicitSourceLogScale
  linarith only [hx, h, hm]

lemma xiLogPotential_exp_error_le_log_square {K : ℝ} (hK : 4 ≤ K)
    {z : ℂ} (hz : xi z ≠ 0) :
    |xiLogPotential (Real.exp (-K)) z - Real.log ‖xi z‖| ≤
      (1 / 2 : ℝ) * Real.exp (-K / 2) + (8 / K) * Real.log ‖xi z‖ ^ 2 := by
  have hs : (xi z).re ^ 2 + (xi z).im ^ 2 = ‖xi z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [xiLogPotential, radialLogPotential, hs]
  exact half_log_regularization_le_log_square (norm_pos_iff.mpr hz) hK

/-- The explicit regulator has a uniform polynomial-times-exponential local error. -/
theorem exists_explicitSourceLocalError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      sourceCutoffControl n *
        xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
      (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
        Real.exp (-((n : ℝ) + 1) ^ 4) := by
  obtain ⟨C, hC, hCb⟩ := exists_xi_log_square_polynomial_bound
  refine ⟨C, hC, fun n hn => ?_⟩
  have hr : 0 ≤ (n : ℝ) + 2 := by positivity
  have hK := explicitSourceLogScale_ge_four hn
  have hK0 : 0 < explicitSourceLogScale n := by linarith only [hK]
  have hη := explicitSourceRegulator_pos n
  have hlog : IntegrableOn (fun z : ℂ => Real.log ‖xi z‖) (closedBall 0 ((n : ℝ) + 2)) := by
    simpa only [abs_of_nonneg hr] using integrableOn_xi_log_norm 0 ((n : ℝ) + 2)
  have herr : IntegrableOn (fun z : ℂ => |xiLogPotential (explicitSourceRegulator n) z - Real.log ‖xi z‖|)
      (closedBall 0 ((n : ℝ) + 2)) := by
    have hi : IntegrableOn (fun z : ℂ =>
        xiLogPotential (explicitSourceRegulator n) z - Real.log ‖xi z‖)
        (closedBall 0 ((n : ℝ) + 2)) :=
      ((contDiff_xiLogPotential hη).continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2))).sub hlog
    convert hi.norm using 1
    rfl
  have hconst : IntegrableOn (fun _ : ℂ =>
      (1 / 2 : ℝ) * Real.exp (-explicitSourceLogScale n / 2))
      (closedBall 0 ((n : ℝ) + 2)) :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall 0 ((n : ℝ) + 2))
  have hsq := (hCb n).1.const_mul (8 / explicitSourceLogScale n)
  -- Integrate the scalar error off the null zero divisor.
  have hlocal : xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
      (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-explicitSourceLogScale n / 2) +
      (8 / explicitSourceLogScale n) * (C * ((n : ℝ) + 1) ^ 6) := by
    unfold xiLocalPotentialError
    rw [abs_of_nonneg hr]
    calc
      (∫ z in closedBall 0 ((n : ℝ) + 2),
          |xiLogPotential (explicitSourceRegulator n) z - Real.log ‖xi z‖|) ≤
          ∫ z in closedBall 0 ((n : ℝ) + 2),
            (1 / 2 : ℝ) * Real.exp (-explicitSourceLogScale n / 2) +
              (8 / explicitSourceLogScale n) * Real.log ‖xi z‖ ^ 2 := by
        apply integral_mono_ae herr (hconst.add hsq)
        filter_upwards [ae_restrict_of_ae xi_ne_zero_ae] with z hz
        exact xiLogPotential_exp_error_le_log_square hK hz
      _ = (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-explicitSourceLogScale n / 2) +
          (8 / explicitSourceLogScale n) *
            ∫ z in closedBall 0 ((n : ℝ) + 2), Real.log ‖xi z‖ ^ 2 := by
        rw [integral_add hconst hsq, integral_const, integral_const_mul]
        simp only [measureReal_restrict_apply_univ, smul_eq_mul]
        rw [measureReal_def, Complex.volume_closedBall]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
          ENNReal.coe_toReal, NNReal.coe_real_pi]
        ring
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hCb n).2 (by positivity : 0 ≤ 8 / explicitSourceLogScale n))
  -- The prescribed scale absorbs the cutoff control in both error terms.
  have hmexp : sourceCutoffControl n * Real.exp (-explicitSourceLogScale n / 2) ≤
      Real.exp (-((n : ℝ) + 1) ^ 4) :=
    mul_exp_neg_exp_mul_half_le_exp_neg (source_radius_fourth_ge_sixteen hn)
      (one_le_sourceCutoffControl n)
  have hcancel : sourceCutoffControl n * (8 / explicitSourceLogScale n) =
      8 * Real.exp (-((n : ℝ) + 1) ^ 4) := by
    unfold explicitSourceLogScale
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos (((n : ℝ) + 1) ^ 4)).ne', (sourceCutoffControl_pos n).ne']
  calc
    sourceCutoffControl n * xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
        sourceCutoffControl n *
          ((Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-explicitSourceLogScale n / 2) +
            (8 / explicitSourceLogScale n) * (C * ((n : ℝ) + 1) ^ 6)) :=
      mul_le_mul_of_nonneg_left hlocal (sourceCutoffControl_pos n).le
    _ = (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) *
          (sourceCutoffControl n * Real.exp (-explicitSourceLogScale n / 2)) +
          (sourceCutoffControl n * (8 / explicitSourceLogScale n)) * (C * ((n : ℝ) + 1) ^ 6) := by ring
    _ ≤ (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-((n : ℝ) + 1) ^ 4) +
        (8 * Real.exp (-((n : ℝ) + 1) ^ 4)) * (C * ((n : ℝ) + 1) ^ 6) := by
      rw [hcancel]
      exact add_le_add (mul_le_mul_of_nonneg_left hmexp
        (by positivity : 0 ≤ Real.pi * ((n : ℝ) + 2) ^ 2 / 2)) le_rfl
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_explicitSourceLocalError_bound
