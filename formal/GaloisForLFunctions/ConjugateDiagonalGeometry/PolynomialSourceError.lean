import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialSourceScale

/-!
# Polynomial local error for the fixed-strip xi regulator

The existing logarithmic-square mass bound is applied at the linear radius
containing the stretched cutoff. The prescribed polynomial logarithmic
scale pays the sixth-degree mass and the actual fixed derivative control.
-/

open Complex MeasureTheory Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower

/-- The stretched source disc inherits a sixth-degree logarithmic-square mass bound. -/
theorem exists_stripSource_log_square_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      IntegrableOn (fun z : ℂ => Real.log ‖xi z‖ ^ 2)
        (closedBall 0 (11 * ((n : ℝ) + 1))) ∧
      (∫ z in closedBall 0 (11 * ((n : ℝ) + 1)), Real.log ‖xi z‖ ^ 2) ≤
        C * ((n : ℝ) + 1) ^ 6 := by
  obtain ⟨C, hC, hb⟩ := exists_xi_log_square_polynomial_bound
  refine ⟨C * 11 ^ 6, by positivity, fun n => ?_⟩
  have h := hb (11 * n + 9)
  have hr : ((11 * n + 9 : ℕ) : ℝ) + 2 = 11 * ((n : ℝ) + 1) := by
    push_cast
    ring
  rw [hr] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hm : ((11 * n + 9 : ℕ) : ℝ) + 1 ≤ 11 * ((n : ℝ) + 1) := by
    push_cast
    linarith
  calc
    C * (((11 * n + 9 : ℕ) : ℝ) + 1) ^ 6 ≤
        C * (11 * ((n : ℝ) + 1)) ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm 6) hC.le
    _ = _ := by rw [mul_pow]; ring

/-- One actual constant bounds the local xi potential error after cutoff differentiation. -/
theorem exists_polynomialSourceLocalError_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      stripSourceCutoffControl *
        xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1)) ≤
      D / ((n : ℝ) + 1) ^ 14 := by
  obtain ⟨C, hC, hCb⟩ := exists_stripSource_log_square_bound
  refine ⟨121 * Real.pi + 8 * C, by positivity, fun n hn => ?_⟩
  have ht : 0 < (n : ℝ) + 1 := by positivity
  have ht1 : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hr : 0 ≤ 11 * ((n : ℝ) + 1) := by positivity
  have hK := polynomialSourceLogScale_ge_four hn
  have hK0 := polynomialSourceLogScale_pos n
  have hη := polynomialSourceRegulator_pos n
  have hlog : IntegrableOn (fun z : ℂ => Real.log ‖xi z‖)
      (closedBall 0 (11 * ((n : ℝ) + 1))) := by
    simpa only [abs_of_nonneg hr] using integrableOn_xi_log_norm 0 (11 * ((n : ℝ) + 1))
  have herr : IntegrableOn
      (fun z : ℂ => |xiLogPotential (polynomialSourceRegulator n) z - Real.log ‖xi z‖|)
      (closedBall 0 (11 * ((n : ℝ) + 1))) := by
    have hi : IntegrableOn (fun z : ℂ =>
        xiLogPotential (polynomialSourceRegulator n) z - Real.log ‖xi z‖)
        (closedBall 0 (11 * ((n : ℝ) + 1))) :=
      ((contDiff_xiLogPotential hη).continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) (11 * ((n : ℝ) + 1)))).sub hlog
    convert hi.norm using 1
    rfl
  have hconst : IntegrableOn (fun _ : ℂ =>
      (1 / 2 : ℝ) * Real.exp (-polynomialSourceLogScale n / 2))
      (closedBall 0 (11 * ((n : ℝ) + 1))) :=
    continuous_const.continuousOn.integrableOn_compact
      (isCompact_closedBall 0 (11 * ((n : ℝ) + 1)))
  have hsq := (hCb n).1.const_mul (8 / polynomialSourceLogScale n)
  -- The pointwise logarithmic estimate is used off the null xi divisor.
  have hlocal : xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1)) ≤
      (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2 / 2) * Real.exp (-polynomialSourceLogScale n / 2) +
      (8 / polynomialSourceLogScale n) * (C * ((n : ℝ) + 1) ^ 6) := by
    unfold xiLocalPotentialError
    rw [abs_of_nonneg hr]
    calc
      (∫ z in closedBall 0 (11 * ((n : ℝ) + 1)),
          |xiLogPotential (polynomialSourceRegulator n) z - Real.log ‖xi z‖|) ≤
          ∫ z in closedBall 0 (11 * ((n : ℝ) + 1)),
            (1 / 2 : ℝ) * Real.exp (-polynomialSourceLogScale n / 2) +
              (8 / polynomialSourceLogScale n) * Real.log ‖xi z‖ ^ 2 := by
        apply integral_mono_ae herr (hconst.add hsq)
        filter_upwards [ae_restrict_of_ae xi_ne_zero_ae] with z hz
        exact xiLogPotential_exp_error_le_log_square hK hz
      _ = (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2 / 2) * Real.exp (-polynomialSourceLogScale n / 2) +
          (8 / polynomialSourceLogScale n) *
            ∫ z in closedBall 0 (11 * ((n : ℝ) + 1)), Real.log ‖xi z‖ ^ 2 := by
        rw [integral_add hconst hsq, integral_const, integral_const_mul]
        simp only [measureReal_restrict_apply_univ, smul_eq_mul]
        rw [measureReal_def, Complex.volume_closedBall]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
          ENNReal.coe_toReal, NNReal.coe_real_pi]
        ring
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hCb n).2 (by positivity : 0 ≤ 8 / polynomialSourceLogScale n))
  -- The fixed integer coefficient pays the entire cutoff derivative control.
  have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
  have hcoef : stripSourceCutoffControl * (8 / polynomialSourceLogScale n) ≤
      8 / ((n : ℝ) + 1) ^ 20 := by
    calc
      stripSourceCutoffControl * (8 / polynomialSourceLogScale n) =
          8 * (stripSourceCutoffControl / polynomialSourceLogScale n) := by ring
      _ ≤ 8 * (1 / ((n : ℝ) + 1) ^ 20) :=
        mul_le_mul_of_nonneg_left (stripSourceControl_div_polynomialScale_le n)
          (by norm_num : (0 : ℝ) ≤ 8)
      _ = _ := by ring
  have hpow : ((n : ℝ) + 1) ^ 14 ≤ ((n : ℝ) + 1) ^ 18 := by
    have h4 : 1 ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ ht1
    have h := le_mul_of_one_le_right (by positivity : 0 ≤ ((n : ℝ) + 1) ^ 14) h4
    simpa only [← pow_add] using h
  calc
    stripSourceCutoffControl * xiLocalPotentialError (polynomialSourceRegulator n) 0
        (11 * ((n : ℝ) + 1)) ≤ stripSourceCutoffControl *
        ((Real.pi * (11 * ((n : ℝ) + 1)) ^ 2 / 2) * Real.exp (-polynomialSourceLogScale n / 2) +
          (8 / polynomialSourceLogScale n) * (C * ((n : ℝ) + 1) ^ 6)) :=
      mul_le_mul_of_nonneg_left hlocal hM
    _ = (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2 / 2) *
          (stripSourceCutoffControl * Real.exp (-polynomialSourceLogScale n / 2)) +
        (stripSourceCutoffControl * (8 / polynomialSourceLogScale n)) * (C * ((n : ℝ) + 1) ^ 6) := by ring
    _ ≤ (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2 / 2) * (2 / ((n : ℝ) + 1) ^ 20) +
        (8 / ((n : ℝ) + 1) ^ 20) * (C * ((n : ℝ) + 1) ^ 6) :=
      add_le_add (mul_le_mul_of_nonneg_left (stripSourceControl_exp_half_le n) (by positivity))
        (mul_le_mul_of_nonneg_right hcoef (by positivity))
    _ = 121 * Real.pi / ((n : ℝ) + 1) ^ 18 + 8 * C / ((n : ℝ) + 1) ^ 14 := by
      field_simp [ht.ne']
      ring
    _ ≤ 121 * Real.pi / ((n : ℝ) + 1) ^ 14 + 8 * C / ((n : ℝ) + 1) ^ 14 := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polynomialSourceLocalError_bound
