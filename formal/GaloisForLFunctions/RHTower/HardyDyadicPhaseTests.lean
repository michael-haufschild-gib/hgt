import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation
import GaloisForLFunctions.RHTower.TrigammaVerticalLowerBound
import GaloisForLFunctions.RHTower.VanDerCorputLocal

/-!
# Van der Corput bounds for a twisted Hardy phase on a dyadic window

On `[T, 2T]` the Hardy phase curvature is bounded below by `1/(200T)`, so the second-derivative
test bounds every twisted cell integral by `O(\sqrt T)`.  Above the conductor — for
`L \ge \log(5\sqrt T)` — the phase velocity `\theta'(\tau) - L` is at most `-1`, so the
first-derivative test bounds the same integral by an absolute constant.  These are the two
regimes that split the direct edge of the approximate functional equation.
-/

open Set MeasureTheory Complex

namespace RHTower

noncomputable section

theorem curvature_lower_dyadic {T τ : ℝ} (hT : 4 ≤ T) (hτ : τ ∈ Icc T (2 * T)) :
    1 / (200 * T) ≤ deriv gammaHardyPhaseRate τ := by
  have hτ4 : (4 : ℝ) ≤ τ := le_trans hT hτ.1
  have hb := deriv_gammaHardyPhaseRate_lower_bound hτ4
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hmono : 1 / (200 * T) ≤ 1 / (100 * τ) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith [hτ.2]
  linarith

theorem one_le_abs_rate_sub_above_conductor {T τ L : ℝ} (hT : 16 ≤ T)
    (hτ : τ ∈ Icc T (2 * T)) (hL : Real.log (5 * Real.sqrt T) ≤ L) :
    1 ≤ |gammaHardyPhaseRate τ - L| := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
  have hτ16 : (16 : ℝ) ≤ τ := le_trans hT hτ.1
  have hbound := gammaHardyPhaseRate_sub_log_conductor_bound hτ0
  have hup : gammaHardyPhaseRate τ
      ≤ Real.log (τ / (2 * Real.pi)) / 2 + (33 / (16 * τ ^ (2 : ℕ)) + Real.pi / (2 * τ)) := by
    have := (abs_le.mp hbound).2
    linarith
  -- monotonicity of the conductor logarithm
  have hlogmono : Real.log (τ / (2 * Real.pi)) ≤ Real.log (T / Real.pi) := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h1 : τ / (2 * Real.pi) ≤ T / Real.pi := by
      rw [div_le_div_iff₀ (by positivity) hpi]
      nlinarith [hτ.2]
    exact Real.log_le_log (by positivity) h1
  -- the error terms
  have herr1 : 33 / (16 * τ ^ (2 : ℕ)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have herr2 : Real.pi / (2 * τ) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_lt_d2]
  -- the log split
  have hsqrt : Real.log (5 * Real.sqrt T) = Real.log 5 + Real.log T / 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hT0.le]
  have hlog5 : (1.386 : ℝ) ≤ Real.log 5 := by
    have h4 : Real.log 4 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    linarith [Real.log_two_gt_d9]
  have hlogpi : (1 : ℝ) ≤ Real.log Real.pi := by
    have he : Real.exp 1 ≤ Real.pi := by
      linarith [Real.exp_one_lt_d9, Real.pi_gt_d2]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log Real.pi := Real.log_le_log (Real.exp_pos 1) he
  have hsplit : Real.log (T / Real.pi) = Real.log T - Real.log Real.pi :=
    Real.log_div hT0.ne' Real.pi_pos.ne'
  have hkey : gammaHardyPhaseRate τ - L ≤ -1 := by
    rw [hsqrt] at hL
    rw [hsplit] at hlogmono
    linarith
  rw [abs_of_nonpos (by linarith)]
  linarith

/-! ## The two single-term oscillatory bounds -/

theorem norm_integral_twist_second_le {T : ℝ} (hT : 4 ≤ T) (L : ℝ) (c : ℂ) :
    ‖∫ τ in T..(2 * T), c * Complex.exp (Complex.I * (hardyTwistPhase L τ : ℂ))‖
      ≤ 64 * ‖c‖ * Real.sqrt (200 * T) := by
  have hab : T ≤ 2 * T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hmu : (0 : ℝ) < 1 / (200 * T) := by positivity
  have h := secondDerivTestOn (a := T) (b := 2 * T) (mu := 1 / (200 * T)) hab hmu
    (φ := hardyTwistPhase L) (φ' := fun τ => gammaHardyPhaseRate τ - L)
    (φ'' := deriv gammaHardyPhaseRate) (A := fun _ => c) (A' := fun _ => 0)
    (fun τ _ => hasDerivAt_hardyTwistPhase L τ)
    (fun τ _ => hasDerivAt_hardyTwistRate L τ)
    continuous_deriv_gammaHardyPhaseRate.continuousOn
    (fun τ _ => hasDerivAt_const τ c)
    continuousOn_const
    (fun τ hτ => curvature_lower_dyadic hT hτ)
  have hzero : (∫ _ : ℝ in T..(2 * T), ‖(0 : ℂ)‖) = 0 := by simp
  rw [hzero] at h
  have hsqrt : Real.sqrt (1 / (200 * T)) = (Real.sqrt (200 * T))⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  rw [hsqrt] at h
  have hs0 : (0 : ℝ) < Real.sqrt (200 * T) := Real.sqrt_pos.mpr (by positivity)
  refine le_trans h (le_of_eq ?_)
  field_simp
  ring

theorem norm_integral_twist_first_le {T L : ℝ} (hT : 16 ≤ T)
    (hL : Real.log (5 * Real.sqrt T) ≤ L) (c : ℂ) :
    ‖∫ τ in T..(2 * T), c * Complex.exp (Complex.I * (hardyTwistPhase L τ : ℂ))‖
      ≤ 8 * ‖c‖ := by
  have hab : T ≤ 2 * T := by linarith
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have h := firstDerivTestOn (a := T) (b := 2 * T) (lam := 1) hab one_pos
    (φ := hardyTwistPhase L) (φ' := fun τ => gammaHardyPhaseRate τ - L)
    (φ'' := deriv gammaHardyPhaseRate) (A := fun _ => c) (A' := fun _ => 0)
    (fun τ _ => hasDerivAt_hardyTwistPhase L τ)
    (fun τ _ => hasDerivAt_hardyTwistRate L τ)
    continuous_deriv_gammaHardyPhaseRate.continuousOn
    (fun τ _ => hasDerivAt_const τ c)
    continuousOn_const
    (fun τ hτ => le_trans (by positivity) (curvature_lower_dyadic hT4 hτ))
    (fun τ hτ => one_le_abs_rate_sub_above_conductor hT hτ hL)
  have hzero : (∫ _ : ℝ in T..(2 * T), ‖(0 : ℂ)‖) = 0 := by simp
  rw [hzero] at h
  refine le_trans h (le_of_eq ?_)
  ring

end

end RHTower
