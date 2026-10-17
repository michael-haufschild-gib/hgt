import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem abs_sourceFactorialCausal_le {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    |sourceFactorialCausal N x| ≤ 2*Real.exp (x/2)/Real.sqrt N := by
  let δ := sourceFactorialWidth N
  have hp (t : ℝ) : |exponentialTentDensity δ t *
      (Real.exp (t/2)*sourceFactorialRamp N (x-t))| ≤
      exponentialTentDensity δ t * (2*Real.exp (x/2)/Real.sqrt N) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (exponentialTentDensity_nonneg δ t),
      abs_of_pos (Real.exp_pos _)]
    have hb := abs_rampBiNull_le (sourceFactorialCollar_pos hN) hN (x-t)
    change |sourceFactorialRamp N (x-t)| ≤ _ at hb
    have he : Real.exp (t/2)*Real.exp ((x-t)/2) = Real.exp (x/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ exponentialTentDensity δ t *
          (Real.exp (t/2)*(2*Real.exp ((x-t)/2)/Real.sqrt N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) (exponentialTentDensity_nonneg δ t)
      _ = _ := by rw [show Real.exp (t/2)*(2*Real.exp ((x-t)/2)/Real.sqrt N) =
          2*(Real.exp (t/2)*Real.exp ((x-t)/2))/Real.sqrt N by ring, he]
  have hc : Continuous (fun t => exponentialTentDensity δ t *
      (Real.exp (t/2)*sourceFactorialRamp N (x-t))) :=
    (continuous_exponentialTentDensity δ).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
        ((continuous_sourceFactorialRamp N).comp (continuous_const.sub continuous_id)))
  have hc' : Continuous (fun t => exponentialTentDensity δ t * (2*Real.exp (x/2)/Real.sqrt N)) :=
    (continuous_exponentialTentDensity δ).mul continuous_const
  calc
    _ ≤ ∫ t in Icc 0 (2*δ), |exponentialTentDensity δ t *
        (Real.exp (t/2)*sourceFactorialRamp N (x-t))| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Icc 0 (2*δ), exponentialTentDensity δ t * (2*Real.exp (x/2)/Real.sqrt N) :=
      integral_mono hc.abs.integrableOn_Icc hc'.integrableOn_Icc hp
    _ = _ := by
      rw [integral_mul_const, integral_Icc_exponentialTentDensity (sourceFactorialWidth_pos hN), one_mul]

theorem sourceFactorialCausal_sq_le {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    (sourceFactorialCausal N x)^2 ≤ 4*Real.exp x/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := abs_sourceFactorialCausal_le hN x
  have he : (2*Real.exp (x/2)/Real.sqrt N)^2 = 4*Real.exp x/(N : ℝ) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hn.le]
    have hp : Real.exp (x/2)^2 = Real.exp x := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hp]
    norm_num
  rw [← he, ← sq_abs (sourceFactorialCausal N x)]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem integrable_sourceFactorialCausal_sq {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun x => (sourceFactorialCausal N x)^2) := by
  apply ((continuous_sourceFactorialCausal N).pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using
    (hasCompactSupport_sourceFactorialCausal hN).mul_left (f := sourceFactorialCausal N)

/-- The squared L² norm is bounded uniformly, without a discrepancy assumption. -/
theorem integral_sourceFactorialCausal_sq_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x : ℝ, (sourceFactorialCausal N x)^2) ≤ 16 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (4*(N : ℝ)+1) := Real.log_nonneg (by have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  have he : (∫ x : ℝ, (sourceFactorialCausal N x)^2) =
      ∫ x in Icc 0 (Real.log (4*(N : ℝ)+1)), (sourceFactorialCausal N x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_cases h0 : 0 ≤ x
    · have ht : Real.log (4*(N : ℝ)+1) ≤ x := by
        by_contra! h
        exact hx ⟨h0, h.le⟩
      rw [sourceFactorialCausal_tail hN ht, zero_pow (by omega)]
    · rw [sourceFactorialCausal_zero_of_nonpos hN (by linarith), zero_pow (by omega)]
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  have hc : Continuous (fun x : ℝ => 4*Real.exp x/(N : ℝ)) := by fun_prop
  calc
    _ ≤ ∫ x in (0 : ℝ)..Real.log (4*(N : ℝ)+1), 4*Real.exp x/(N : ℝ) :=
      intervalIntegral.integral_mono_on hL
        (((continuous_sourceFactorialCausal N).pow 2).intervalIntegrable _ _)
        (hc.intervalIntegrable _ _) (fun x _ => sourceFactorialCausal_sq_le hN x)
    _ = 16 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_exp,
        Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1), Real.exp_zero]
      field_simp
      ring

/-- Small signed pairing is not obtained by letting the L² norm vanish. -/
theorem one_le_integral_sourceFactorialCausal_sq {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ∫ x : ℝ, (sourceFactorialCausal N x)^2 := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hL : Real.log (2*(N : ℝ)+1) ≤ Real.log (4*(N : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have he : (∫ x in Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ))),
      (sourceFactorialCausal N x)^2) = (4*(N : ℝ)-(2*(N : ℝ)+1))/(N : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
    have heq : (∫ x in Real.log (2*(N : ℝ)+1)..Real.log (4*(N : ℝ)),
        (sourceFactorialCausal N x)^2) =
        ∫ x in Real.log (2*(N : ℝ)+1)..Real.log (4*(N : ℝ)), Real.exp x/(N : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL] at hx
      dsimp only
      rw [sourceFactorialCausal_on_band hN hx, div_pow, Real.sq_sqrt hn.le]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq, intervalIntegral.integral_div, integral_exp,
      Real.exp_log (by positivity : 0 < 4*(N : ℝ)),
      Real.exp_log (by positivity : 0 < 2*(N : ℝ)+1)]
  have hmono := setIntegral_le_integral (s := Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ))))
    (integrable_sourceFactorialCausal_sq hN)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (sourceFactorialCausal N x)))
  rw [he] at hmono
  exact le_trans ((le_div_iff₀ hn).2 (by linarith)) hmono


end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
