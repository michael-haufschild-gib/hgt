import GaloisForLFunctions.HTGeometry.AnalyticPolynomialHardyCoefficients
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

/-!
# Taylor-coefficient algebra for polynomial Hardy factors

This module identifies the Cauchy coefficients used by the Hardy-space bounds with factorially
normalized iterated derivatives.  It then transports the finite polynomial factorization through
the Taylor map, giving the exact coefficient convolution needed in the F. and M. Riesz compactness
argument.
-/

open MeasureTheory Complex Filter Topology Set Polynomial PowerSeries Finset
open scoped Real ENNReal NNReal Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A Cauchy coefficient of a disk-analytic function is its factorially normalized derivative. -/
theorem cauchyPowerSeries_coeff_eq_iteratedDeriv_div_factorial
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1)) (k : ℕ) :
    (cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k =
      iteratedDeriv k f 0 / k.factorial := by
  have hp := hasFPowerSeriesOnBall_of_analyticOnNhd_ball hf
    (R := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
  have hfac := hp.factorial_smul (1 : ℂ) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  change k.factorial • (cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k =
      iteratedDeriv k f 0 at hfac
  have hfac' : (k.factorial : ℂ) *
      (cauchyPowerSeries f 0 (1 / 2 : NNReal)).coeff k =
      iteratedDeriv k f 0 := by
    simpa only [nsmul_eq_mul] using hfac
  rw [eq_div_iff (by exact_mod_cast k.factorial_ne_zero)]
  simpa only [mul_comm] using hfac'

/-- The Taylor map is multiplicative for functions analytic at the origin. -/
theorem taylorPS_mul_of_analyticAt_hardy {u v : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) :
    GaloisForLFunctions.taylorPS (u * v) =
      GaloisForLFunctions.taylorPS u * GaloisForLFunctions.taylorPS v := by
  ext N
  rw [GaloisForLFunctions.coeff_taylorPS, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_mul hu.contDiffAt hv.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [GaloisForLFunctions.coeff_taylorPS, GaloisForLFunctions.coeff_taylorPS]
  have hfac : (N.choose i : ℂ) * (i.factorial : ℂ) * ((N - i).factorial : ℂ) =
      (N.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hi0 : (i.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hNi0 : ((N - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (N - i)
  have hN0 : (N.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  field_simp
  rw [← hfac]
  ring

private theorem iteratedDeriv_polynomial_eval_hardy (p : Polynomial ℂ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun x => p.eval x) z =
      ((⇑Polynomial.derivative)^[j] p).eval z := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,
      show iteratedDeriv j (fun x => p.eval x) =
        fun x => ((⇑Polynomial.derivative)^[j] p).eval x from funext ih,
      Polynomial.deriv, Function.iterate_succ_apply']

/-- The analytic Taylor series of a polynomial evaluation is its formal power-series coercion. -/
theorem taylorPS_polynomial_eval_hardy (p : Polynomial ℂ) :
    GaloisForLFunctions.taylorPS (fun z : ℂ => p.eval z) = (p : PowerSeries ℂ) := by
  ext k
  rw [GaloisForLFunctions.coeff_taylorPS, iteratedDeriv_polynomial_eval_hardy,
    Polynomial.coeff_coe, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Exact coefficient convolution for any disk-analytic factorization of a polynomial. -/
theorem cauchyPowerSeries_coeff_convolution_of_mul_eq_polynomial
    {p : Polynomial ℂ} {g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 1))
    (hprod : ∀ z ∈ Metric.ball (0 : ℂ) 1, g z * h z = p.eval z) (N : ℕ) :
    p.coeff N = ∑ i ∈ Finset.range (N + 1),
      (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff i *
        (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff (N - i) := by
  have hg0 : AnalyticAt ℂ g 0 := hg 0 (by simp)
  have hh0 : AnalyticAt ℂ h 0 := hh 0 (by simp)
  have heq : (fun z => g z * h z) =ᶠ[𝓝 (0 : ℂ)] fun z => p.eval z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : ℂ) ∈ Metric.ball 0 1 by simp)]
      with z hz
    exact hprod z hz
  have hTaylorEq : GaloisForLFunctions.taylorPS (fun z => g z * h z) =
      GaloisForLFunctions.taylorPS (fun z => p.eval z) := by
    ext k
    rw [GaloisForLFunctions.coeff_taylorPS, GaloisForLFunctions.coeff_taylorPS,
      heq.iteratedDeriv_eq k]
  have hseries : (p : PowerSeries ℂ) =
      GaloisForLFunctions.taylorPS g * GaloisForLFunctions.taylorPS h := by
    have hmul : GaloisForLFunctions.taylorPS (fun z => g z * h z) =
        GaloisForLFunctions.taylorPS g * GaloisForLFunctions.taylorPS h := by
      change GaloisForLFunctions.taylorPS (g * h) = _
      exact taylorPS_mul_of_analyticAt_hardy hg0 hh0
    rw [← taylorPS_polynomial_eval_hardy p, ← hTaylorEq, hmul]
  have hcoeff := congrArg (PowerSeries.coeff N) hseries
  rw [Polynomial.coeff_coe, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simpa only [GaloisForLFunctions.coeff_taylorPS,
    cauchyPowerSeries_coeff_eq_iteratedDeriv_div_factorial hg,
    cauchyPowerSeries_coeff_eq_iteratedDeriv_div_factorial hh] using hcoeff

/-- Polynomial Hardy factors with uniform square-sum bounds and exact coefficient convolution. -/
theorem exists_polynomial_hardy_coefficients_with_convolution {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ g h : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball 0 1) ∧
      AnalyticOnNhd ℂ h (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, g z * h z = p.eval z) ∧
      Memℓp (fun k => (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      Memℓp (fun k => (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      (∑' k, ‖(cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k‖ ^ 2)
        ≤ polynomialBoundaryL1 p ∧
      (∑' k, ‖(cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k‖ ^ 2)
        ≤ polynomialBoundaryL1 p ∧
      ∀ N, p.coeff N = ∑ i ∈ Finset.range (N + 1),
        (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff i *
          (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff (N - i) := by
  obtain ⟨g, h, hg, hh, hprod, hgl2, hhl2, hgbound, hhbound⟩ :=
    exists_polynomial_hardy_coefficients hp
  exact ⟨g, h, hg, hh, hprod, hgl2, hhl2, hgbound, hhbound,
    cauchyPowerSeries_coeff_convolution_of_mul_eq_polynomial hg hh hprod⟩

/-- The coefficient factorization in a form valid for every polynomial, including zero. -/
theorem exists_polynomial_hardy_coefficients_with_convolution_all (p : ℂ[X]) :
    ∃ g h : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball 0 1) ∧
      AnalyticOnNhd ℂ h (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, g z * h z = p.eval z) ∧
      Memℓp (fun k => (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      Memℓp (fun k => (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      (∑' k, ‖(cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k‖ ^ 2)
        ≤ polynomialBoundaryL1 p ∧
      (∑' k, ‖(cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k‖ ^ 2)
        ≤ polynomialBoundaryL1 p ∧
      ∀ N, p.coeff N = ∑ i ∈ Finset.range (N + 1),
        (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff i *
          (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff (N - i) := by
  by_cases hp : p = 0
  · subst p
    have hcoeff : ∀ k : ℕ,
        (cauchyPowerSeries (fun _ : ℂ => (0 : ℂ)) 0 (1 / 2 : NNReal)).coeff k = 0 := by
      intro k
      rw [cauchyPowerSeries_coeff_eq_iteratedDeriv_div_factorial
        (f := fun _ : ℂ => (0 : ℂ)) analyticOnNhd_const]
      simp
    have hzeroMem : Memℓp (fun _ : ℕ => (0 : ℂ)) 2 := by
      apply memℓp_gen
      simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    refine ⟨fun _ => 0, fun _ => 0, analyticOnNhd_const, analyticOnNhd_const, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp
    · simpa only [hcoeff] using hzeroMem
    · simpa only [hcoeff] using hzeroMem
    · have hboundary : polynomialBoundaryL1 (0 : ℂ[X]) = 0 := by
        simp [polynomialBoundaryL1]
      rw [hboundary]
      simp_rw [hcoeff]
      simp
    · have hboundary : polynomialBoundaryL1 (0 : ℂ[X]) = 0 := by
        simp [polynomialBoundaryL1]
      rw [hboundary]
      simp_rw [hcoeff]
      simp
    · intro N
      simp_rw [hcoeff]
      simp
  · exact exists_polynomial_hardy_coefficients_with_convolution hp

end

end GaloisForLFunctions.HTGeometry
