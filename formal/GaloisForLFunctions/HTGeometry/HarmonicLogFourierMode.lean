import GaloisForLFunctions.HTGeometry.DirichletLinePartialSum

/-!
# Harmonic logarithmic rotation on Fourier modes
-/

open Complex Filter Topology Finset MeasureTheory

namespace GaloisForLFunctions

noncomputable section

/-- Logarithmically weighted sampling of a continuous function on the unit additive circle. -/
def harmonicLogCircleAverage (β θ : ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N,
      (((n : ℂ) + 1)⁻¹ *
        f ((β * Real.log ((n : ℝ) + 1) + θ : ℝ) : AddCircle (1 : ℝ)))) /
    (Real.log N : ℂ)

lemma harmonicLog_fourier_summand (β θ : ℝ) (j : ℤ) (n : ℕ) :
    ((n : ℂ) + 1)⁻¹ *
        fourier j
          ((β * Real.log ((n : ℝ) + 1) + θ : ℝ) : AddCircle (1 : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * θ) *
        gpow (2 * Real.pi * (j : ℝ) * β) ((n : ℝ) + 1) := by
  rw [fourier_coe_apply, gpow]
  norm_num
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [show ((n : ℂ) + 1)⁻¹ = Complex.exp (-(Real.log ((n : ℝ) + 1) : ℂ)) by
    calc
      ((n : ℂ) + 1)⁻¹ = (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) := by push_cast; rfl
      _ = ((Real.exp (-Real.log ((n : ℝ) + 1)) : ℝ) : ℂ) := by
        rw [Real.exp_neg, Real.exp_log hn]
      _ = Complex.exp (-(Real.log ((n : ℝ) + 1) : ℂ)) := by
        rw [← Complex.ofReal_neg, Complex.ofReal_exp]]
  rw [← Complex.exp_add]
  rw [← Complex.exp_add]
  congr 1
  ring_nf

/-- The harmonic numbers, normalized by `log N`, tend to one. -/
theorem tendsto_harmonic_div_log :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (nhds 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror : Tendsto
      (fun N : ℕ => ((harmonic N : ℝ) - Real.log N) / Real.log N) atTop (nhds 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop hlog
  have hadd := herror.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  simpa only [zero_add] using hadd.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogne : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
    ring)

theorem tendsto_dirichlet_line_div_log (α : ℝ) (hα : α ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gpow α ((n : ℝ) + 1)) / (Real.log N : ℂ))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (dirichlet_line_logCesaro α hα).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))]

/-- Every Fourier mode has the expected Haar limit under harmonic logarithmic rotation. -/
theorem harmonicLogCircleAverage_fourier (β θ : ℝ) (hβ : β ≠ 0) (j : ℤ) :
    Tendsto (fun N : ℕ => harmonicLogCircleAverage β θ (fourier j) N)
      atTop (nhds (if j = 0 then 1 else 0)) := by
  by_cases hj : j = 0
  · subst j
    simp only
    have hreal := tendsto_harmonic_div_log
    have hcomplex' : Tendsto
        (fun N : ℕ => (((harmonic N : ℝ) / Real.log N : ℝ) : ℂ)) atTop (nhds 1) := by
      simpa only [Complex.ofReal_one] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hcomplex : Tendsto
        (fun N : ℕ => ((harmonic N : ℝ) : ℂ) / (Real.log N : ℂ)) atTop (nhds 1) := by
      refine hcomplex'.congr' ?_
      filter_upwards with N
      push_cast
      rfl
    refine hcomplex.congr' ?_
    filter_upwards with N
    rw [harmonicLogCircleAverage]
    simp only [fourier_zero, mul_one]
    congr 1
    rw [harmonic]
    push_cast
    rfl
  · simp only [if_neg hj]
    have hα : 2 * Real.pi * (j : ℝ) * β ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by positivity) (by exact_mod_cast hj)) hβ
    have hmode := tendsto_dirichlet_line_div_log _ hα
    have hscaled := hmode.const_mul (Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * θ))
    simpa only [mul_zero] using hscaled.congr' (by
      filter_upwards with N
      rw [harmonicLogCircleAverage]
      simp_rw [harmonicLog_fourier_summand]
      rw [← mul_div_assoc, Finset.mul_sum])

end

end GaloisForLFunctions
