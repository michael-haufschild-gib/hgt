import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The horizontal segments of the truncated Perron contour

Perron's lemma bounds the truncated vertical integral of `y^s/s` against the indicator of `y > 1`, and its
proof shifts the contour to `Re s = -A` and lets `A → ∞`.  The cost of the shift is the two horizontal
segments at height `±T`, and on those the kernel is elementary: `‖y^s‖ = y^{Re s}` while `‖s‖ ≥ T`, so

`‖∫_{-A}^{σ} y^{u+iT}/(u+iT) du‖ ≤ (1/T) ∫_{-A}^{σ} y^u du ≤ y^σ/(T log y)`   for `y > 1`,

uniformly in `A`.  This is the estimate that produces Perron's `min(1, 1/(T|log y|))` factor, the factor
that makes truncated Perron the only device whose error is a *global* Dirichlet-series sum rather than a
short-interval divisor estimate.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Complex MeasureTheory intervalIntegral

/-- The exponential integral in the form the Perron contour needs. -/
theorem integral_exp_mul_const (L : ℝ) (hL : L ≠ 0) (a b : ℝ) :
    (∫ u in a..b, Real.exp (u * L)) = (Real.exp (b * L) - Real.exp (a * L)) / L := by
  rw [intervalIntegral.integral_comp_mul_right (f := Real.exp) (c := L) hL, integral_exp,
    smul_eq_mul]
  field_simp

/-- **The horizontal segment of the Perron contour.**  On the line `Im s = T` the kernel `y^s/s` has
norm at most `y^{Re s}/T`, so the segment integral is at most `y^σ/(T log y)`. -/
theorem norm_integral_horizontal_le {y : ℝ} (hy : 1 < y) {σ A T : ℝ} (hT : 0 < T)
    (hAσ : -A ≤ σ) :
    ‖∫ u in (-A)..σ, ((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
        / ((u : ℂ) + (T : ℝ) * Complex.I)‖
      ≤ y ^ σ / (T * Real.log y) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hL : (0 : ℝ) < Real.log y := Real.log_pos hy
  set L : ℝ := Real.log y with hLdef
  have hrpow : ∀ u : ℝ, y ^ u = Real.exp (u * L) := by
    intro u
    rw [hLdef, Real.rpow_def_of_pos hy0, mul_comm]
  have hcont : ContinuousOn (fun u : ℝ => ((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
      / ((u : ℂ) + (T : ℝ) * Complex.I)) (Set.uIcc (-A) σ) := by
    refine ContinuousOn.div ?_ (Continuous.continuousOn (by fun_prop)) ?_
    · refine Continuous.continuousOn ?_
      refine Continuous.const_cpow (by fun_prop) ?_
      exact Or.inl (by exact_mod_cast hy0.ne')
    · intro u _ hzero
      have him : ((u : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
      rw [hzero] at him
      simp at him
      exact absurd him.symm hT.ne'
  have hmaj : Continuous fun u : ℝ => Real.exp (u * L) / T := by fun_prop
  have hnorm : ∀ u ∈ Set.Icc (-A) σ,
      ‖((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I)) / ((u : ℂ) + (T : ℝ) * Complex.I)‖
        ≤ Real.exp (u * L) / T := by
    intro u _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((u : ℂ) + (T : ℝ) * Complex.I).re = u := by simp
    rw [hre, ← hrpow u]
    have hden : T ≤ ‖(u : ℂ) + (T : ℝ) * Complex.I‖ := by
      have him : ((u : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
      calc T = |((u : ℂ) + (T : ℝ) * Complex.I).im| := by rw [him, abs_of_pos hT]
        _ ≤ ‖(u : ℂ) + (T : ℝ) * Complex.I‖ := Complex.abs_im_le_norm _
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le u) hT hden
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hAσ) ?_
  have hmono : (∫ u in (-A)..σ, ‖((y : ℂ) ^ ((u : ℂ) + (T : ℝ) * Complex.I))
        / ((u : ℂ) + (T : ℝ) * Complex.I)‖)
      ≤ ∫ u in (-A)..σ, Real.exp (u * L) / T :=
    intervalIntegral.integral_mono_on hAσ hcont.norm.intervalIntegrable
      hmaj.continuousOn.intervalIntegrable hnorm
  refine le_trans hmono ?_
  have hval : (∫ u in (-A)..σ, Real.exp (u * L) / T)
      = (Real.exp (σ * L) - Real.exp (-A * L)) / (L * T) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_exp_mul_const L hL.ne' (-A) σ]
    field_simp
  rw [hval]
  have hpos : (0 : ℝ) < Real.exp (-A * L) := Real.exp_pos _
  have hden : (0 : ℝ) < L * T := by positivity
  rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < T * L)]
  have hyσ : y ^ σ = Real.exp (σ * L) := hrpow σ
  rw [hyσ]
  nlinarith [hpos, Real.exp_pos (σ * L), hden, hL, hT]

end GaloisForLFunctions.HTGeometry
end
