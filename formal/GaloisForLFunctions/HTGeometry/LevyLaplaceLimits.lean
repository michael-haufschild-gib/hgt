import GaloisForLFunctions.HTGeometry.LevyLaplaceExponent
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Intrinsic endpoint limits: finite control jump activity has no killing or linear drift part. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem tendsto_levyLaplaceKernel_ofReal_zero (h : ℝ≥0) :
    Tendsto (fun x : ℝ => levyLaplaceKernel (x : ℂ) h) (𝓝 0) (𝓝 0) := by
  simpa only [Function.comp_apply, Complex.ofReal_zero, levyLaplaceKernel_at_zero] using!
    (hasDerivAt_levyLaplaceKernel (0 : ℂ) h).continuousAt.tendsto.comp
      (Complex.continuous_ofReal.tendsto 0)

theorem tendsto_levyLaplaceKernel_div_atTop (h : ℝ≥0) :
    Tendsto (fun x : ℝ => levyLaplaceKernel (x : ℂ) h / (x : ℂ)) atTop (𝓝 0) := by
  by_cases hh : h = 0
  · simpa only [hh, levyLaplaceKernel_zero, zero_div] using
      (tendsto_const_nhds (x := (0 : ℂ)))
  · have hp : 0 < (h : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hh)
    have he : Tendsto (fun x : ℝ => Real.exp (-(x * (h : ℝ)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.Tendsto.atTop_mul_const hp tendsto_id)
    have hr := ((tendsto_const_nhds (x := (1 + (h : ℝ)) / (h : ℝ))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub he)).mul
        (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa only [levyLaplaceKernel_ofReal, Function.comp_def, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.ofReal_inv, sub_zero, mul_one, mul_zero,
      Complex.ofReal_zero] using! hc

variable (η : Measure ℝ≥0) [IsFiniteMeasure η]

theorem tendsto_levyLaplaceJump_zero :
    Tendsto (fun x : ℝ => levyLaplaceJump η (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hB : ∀ᶠ x : ℝ in 𝓝[>] 0, ∀ᵐ h ∂η, ‖levyLaplaceKernel (x : ℂ) h‖ ≤ 3 := by
    have hx1 : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hx1] with x hx hx1
    refine Eventually.of_forall fun h => ?_
    have hn := norm_levyLaplaceKernel_le (z := (x : ℂ)) hx.le h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.le] at hn
    have hx1' : x < 1 := hx1
    exact hn.trans (by linarith)
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := η)
    (F := fun x : ℝ => levyLaplaceKernel (x : ℂ)) (f := fun _ => (0 : ℂ))
    (l := 𝓝[>] (0 : ℝ)) (fun _ => (3 : ℝ))
    (Eventually.of_forall fun x => (measurable_levyLaplaceKernel (x : ℂ)).aestronglyMeasurable)
    hB (integrable_const _)
    (Eventually.of_forall fun h => (tendsto_levyLaplaceKernel_ofReal_zero h).mono_left nhdsWithin_le_nhds)
  simpa only [levyLaplaceJump, integral_zero] using hd

theorem tendsto_levyLaplaceJump_div_atTop :
    Tendsto (fun x : ℝ => levyLaplaceJump η (x : ℂ) / (x : ℂ)) atTop (𝓝 0) := by
  have hB : ∀ᶠ x : ℝ in atTop, ∀ᵐ h ∂η, ‖levyLaplaceKernel (x : ℂ) h / (x : ℂ)‖ ≤ 3 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
    refine Eventually.of_forall fun h => ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxp.le]
    apply (div_le_iff₀ hxp).mpr
    have hn := norm_levyLaplaceKernel_le (z := (x : ℂ)) hxp.le h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxp.le] at hn
    linarith
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := η)
    (F := fun x : ℝ => fun h => levyLaplaceKernel (x : ℂ) h / (x : ℂ))
    (f := fun _ => (0 : ℂ)) (l := atTop) (fun _ => (3 : ℝ))
    (Eventually.of_forall fun x =>
      ((measurable_levyLaplaceKernel (x : ℂ)).div measurable_const).aestronglyMeasurable)
    hB (integrable_const _) (Eventually.of_forall tendsto_levyLaplaceKernel_div_atTop)
  simpa only [integral_div, integral_zero, levyLaplaceJump] using hd

end GaloisForLFunctions.HTGeometry
