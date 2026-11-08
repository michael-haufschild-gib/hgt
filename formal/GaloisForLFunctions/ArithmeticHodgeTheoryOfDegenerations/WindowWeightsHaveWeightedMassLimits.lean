import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsCoercive
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsPositive

/-!
# Weighted masses of logarithmic window vectors

Exponential reweighting converts weighted coefficient masses into ordinary
window Riemann sums. The receiving test pairing has the half-weighted limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- Exponential weighting of a window gives the corresponding inverse-power coefficient mass. -/
theorem tendsto_weighted_sum_horizonWeights_sq {h : ℝ → ℝ} {A : ℝ}
    (hh : Continuous h) (hsupp : ∀ u, u ∉ Set.Icc (-A) 0 → h u = 0)
    (hA : 0 ≤ A) (p : ℕ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      ((N : ℝ) / n) ^ p * horizonWeights h N n ^ 2) atTop
      (𝓝 (∫ u, Real.exp (-((p : ℝ) * u)) * h u ^ 2)) := by
  let g : ℝ → ℝ := fun u => Real.exp (-((p : ℝ) * u) / 2) * h u
  have hg : Continuous g :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg.div_const 2)).mul hh
  have hgs : ∀ u, u ∉ Set.Icc (-A) 0 → g u = 0 := by
    intro u hu
    dsimp only [g]
    rw [hsupp u hu, mul_zero]
  have hg2 (u : ℝ) : g u ^ 2 = Real.exp (-((p : ℝ) * u)) * h u ^ 2 := by
    dsimp only [g]
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  have hlim := tendsto_sum_horizonWeights_sq hg hgs hA
  simp only [hg2] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold horizonWeights
  rw [div_pow, hg2]
  have hexp : Real.exp (-((p : ℝ) * (Real.log n - Real.log N))) = ((N : ℝ) / n) ^ p := by
    rw [show -((p : ℝ) * (Real.log n - Real.log N)) =
        (p : ℝ) * (Real.log N - Real.log n) by ring,
      Real.exp_nat_mul, Real.exp_sub, Real.exp_log hN0, Real.exp_log hn0]
  rw [hexp, div_pow]
  ring

/-- A compact logarithmic Riemann sum has the natural `1/n` density. -/
theorem tendsto_sum_log_window_div {g : ℝ → ℝ} {A : ℝ} (hg : Continuous g)
    (hsupp : ∀ u, u ∉ Set.Icc (-A) 0 → g u = 0) (hA : 0 ≤ A) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      g (Real.log n - Real.log N) / n) atTop (𝓝 (∫ u, g u)) := by
  have hlim := tendsto_riemannSum_Icc_complex (continuous_horizonProfile hg hsupp 0)
    (fun x hx => horizonProfile_eq_zero_of_notMem hsupp 0 hx)
  rw [integral_horizonProfile hg hsupp hA 0] at hlim
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hlim
  have htransform : (horizonTransform g 0).re = ∫ u, g u := by
    unfold horizonTransform
    simp only [zero_mul, Complex.exp_zero, mul_one]
    rw [integral_complex_ofReal]
    rfl
  rw [htransform] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [mul_sum, Complex.re_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [horizonProfile_zero _ (div_pos hn0 hN0), Real.log_div hn0.ne' hN0.ne',
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

/-- Sampling a continuous test against a horizon vector converges to its half-weighted pairing. -/
theorem tendsto_horizonWeights_sample_pairing {h f : ℝ → ℝ} {A : ℝ}
    (hh : Continuous h) (hf : Continuous f) (hA : 0 ≤ A)
    (hsupp : ∀ u, u ∉ Set.Icc (-A) 0 → h u = 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,
      horizonWeights h N n * f (Real.log n - Real.log N)) / Real.sqrt N)
      atTop (𝓝 (∫ u, halfWeight h u * f u)) := by
  let g : ℝ → ℝ := fun u => halfWeight h u * f u
  have hg : Continuous g := ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hh).mul hf
  have hgs : ∀ u, u ∉ Set.Icc (-A) 0 → g u = 0 := by
    intro u hu
    dsimp only [g, halfWeight]
    rw [hsupp u hu, mul_zero, zero_mul]
  refine (tendsto_sum_log_window_div hg hgs hA).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_div]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hhalf {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hsqrt : Real.exp ((Real.log n - Real.log N) / 2) = Real.sqrt n / Real.sqrt N := by
    rw [sub_div, Real.exp_sub, hhalf hn0, hhalf hN0]
  dsimp only [g, halfWeight, horizonWeights]
  rw [hsqrt]
  field_simp
  rw [Real.sq_sqrt hn0.le]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
