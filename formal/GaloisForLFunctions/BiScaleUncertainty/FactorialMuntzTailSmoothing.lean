import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzZeroReadout

/-! Uniform exponential and polar budgets for the literal smoothed correction
tail. Both polar branches are retained, including the negative endpoint. -/

open MeasureTheory Set Filter Complex
open scoped Topology Convolution ComplexConjugate
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.CHMDDoobGraph
open _root_.Zeta23
noncomputable section
set_option autoImplicit false

theorem factorialMuntzCorrectedTail_integrable (n : ℕ) :
    Integrable (factorialMuntzCorrectedTail n) := by
  have h := (factorialMuntzCorrectedTail_readout_integrable n (1/2 : ℂ) (by norm_num)).re
  change Integrable (fun x : ℝ =>
    (Complex.exp (((1/2 : ℂ)-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)).re) at h
  simpa only [sub_self, zero_mul, Complex.exp_zero, one_mul, Complex.ofReal_re] using h

/-- The one-sided tail gives a global rate `3/2`, not merely rate one. -/
theorem factorialMuntzCorrectedTail_exp_bound (n : ℕ) (x : ℝ) :
    |factorialMuntzCorrectedTail n x| ≤
      (12/Real.sqrt ((n+1 : ℕ) : ℝ))*Real.exp (-((3/2 : ℝ)*|x|)) := by
  have hb := factorialMuntzCorrectedTail_abs_le n x
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)] at hb
    calc
      _ ≤ 12*Real.exp (3*x/2)/Real.sqrt ((n+1 : ℕ) : ℝ) := hb
      _ = _ := by
        rw [abs_of_nonpos hx, show -((3/2 : ℝ)*(-x)) = 3*x/2 by ring]
        ring
  · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx)] at hb
    exact hb.trans (by positivity)

def factorialMuntzSmoothedTail (n k : ℕ) : ℝ → ℝ :=
  CHMDDoobGraph.mollifier k ⋆[ContinuousLinearMap.mul ℝ ℝ] factorialMuntzCorrectedTail n

private theorem kernel_support_abs_le_one (k : ℕ) {x : ℝ}
    (hx : CHMDDoobGraph.mollifier k x ≠ 0) : |x| ≤ 1 := by
  have hm : x ∈ Function.support ((WeilOneSided.narrowBump k).normed volume) := hx
  rw [(WeilOneSided.narrowBump k).support_normed_eq] at hm
  have hr : (WeilOneSided.narrowBump k).rOut ≤ 1 := by
    change 1/(4*((k : ℝ)+1)) ≤ 1
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hxout : |x| < (WeilOneSided.narrowBump k).rOut := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hm
  exact hxout.le.trans hr

/-- Smoothing preserves the faster tail decay with a constant independent of
the smoothing index. No derivative estimate enters this value bound. -/
theorem factorialMuntzSmoothedTail_exp_bound (n k : ℕ) (x : ℝ) :
    |factorialMuntzSmoothedTail n k x| ≤
      (12*Real.exp (3/2)/Real.sqrt ((n+1 : ℕ) : ℝ))*
        Real.exp (-((3/2 : ℝ)*|x|)) := by
  set C := 12/Real.sqrt ((n+1 : ℕ) : ℝ)
  have hC : 0 ≤ C := by positivity
  have hm := (mollifier_integrable k).mul_const
    (C*Real.exp (3/2)*Real.exp (-((3/2 : ℝ)*|x|)))
  have hb : ∀ᵐ y : ℝ, ‖CHMDDoobGraph.mollifier k y*factorialMuntzCorrectedTail n (x-y)‖ ≤
      CHMDDoobGraph.mollifier k y*(C*Real.exp (3/2)*Real.exp (-((3/2 : ℝ)*|x|))) := by
    filter_upwards [] with y
    by_cases hy : CHMDDoobGraph.mollifier k y = 0
    · simp only [hy, zero_mul, norm_zero, le_refl]
    have hy1 := kernel_support_abs_le_one k hy
    have ht : |x| ≤ |x-y|+|y| := by
      simpa only [sub_add_cancel] using (_root_.abs_add_le (x-y) y)
    have he : Real.exp (-((3/2 : ℝ)*|x-y|)) ≤
        Real.exp (3/2)*Real.exp (-((3/2 : ℝ)*|x|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mollifier_nonneg k y)]
    apply mul_le_mul_of_nonneg_left _ (mollifier_nonneg k y)
    calc
      _ ≤ C*Real.exp (-((3/2 : ℝ)*|x-y|)) := factorialMuntzCorrectedTail_exp_bound n _
      _ ≤ C*(Real.exp (3/2)*Real.exp (-((3/2 : ℝ)*|x|))) :=
        mul_le_mul_of_nonneg_left he hC
      _ = _ := by ring
  have h := norm_integral_le_of_norm_le hm hb
  simp only [integral_mul_const, mollifier_integral, one_mul] at h
  simpa only [factorialMuntzSmoothedTail, convolution_def, ContinuousLinearMap.mul_apply',
    Real.norm_eq_abs, C, div_mul_eq_mul_div] using h

theorem factorialMuntzSmoothedTail_expDecayTest (n k : ℕ) :
    ExpDecayTest (factorialMuntzSmoothedTail n k) := by
  have hb (x : ℝ) : |factorialMuntzCorrectedTail n x| ≤
      (12/Real.sqrt ((n+1 : ℕ) : ℝ))*Real.exp (-|x|) := by
    apply (factorialMuntzCorrectedTail_exp_bound n x).trans
    gcongr
    nlinarith [abs_nonneg x]
  obtain ⟨hc, D, hD, hd⟩ := compactConvolution_contDiff_exp_bounds
    (factorialMuntzCorrectedTail_integrable n) (by positivity) hb
      (mollifier_contDiff k) (mollifier_compact k)
  refine ⟨hc, 1/2, D, by norm_num, hD, fun x => ?_⟩
  simpa only [factorialMuntzSmoothedTail, show (1/2 : ℝ)+1/2 = 1 by norm_num, one_mul] using hd x

private theorem kernel_readout_integrable (k : ℕ) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*(CHMDDoobGraph.mollifier k x : ℂ)) := by
  have hk : Continuous (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))) := by fun_prop
  exact (hk.mul (Complex.continuous_ofReal.comp (mollifier_contDiff k).continuous)).integrable_of_hasCompactSupport
    ((mollifier_compact k).comp_left Complex.ofReal_zero).mul_left

theorem factorialMuntzSmoothedTail_readout (n k : ℕ) (s : ℂ) (hs : -1 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzSmoothedTail n k x : ℂ)) ∧
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzSmoothedTail n k x : ℂ)) =
      factorialMuntzKernelReadout k s*
        ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ) :=
  integral_exponential_tilt_convolution (s-1/2) (kernel_readout_integrable k s)
    (factorialMuntzCorrectedTail_readout_integrable n s hs)

/-- Uniform control includes both endpoints `s=0,1`. -/
theorem factorialMuntzSmoothedTail_paperFT_bound (n k : ℕ) {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf s)‖ ≤
      Real.exp 1*(12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(s.re+1))) := by
  have he : paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (gammaOf s) =
      ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzSmoothedTail n k x : ℂ) := by
    simp only [paperFT, gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero, mul_comm]
  rw [he, (factorialMuntzSmoothedTail_readout n k s (by linarith)).2, norm_mul]
  exact mul_le_mul (factorialMuntzKernelReadout_bound k hs0 hs1)
    (factorialMuntzCorrectedTail_readout_norm_le n s (by linarith))
      (norm_nonneg _) (Real.exp_pos 1).le

def factorialMuntzTailPolarTerm (n k : ℕ) : ℝ :=
  2*(paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (Complex.I/2)*
    conj (paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (-Complex.I/2))).re

theorem factorialMuntzTailPolarTerm_bound (n k : ℕ) :
    |factorialMuntzTailPolarTerm n k| ≤ 144*Real.exp 1^2/((n+1 : ℕ) : ℝ) := by
  have h0 := factorialMuntzSmoothedTail_paperFT_bound n k (s := 0) (by norm_num) (by norm_num)
  have h1 := factorialMuntzSmoothedTail_paperFT_bound n k (s := 1) (by norm_num) (by norm_num)
  norm_num [gammaOf, Complex.div_I] at h0 h1
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)
  unfold factorialMuntzTailPolarTerm
  calc
    _ ≤ 2*(‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (Complex.I/2)‖*
        ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (-Complex.I/2)‖) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [norm_mul, norm_conj] using Complex.abs_re_le_norm
        (paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (Complex.I/2)*
          conj (paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) (-Complex.I/2)))
    _ ≤ 2*((Real.exp 1*(12/Real.sqrt ((n+1 : ℕ) : ℝ)))*
        (Real.exp 1*(12/(Real.sqrt ((n+1 : ℕ) : ℝ)*2)))) := by
      gcongr
      · simpa [div_eq_mul_inv, mul_comm] using h0
      · simpa [div_eq_mul_inv, mul_comm] using h1
    _ = _ := by
      field_simp
      nlinarith [hsq]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
