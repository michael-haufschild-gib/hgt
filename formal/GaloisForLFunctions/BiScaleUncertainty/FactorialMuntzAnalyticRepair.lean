import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzUniformTail
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-! Actual Mellin regularisation, analytic across the negative pole, and uniform
half-plane approximation by the compact ramp. No full-Weil limit is assumed. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.RHTower
noncomputable section
set_option autoImplicit false

def factorialMuntzRegularizedSum (n : ℕ) (t : ℝ) : ℝ :=
  factorialMuntzSum n t+(Ioc (0 : ℝ) 1).indicator (fun _ => (1/2 : ℝ)) t

theorem factorialMuntzRegularizedSum_measurable (n : ℕ) :
    Measurable (factorialMuntzRegularizedSum n) :=
  (factorialMuntzSum_measurable n).add (measurable_const.indicator measurableSet_Ioc)

theorem factorialMuntzRegularizedSum_abs_le (n : ℕ) (t : ℝ) :
    |factorialMuntzRegularizedSum n t| ≤ 21/2 := by
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [factorialMuntzRegularizedSum, indicator_of_mem ht]
    have h := _root_.abs_add_le (factorialMuntzSum n t) (1/2 : ℝ)
    norm_num at h
    linarith only [h, factorialMuntzSum_abs_le n t]
  · simp only [factorialMuntzRegularizedSum, indicator_of_notMem ht, add_zero]
    linarith only [factorialMuntzSum_abs_le n t]

theorem factorialMuntzRegularizedSum_small_bound (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : |factorialMuntzRegularizedSum n t| ≤ 12*t := by
  rw [factorialMuntzRegularizedSum, indicator_of_mem ht]
  exact factorialMuntzSum_boundary_error_uniform n ht.1

theorem factorialMuntzRegularizedSum_support (n : ℕ) {t : ℝ}
    (ht : max (factorialMuntzSupport n) 1 < t) : factorialMuntzRegularizedSum n t = 0 := by
  have hL : factorialMuntzSupport n < t := lt_of_le_of_lt (le_max_left _ _) ht
  have h1 : 1 < t := lt_of_le_of_lt (le_max_right _ _) ht
  have hz : factorialMuntzSum n t = 0 :=
    arithmeticSum_eq_zero_of_lt (factorialMuntzSeed_support n) hL
  simp only [factorialMuntzRegularizedSum, hz,
    indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => not_le.mpr h1 h.2), zero_add]

private theorem regularizedSum_isBigO_zero (n : ℕ) :
    (fun t : ℝ => (factorialMuntzRegularizedSum n t : ℂ)) =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t^(-(-1 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound 12 ?_
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht h1
  have htpos : 0 < t := ht
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos htpos] using
    factorialMuntzRegularizedSum_small_bound n ⟨ht, h1.le⟩

/-- The actual regularised Mellin transform is holomorphic on `Re s > -1`. -/
theorem factorialMuntzRegularizedSum_mellin_differentiableAt (n : ℕ) {s : ℂ}
    (hs : -1 < s.re) :
    DifferentiableAt ℂ (mellin (fun t => (factorialMuntzRegularizedSum n t : ℂ))) s := by
  exact mellin_differentiableAt_of_isBigO_rpow
    ((locallyIntegrable_ofReal_of_bound (factorialMuntzRegularizedSum_measurable n)
      (factorialMuntzRegularizedSum_abs_le n)).locallyIntegrableOn _)
    (isBigO_atTop_of_support (fun _ ht => factorialMuntzRegularizedSum_support n ht) (s.re+1))
    (by linarith) (regularizedSum_isBigO_zero n) hs

private theorem corrected_eq_regularized (n : ℕ) (x : ℝ) :
    factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x =
      Real.exp (x/2)*factorialMuntzRegularizedSum n (Real.exp x)/
        Real.sqrt ((n+1 : ℕ) : ℝ) := by
  have he : Real.exp x ∈ Ioc (0 : ℝ) 1 ↔ x ≤ 0 := by
    simp only [mem_Ioc, Real.exp_pos, true_and, Real.exp_le_one_iff]
  by_cases hx : x ≤ 0
  · simp only [factorialMuntzBoundaryCorrected, factorialMuntzRegularizedSum,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx), indicator_of_mem (he.mpr hx), factorialMuntzCompletion,
      factorialMuntzBoundaryCoefficient]
    ring
  · simp only [factorialMuntzBoundaryCorrected, factorialMuntzRegularizedSum,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), indicator_of_notMem (mt he.mp hx), add_zero,
      factorialMuntzCompletion]

/-- Literal exponential substitution identifies the analytic function with the
convergent corrected readout, including at `s=0`. -/
theorem factorialMuntzBoundaryCorrected_readout_eq_regularized_mellin (n : ℕ) (s : ℂ) :
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
        (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) =
      mellin (fun t => (factorialMuntzRegularizedSum n t : ℂ)) s/
        (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ) := by
  rw [_root_.RHTower.mellin_eq_integral_exp_mul_log, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [corrected_eq_regularized]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [← mul_div_assoc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem factorialMuntzBoundaryCorrected_readout_differentiableAt (n : ℕ) {s : ℂ}
    (hs : -1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ x : ℝ, Complex.exp ((z-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) s := by
  simp_rw [factorialMuntzBoundaryCorrected_readout_eq_regularized_mellin]
  exact (factorialMuntzRegularizedSum_mellin_differentiableAt n hs).div_const _

/-- Holomorphy is proved for the source integral itself, not postulated as an
extension of a formal transform. -/
theorem factorialMuntzBoundaryCorrected_readout_analyticOnNhd (n : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ x : ℝ, Complex.exp ((z-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      {s : ℂ | -1 < s.re} := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => ∫ x : ℝ, Complex.exp ((z-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      {s : ℂ | -1 < s.re} := fun _ hs =>
    (factorialMuntzBoundaryCorrected_readout_differentiableAt n hs).differentiableWithinAt
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- Exact finite part of the original Mellin readout at its negative pole. -/
theorem factorialMuntzCompletion_readout_regularized_tendsto (n : ℕ) :
    Tendsto (fun s : ℂ =>
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ))+
        (factorialMuntzBoundaryCoefficient n : ℂ)/s)
      (𝓝[{s : ℂ | 0 < s.re}] 0)
      (𝓝 (∫ x : ℝ, Complex.exp ((-1/2 : ℂ)*(x : ℂ))*
        (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))) := by
  have hc := (factorialMuntzBoundaryCorrected_readout_differentiableAt n
    (s := 0) (by norm_num)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s : ℂ | 0 < s.re}) (a := 0))
  have he : ∀ᶠ s : ℂ in 𝓝[{s : ℂ | 0 < s.re}] 0,
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ))+
          (factorialMuntzBoundaryCoefficient n : ℂ)/s =
        ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
          (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [factorialMuntzCompletion_readout_eq_mellin,
      factorialMuntzBoundaryCorrected_readout_eq n _ s hs]
  simpa only [zero_sub, neg_div] using hc.congr' (Filter.EventuallyEq.symm he)

/-- The actual uncorrected readout has residue `-c_n` at zero. -/
theorem factorialMuntzCompletion_readout_residue (n : ℕ) :
    Tendsto (fun s : ℂ => s*
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ)))
      (𝓝[{s : ℂ | 0 < s.re}] 0) (𝓝 (-(factorialMuntzBoundaryCoefficient n : ℂ))) := by
  have hc := (factorialMuntzBoundaryCorrected_readout_differentiableAt n
    (s := 0) (by norm_num)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s : ℂ | 0 < s.re}) (a := 0))
  have h0 : Tendsto (fun s : ℂ => s) (𝓝[{s : ℂ | 0 < s.re}] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hm := (h0.mul hc).sub (tendsto_const_nhds
    (x := (factorialMuntzBoundaryCoefficient n : ℂ)))
  have he : ∀ᶠ s : ℂ in 𝓝[{s : ℂ | 0 < s.re}] 0,
      s*(∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
          (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))-
          (factorialMuntzBoundaryCoefficient n : ℂ) =
        s*(∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [factorialMuntzBoundaryCorrected_readout_eq n _ s hs,
      factorialMuntzCompletion_readout_eq_mellin]
    field_simp
    ring
  simpa only [zero_mul, zero_sub] using hm.congr' he

/-- Uniform convergence on entire closed half-planes, not only at individual
zeros or on finite frequency windows. -/
theorem factorialMuntzCorrectedTail_readout_tendstoUniformlyOn {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun s : ℂ => ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
        (factorialMuntzCorrectedTail n x : ℂ))
      (fun _ => 0) atTop {s : ℂ | -1+δ ≤ s.re} := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hb : Tendsto (fun n : ℕ => 12/(Real.sqrt ((n+1 : ℕ) : ℝ)*δ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm, mul_zero,
      zero_mul] using
      hi.const_mul (12/δ)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually (eventually_lt_nhds hε)] with n hn
  intro s hs
  have hbnd := factorialMuntzCorrectedTail_readout_norm_le n s
    (by change -1+δ ≤ s.re at hs; linarith)
  have hden : Real.sqrt ((n+1 : ℕ) : ℝ)*δ ≤ Real.sqrt ((n+1 : ℕ) : ℝ)*(s.re+1) :=
    mul_le_mul_of_nonneg_left (by change -1+δ ≤ s.re at hs; linarith) (Real.sqrt_nonneg _)
  have hcmp : 12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(s.re+1)) ≤
      12/(Real.sqrt ((n+1 : ℕ) : ℝ)*δ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  simpa only [dist_zero_left] using (hbnd.trans hcmp).trans_lt hn

theorem factorialMuntzBoundaryCorrected_readout_sub_ramp_tendstoUniformlyOn {δ : ℝ}
    (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun s : ℂ =>
        (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
          (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))-
        (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)))
      (fun _ => 0) atTop {s : ℂ | -1+δ ≤ s.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
    (factorialMuntzCorrectedTail_readout_tendstoUniformlyOn hδ)) ε hε] with n hn
  intro s hs
  rw [factorialMuntzBoundaryCorrected_readout_sub_ramp n s
    (by change -1+δ ≤ s.re at hs; linarith)]
  exact hn s hs

/-- Uniform bound for every right-half-plane zero, with no ordinate cutoff and
no inverse distance to `Re s=0`. -/
theorem factorialRamp_zeta_readout_uniform_bound (n : ℕ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    ‖∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)‖ ≤
      13/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
  have h4 : 4 ≤ ‖ρ‖ :=
    (_root_.RHTower.four_le_abs_im_of_zeta_zero hρ
      (_root_.RHTower.riemannZeta_zero_re_lt_one hz) hz).trans (Complex.abs_im_le_norm ρ)
  have hfirst : factorialMuntzBoundaryCoefficient n/‖ρ‖ ≤ factorialMuntzBoundaryCoefficient n := by
    apply (div_le_iff₀ (by linarith : 0 < ‖ρ‖)).2
    nlinarith [factorialMuntzBoundaryCoefficient_pos n]
  have hsecond : 12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(ρ.re+1)) ≤
      12/Real.sqrt ((n+1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hs (by nlinarith)
  calc
    _ ≤ factorialMuntzBoundaryCoefficient n/‖ρ‖+
        12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(ρ.re+1)) :=
      factorialRamp_zeta_readout_boundary_bound n hρ hz
    _ ≤ factorialMuntzBoundaryCoefficient n+12/Real.sqrt ((n+1 : ℕ) : ℝ) := by
      linarith only [hfirst, hsecond]
    _ = (25/2)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
      unfold factorialMuntzBoundaryCoefficient
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) hs.le

/-- All nontrivial zero readouts vanish uniformly for the literal compact
source. This alone does not justify exchanging an infinite Weil zero sum. -/
theorem factorialRamp_zeta_readout_tendstoUniformlyOn :
    TendstoUniformlyOn
      (fun n : ℕ => fun ρ : ℂ => ∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*
        (sourceFactorialRamp (n+1) x : ℂ))
      (fun _ => 0) atTop {ρ : ℂ | 0 < ρ.re ∧ riemannZeta ρ = 0} := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => 13/Real.sqrt ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)).const_mul (13 : ℝ)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually (eventually_lt_nhds hε)] with n hn
  intro ρ hρ
  simpa only [dist_zero_left] using
    (factorialRamp_zeta_readout_uniform_bound n hρ.1 hρ.2).trans_lt hn

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
