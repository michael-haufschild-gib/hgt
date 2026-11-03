import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicMellinAnalytic
import GaloisForLFunctions.RHTower.CriticalContinuousChebyshevDivisorLaplaceWeld
import GaloisForLFunctions.RHTower.Suzuki.SuzukiMellinConvolution

/-!
# The Mellin transform of the first Chebyshev mode

The continuous first-mode packet is a multiplicative convolution. Its Mellin
transform factors into the literal Chebyshev divisor current and the first
cyclotomic multiplier. A power bound gives holomorphy on its growth half-plane.
-/

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology Asymptotics intervalIntegral

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Square-root-normalized Chebyshev error, supported beyond one. -/
def firstCyclotomicChebyshevInput : ℝ → ℂ :=
  (Ioi 1).indicator fun t =>
    (_root_.RHTower.criticalMellinError (fun n => ArithmeticFunction.vonMangoldt n) t : ℂ) *
      (t : ℂ) ^ (-(1 / 2 : ℂ))

/-- Compact head of the first difference kernel. -/
def firstCyclotomicKernelHead : ℝ → ℂ := (Ioc 0 1).indicator firstCyclotomicKernel

/-- Inversion turns the compact kernel head into a causal multiplicative kernel. -/
def firstCyclotomicInverseKernel (t : ℝ) : ℂ := firstCyclotomicKernelHead t⁻¹

/-- Continuous first-mode Chebyshev packet. -/
def chebyshevFirstCyclotomicContinuous : ℝ → ℂ :=
  _root_.RHTower.positiveMellinConvolution firstCyclotomicChebyshevInput firstCyclotomicInverseKernel

private theorem firstCyclotomicChebyshevInput_integrand (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (-s - 1) * firstCyclotomicChebyshevInput t) =
      (Ioi 1).indicator (fun t : ℝ =>
        (_root_.RHTower.criticalMellinError (fun n => ArithmeticFunction.vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-((s + 1 / 2) + 1))) := by
  funext t
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · have ht0 : 0 < t := lt_trans zero_lt_one ht
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [firstCyclotomicChebyshevInput, indicator_of_mem ht, indicator_of_mem ht]
    calc
      _ = (_root_.RHTower.criticalMellinError (fun n => ArithmeticFunction.vonMangoldt n) t : ℂ) *
          ((t : ℂ) ^ (-s - 1) * (t : ℂ) ^ (-(1 / 2 : ℂ))) := by ring
      _ = _ := by rw [← Complex.cpow_add _ _ htne]; congr 2; ring
  · simp only [firstCyclotomicChebyshevInput, indicator_of_notMem ht, mul_zero]

/-- The Mellin transform of the literal arithmetic input is the Chebyshev divisor current. -/
theorem hasMellin_firstCyclotomicChebyshevInput {s : ℂ} (hs : 1 / 2 < s.re) :
    HasMellin firstCyclotomicChebyshevInput (-s)
      (_root_.RHTower.criticalContinuousChebyshevErrorMellinRay (s + 1 / 2)) := by
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hshift : 1 < (s + 1 / 2).re := by rw [add_re, hhalf]; linarith only [hs]
  have hset : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 := Ioi_inter_Ioi.trans (by norm_num)
  constructor
  · rw [MellinConvergent]
    simp only [smul_eq_mul]
    rw [firstCyclotomicChebyshevInput_integrand, integrableOn_indicator_iff measurableSet_Ioi, hset]
    exact _root_.RHTower.integrableOn_criticalContinuousChebyshevErrorMellinRay hshift
  · rw [mellin]
    simp only [smul_eq_mul]
    rw [firstCyclotomicChebyshevInput_integrand, setIntegral_indicator measurableSet_Ioi]
    have hset' : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := Ioi_inter_Ioi.trans (by norm_num)
    rw [hset']
    rfl

private theorem firstCyclotomicKernelHead_integrand (s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (s - 1) * firstCyclotomicKernelHead t) =
      (Ioc 0 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) * firstCyclotomicKernel t) := by
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [firstCyclotomicKernelHead, indicator_of_mem ht]
  · simp only [firstCyclotomicKernelHead, indicator_of_notMem ht, mul_zero]

/-- The compact kernel head has precisely the first cyclotomic Mellin multiplier. -/
theorem hasMellin_firstCyclotomicKernelHead {s : ℂ} (hs : 0 < s.re) :
    HasMellin firstCyclotomicKernelHead s (firstCyclotomicMellin s) := by
  have hi : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * firstCyclotomicKernel t)
      volume 0 1 :=
    (intervalIntegrable_cpow' (a := 0) (b := 1) (r := s - 1)
      (by simp only [sub_re, one_re]; linarith)).mul_continuousOn
        continuous_firstCyclotomicKernel.continuousOn
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ h => h.1
  constructor
  · rw [MellinConvergent]
    simp only [smul_eq_mul]
    rw [firstCyclotomicKernelHead_integrand, integrableOn_indicator_iff measurableSet_Ioc,
      inter_eq_self_of_subset_left hsub]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  · rw [mellin]
    simp only [smul_eq_mul]
    rw [firstCyclotomicKernelHead_integrand, setIntegral_indicator measurableSet_Ioc,
      inter_eq_self_of_subset_right hsub, firstCyclotomicMellin,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rfl

/-- Mellin inversion of the horizon variable changes the sign of the exponent. -/
theorem hasMellin_firstCyclotomicInverseKernel {s : ℂ} (hs : 0 < s.re) :
    HasMellin firstCyclotomicInverseKernel (-s) (firstCyclotomicMellin s) := by
  have hh := hasMellin_firstCyclotomicKernelHead hs
  constructor
  · have h := (MellinConvergent.comp_rpow (f := firstCyclotomicKernelHead)
      (s := -s) (a := -1) (by norm_num)).mpr (by simpa using hh.1)
    change MellinConvergent (fun t => firstCyclotomicKernelHead t⁻¹) (-s)
    simpa only [Real.rpow_neg_one] using h
  · have h := mellin_comp_rpow firstCyclotomicKernelHead (-s) (-1)
    have harg : -s / (-1 : ℂ) = s := by ring
    simpa only [Real.rpow_neg_one, firstCyclotomicInverseKernel,
      abs_neg, abs_one, inv_one, one_smul, ofReal_neg, ofReal_one,
      harg, hh.2] using! h

#print axioms hasMellin_firstCyclotomicChebyshevInput
#print axioms hasMellin_firstCyclotomicKernelHead
#print axioms hasMellin_firstCyclotomicInverseKernel


private theorem measurable_firstCyclotomicChebyshevInput : Measurable firstCyclotomicChebyshevInput := by
  have hE : Measurable (fun t : ℝ =>
      _root_.RHTower.criticalMellinError (fun n => ArithmeticFunction.vonMangoldt n) t) :=
    _root_.RHTower.measurable_criticalCumulative_vonMangoldt.sub measurable_id
  exact ((Complex.measurable_ofReal.comp hE).mul (by fun_prop)).indicator measurableSet_Ioi

private theorem measurable_firstCyclotomicInverseKernel : Measurable firstCyclotomicInverseKernel :=
  (continuous_firstCyclotomicKernel.measurable.indicator measurableSet_Ioc).comp measurable_inv

/-- Absolute Mellin factorization of the actual continuous first-mode packet. -/
theorem hasMellin_chebyshevFirstCyclotomicContinuous {s : ℂ} (hs : 1 / 2 < s.re) :
    HasMellin chebyshevFirstCyclotomicContinuous (-s)
      (_root_.RHTower.criticalContinuousChebyshevErrorMellinRay (s + 1 / 2) *
        firstCyclotomicMellin s) := by
  have hf := hasMellin_firstCyclotomicChebyshevInput hs
  have hg := hasMellin_firstCyclotomicInverseKernel (by linarith only [hs])
  have h := _root_.RHTower.hasMellin_positiveMellinConvolution
    measurable_firstCyclotomicChebyshevInput measurable_firstCyclotomicInverseKernel hf.1 hg.1
  simpa only [chebyshevFirstCyclotomicContinuous, hf.2, hg.2] using h

/-- The first-mode transform retains the literal zeta logarithmic derivative. -/
theorem mellin_chebyshevFirstCyclotomicContinuous_eq_logDeriv {s : ℂ} (hs : 1 / 2 < s.re) :
    mellin chebyshevFirstCyclotomicContinuous (-s) =
      (-(logDeriv _root_.RHTower.zetaResidueUnit (s + 1 / 2) + 1) /
        (s + 1 / 2)) * firstCyclotomicMellin s := by
  rw [(hasMellin_chebyshevFirstCyclotomicContinuous hs).2,
    _root_.RHTower.criticalContinuousChebyshevErrorMellinRay_eq_logDeriv]
  have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rw [add_re, hhalf]
  linarith only [hs]

#print axioms hasMellin_chebyshevFirstCyclotomicContinuous
#print axioms mellin_chebyshevFirstCyclotomicContinuous_eq_logDeriv


/-- The multiplicative convolution is the literal weighted Chebyshev-error integral. -/
theorem chebyshevFirstCyclotomicContinuous_eq_integral {x : ℝ} (hx : 1 ≤ x) :
    chebyshevFirstCyclotomicContinuous x =
      ∫ t in (1 : ℝ)..x,
        (_root_.RHTower.criticalMellinError (fun n => ArithmeticFunction.vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-3 / 2 : ℂ) * firstCyclotomicKernel (t / x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [chebyshevFirstCyclotomicContinuous, _root_.RHTower.positiveMellinConvolution,
    intervalIntegral.integral_of_le hx]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun t (ht : t ∈ Ioc 1 x) => lt_trans zero_lt_one ht.1)]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hmem : t / x ∈ Ioc (0 : ℝ) 1 := ⟨div_pos ht0 hx0, (div_le_one hx0).mpr ht.2⟩
    dsimp only
    rw [firstCyclotomicChebyshevInput, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht.1),
      firstCyclotomicInverseKernel, inv_div, firstCyclotomicKernelHead, indicator_of_mem hmem]
    have hp : (t : ℂ) ^ (-(1 / 2 : ℂ)) / t = (t : ℂ) ^ (-3 / 2 : ℂ) := by
      rw [show (-3 / 2 : ℂ) = -(1 / 2) - 1 by ring,
        Complex.cpow_sub _ _ htne, Complex.cpow_one]
    calc
      _ = (_root_.RHTower.criticalMellinError (fun n => ArithmeticFunction.vonMangoldt n) t : ℂ) *
          ((t : ℂ) ^ (-(1 / 2 : ℂ)) / t) * firstCyclotomicKernel (t / x) := by ring
      _ = _ := by rw [hp]
  · intro t ht
    by_cases ht1 : 1 < t
    · have hxt : x < t := by
        have hnot := ht.2
        simp only [mem_Ioc, not_and, not_le] at hnot
        exact hnot ht1
      have hnot : t / x ∉ Ioc (0 : ℝ) 1 := by
        intro hh
        exact (not_le.mpr ((one_lt_div hx0).mpr hxt)) hh.2
      rw [firstCyclotomicInverseKernel, inv_div, firstCyclotomicKernelHead,
        indicator_of_notMem hnot, mul_zero, zero_div]
    · rw [firstCyclotomicChebyshevInput,
        indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from ht1), zero_mul, zero_div]

/-- The continuous packet vanishes below its arithmetic support. -/
theorem chebyshevFirstCyclotomicContinuous_zero {x : ℝ} (hx : x ≤ 1) :
    chebyshevFirstCyclotomicContinuous x = 0 := by
  rw [chebyshevFirstCyclotomicContinuous, _root_.RHTower.positiveMellinConvolution]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  by_cases ht1 : 1 < t
  · have hnot : t / x ∉ Ioc (0 : ℝ) 1 := by
      by_cases hx0 : 0 < x
      · intro hh
        exact (not_le.mpr ((one_lt_div hx0).mpr (lt_of_le_of_lt hx ht1))) hh.2
      · have hdiv : t / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (le_of_not_gt hx0)
        exact fun hh => (not_lt.mpr hdiv) hh.1
    rw [firstCyclotomicInverseKernel, inv_div, firstCyclotomicKernelHead,
      indicator_of_notMem hnot, mul_zero, zero_div]
  · rw [firstCyclotomicChebyshevInput,
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from ht1), zero_mul, zero_div]

#print axioms chebyshevFirstCyclotomicContinuous_eq_integral
#print axioms chebyshevFirstCyclotomicContinuous_zero


/-- Absolute convergence at one point gives local integrability of the actual packet. -/
theorem locallyIntegrableOn_chebyshevFirstCyclotomicContinuous :
    LocallyIntegrableOn chebyshevFirstCyclotomicContinuous (Ioi 0) volume := by
  have hi := (hasMellin_chebyshevFirstCyclotomicContinuous (s := 1) (by norm_num)).1
  have hloc : LocallyIntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((-1 : ℂ) - 1) * chebyshevFirstCyclotomicContinuous t)
      (Ioi 0) volume := hi.locallyIntegrableOn
  have hmul := hloc.mul_continuousOn
    (Complex.continuous_ofReal_cpow_const (show 0 < ((1 : ℂ) + 1).re by norm_num)).continuousOn
    isOpen_Ioi.isLocallyClosed
  apply hmul.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  calc
    _ = chebyshevFirstCyclotomicContinuous t *
        ((t : ℂ) ^ ((-1 : ℂ) - 1) * (t : ℂ) ^ ((1 : ℂ) + 1)) := by ring
    _ = chebyshevFirstCyclotomicContinuous t := by
      rw [← Complex.cpow_add _ _ htne]
      norm_num

/-- A power bound continues the actual first-mode transform to its growth half-plane. -/
theorem differentiableAt_mellin_chebyshevFirstCyclotomicContinuous
    {b : ℝ} (hbound : chebyshevFirstCyclotomicContinuous =O[Filter.atTop] fun x : ℝ => x ^ b)
    {s : ℂ} (hs : b < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => mellin chebyshevFirstCyclotomicContinuous (-z)) s := by
  have hbot : chebyshevFirstCyclotomicContinuous =O[nhdsWithin (0 : ℝ) (Ioi 0)]
      fun x : ℝ => x ^ (-(-s.re - 1)) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    rw [chebyshevFirstCyclotomicContinuous_zero hx.2.le, norm_zero, zero_mul]
  have h := mellin_differentiableAt_of_isBigO_rpow (a := -b) (b := -s.re - 1) (s := -s)
    locallyIntegrableOn_chebyshevFirstCyclotomicContinuous
    (by simpa only [neg_neg] using hbound)
    (by simp only [Complex.neg_re]; linarith only [hs]) hbot
    (by simp only [Complex.neg_re]; linarith)
  exact h.comp s differentiableAt_id.neg

#print axioms locallyIntegrableOn_chebyshevFirstCyclotomicContinuous
#print axioms differentiableAt_mellin_chebyshevFirstCyclotomicContinuous

end GaloisForLFunctions.CompletedArithmeticForms
