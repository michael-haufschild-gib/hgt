import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTail
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceFactorization
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelKernelInversion

/-! Exact tail reconstruction and quantitative bounds for the actual compact
factorial-ramp readout at every right-half-plane zeta zero. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

private def readoutKernel (s : ℂ) (x : ℝ) : ℂ := Complex.exp ((s-1/2)*(x : ℂ))

private theorem readoutKernel_norm (s : ℂ) (x : ℝ) :
    ‖readoutKernel s x‖ = Real.exp ((s.re-1/2)*x) := by
  rw [readoutKernel, Complex.norm_exp]
  congr 1
  simp

private theorem completion_readout_integrand (n : ℕ) (s : ℂ) (x : ℝ) :
    readoutKernel s x*(factorialMuntzCompletion n x : ℂ) =
      Complex.exp (s*(x : ℂ))*(factorialMuntzSum n (Real.exp x) : ℂ)/
        (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ) := by
  simp only [readoutKernel, factorialMuntzCompletion, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_exp]
  rw [← mul_div_assoc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem factorialMuntzCompletion_readout_eq_mellin (n : ℕ) (s : ℂ) :
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ)) =
      mellin (fun t => (factorialMuntzSum n t : ℂ)) s/
        (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ) := by
  change (∫ x : ℝ, readoutKernel s x*(factorialMuntzCompletion n x : ℂ)) = _
  simp_rw [completion_readout_integrand]
  rw [integral_div, _root_.RHTower.mellin_eq_integral_exp_mul_log]

private theorem readout_norm_le (n : ℕ) (s : ℂ) (x : ℝ) :
    ‖readoutKernel s x*(factorialMuntzCompletion n x : ℂ)‖ ≤
      10*Real.exp (s.re*x)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  rw [norm_mul, readoutKernel_norm, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ Real.exp ((s.re-1/2)*x)*(10*Real.exp (x/2)/Real.sqrt ((n+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorialMuntzCompletion_abs_le n x) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_div_assoc]
      have he : Real.exp ((s.re-1/2)*x)*Real.exp (x/2) = Real.exp (s.re*x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 10*(Real.exp ((s.re-1/2)*x)*Real.exp (x/2))/Real.sqrt ((n+1 : ℕ) : ℝ) := by ring
        _ = _ := by rw [he]

private theorem completion_readout_measurable (n : ℕ) (s : ℂ) :
    Measurable (fun x => readoutKernel s x*(factorialMuntzCompletion n x : ℂ)) := by
  have hk : Continuous (readoutKernel s) := by unfold readoutKernel; fun_prop
  exact hk.measurable.mul (Complex.continuous_ofReal.measurable.comp
    (factorialMuntzCompletion_measurable n))

theorem factorialMuntzCompletion_readout_integrable (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ)) := by
  let L := Real.log (factorialMuntzSupport n)
  have henv : Integrable ((Iic L).indicator
      (fun x : ℝ => 10*Real.exp (s.re*x)/Real.sqrt ((n+1 : ℕ) : ℝ))) :=
    IntegrableOn.integrable_indicator
      (((integrableOn_exp_mul_Iic hs L).const_mul 10).div_const _) measurableSet_Iic
  apply henv.mono' (completion_readout_measurable n s).aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ≤ L
  · rw [indicator_of_mem (show x ∈ Iic L from hx)]
    exact readout_norm_le n s x
  · have hLp : 0 < factorialMuntzSupport n := by
      unfold factorialMuntzSupport
      have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
      positivity
    have hxl : factorialMuntzSupport n < Real.exp x := by
      rw [← Real.exp_log hLp]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge hx)
    have hz : factorialMuntzSum n (Real.exp x) = 0 :=
      GaloisForLFunctions.RHTower.arithmeticSum_eq_zero_of_lt (factorialMuntzSeed_support n) hxl
    simp only [indicator_of_notMem (show x ∉ Iic L from hx), factorialMuntzCompletion,
      hz, mul_zero, zero_div, Complex.ofReal_zero, norm_zero, le_refl]

private def tailReadoutEnvelope (n : ℕ) (s : ℂ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (fun x => 10*Real.exp (s.re*x)/Real.sqrt ((n+1 : ℕ) : ℝ))

private theorem tailReadoutEnvelope_integrable (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (tailReadoutEnvelope n s) :=
  IntegrableOn.integrable_indicator
    (((integrableOn_exp_mul_Iic hs 0).const_mul 10).div_const _) measurableSet_Iic

private theorem tail_readout_norm_le (n : ℕ) (s : ℂ) (x : ℝ) :
    ‖readoutKernel s x*(factorialMuntzTail n x : ℂ)‖ ≤ tailReadoutEnvelope n s x := by
  by_cases hx : x ≤ 0
  · rw [factorialMuntzTail, tailReadoutEnvelope,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    exact readout_norm_le n s x
  · simp only [factorialMuntzTail, tailReadoutEnvelope,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), Complex.ofReal_zero,
      mul_zero, norm_zero, le_refl]

theorem factorialMuntzTail_readout_integrable (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzTail n x : ℂ)) := by
  have hk : Continuous (readoutKernel s) := by unfold readoutKernel; fun_prop
  apply (tailReadoutEnvelope_integrable n s hs).mono'
    (hk.measurable.mul (Complex.continuous_ofReal.measurable.comp
      (factorialMuntzTail_measurable n))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (tail_readout_norm_le n s)

theorem factorialMuntzTail_readout_norm_le (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzTail n x : ℂ)‖ ≤
      10/(Real.sqrt ((n+1 : ℕ) : ℝ)*s.re) := by
  calc
    _ ≤ ∫ x : ℝ, ‖readoutKernel s x*(factorialMuntzTail n x : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, tailReadoutEnvelope n s x :=
      integral_mono (factorialMuntzTail_readout_integrable n s hs).norm
        (tailReadoutEnvelope_integrable n s hs) (tail_readout_norm_le n s)
    _ = _ := by
      rw [tailReadoutEnvelope, integral_indicator measurableSet_Iic, integral_div,
        integral_const_mul, integral_exp_mul_Iic hs]
      simp only [mul_zero, Real.exp_zero]
      field_simp

/-- At every right-half-plane zeta zero, the actual compact-ramp readout is
exactly the opposite tail readout, with a source-derived quantitative bound. -/
theorem factorialRamp_zeta_readout (n : ℕ) :
    ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 →
      (∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)) =
        -(∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(factorialMuntzTail n x : ℂ)) ∧
      ‖∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)‖ ≤
        10/(Real.sqrt ((n+1 : ℕ) : ℝ)*ρ.re) := by
  intro ρ hρ hz
  have hF : Integrable (fun x : ℝ => readoutKernel ρ x*(factorialMuntzCompletion n x : ℂ)) :=
    factorialMuntzCompletion_readout_integrable n ρ hρ
  have hT : Integrable (fun x : ℝ => readoutKernel ρ x*(factorialMuntzTail n x : ℂ)) :=
    factorialMuntzTail_readout_integrable n ρ hρ
  have hzero : (∫ x : ℝ, readoutKernel ρ x*(factorialMuntzCompletion n x : ℂ)) = 0 := by
    rw [show (∫ x : ℝ, readoutKernel ρ x*(factorialMuntzCompletion n x : ℂ)) =
      mellin (fun t => (factorialMuntzSum n t : ℂ)) ρ/(Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ) from
      factorialMuntzCompletion_readout_eq_mellin n ρ,
      factorialMuntzSum_mellin_zero n ρ hρ hz, zero_div]
  have he : (fun x : ℝ => readoutKernel ρ x*(sourceFactorialRamp (n+1) x : ℂ)) =
      fun x => readoutKernel ρ x*(factorialMuntzCompletion n x : ℂ)-
        readoutKernel ρ x*(factorialMuntzTail n x : ℂ) := by
    funext x
    rw [← factorialMuntzCompletion_sub_ramp n x, Complex.ofReal_sub]
    ring
  have hid : (∫ x : ℝ, readoutKernel ρ x*(sourceFactorialRamp (n+1) x : ℂ)) =
      -(∫ x : ℝ, readoutKernel ρ x*(factorialMuntzTail n x : ℂ)) := by
    rw [he, integral_sub hF hT, hzero, zero_sub]
  refine ⟨hid, ?_⟩
  change ‖∫ x : ℝ, readoutKernel ρ x*(sourceFactorialRamp (n+1) x : ℂ)‖ ≤ _
  rw [hid, norm_neg]
  exact factorialMuntzTail_readout_norm_le n ρ hρ

/-- The same quantitative certificate for the literal reflected source used
as the ramp diagonal of the full Weil Gram matrix. -/
theorem factorialSourceLeft_zeta_readout_norm_le (n : ℕ) :
    ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 →
      ‖∫ u : ℝ, Complex.exp ((1/2-ρ)*(u : ℂ))*(factorialSourceLeft n u : ℂ)‖ ≤
        10/(Real.sqrt ((n+1 : ℕ) : ℝ)*ρ.re) := by
  intro ρ hρ hz
  have he : (∫ u : ℝ, Complex.exp ((1/2-ρ)*(u : ℂ))*(factorialSourceLeft n u : ℂ)) =
      ∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ) := by
    rw [← integral_neg_eq_self (fun u : ℝ =>
      Complex.exp ((1/2-ρ)*(u : ℂ))*(factorialSourceLeft n u : ℂ))]
    apply integral_congr_ae
    filter_upwards [] with x
    change Complex.exp ((1/2-ρ)*((-x : ℝ) : ℂ))*(sourceFactorialRamp (n+1) (-(-x)) : ℂ) = _
    rw [neg_neg, Complex.ofReal_neg]
    congr 2
    ring
  rw [he]
  exact (factorialRamp_zeta_readout n ρ hρ hz).2

/-- Fixed zero readouts vanish for this concrete source family, regardless
of a zero's position relative to the critical line. -/
theorem factorialSourceLeft_zeta_readout_tendsto :
    ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 →
      Tendsto (fun n : ℕ => ∫ u : ℝ,
        Complex.exp ((1/2-ρ)*(u : ℂ))*(factorialSourceLeft n u : ℂ)) atTop (𝓝 0) := by
  intro ρ hρ hz
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ => 1/Real.sqrt ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow, one_div] using
      tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hn)
  have hb : Tendsto (fun n : ℕ => 10/(Real.sqrt ((n+1 : ℕ) : ℝ)*ρ.re)) atTop (𝓝 0) := by
    have he : (fun n : ℕ => 10/(Real.sqrt ((n+1 : ℕ) : ℝ)*ρ.re)) =
        fun n => (10/ρ.re)*(1/Real.sqrt ((n+1 : ℕ) : ℝ)) := by
      funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    simpa using hi.const_mul (10/ρ.re)
  exact squeeze_zero_norm (fun n => factorialSourceLeft_zeta_readout_norm_le n ρ hρ hz) hb

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
