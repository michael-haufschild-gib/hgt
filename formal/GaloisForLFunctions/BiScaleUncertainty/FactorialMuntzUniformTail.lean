import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzBoundaryRepair

/-! The actual collar cancels the apparent nonuniform boundary constant.
The canonical corrected tail has uniform exponential decay, including at both
polar weights, and its readout converges throughout `Re s > -1`. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

private theorem collar_scaled_lower (n : ℕ) :
    1/15 ≤ ((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1) := by
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have h := (sourceFactorialWidth_bounds (N := n+1) (by omega)).1.trans
    (sourceFactorialWidth_le_collar (n+1))
  have hh := (div_le_iff₀ (by positivity : 0 < 15*((n+1 : ℕ) : ℝ))).mp h
  nlinarith

/-- The shrinking collar costs no additional power of the source scale. -/
theorem factorialMuntzBoundaryError_uniform (n : ℕ) :
    factorialMuntzBoundaryError n ≤ 12/Real.sqrt ((n+1 : ℕ) : ℝ) := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hs : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := by positivity
  have he : (12/Real.sqrt ((n+1 : ℕ) : ℝ))*
      (32*((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1)*Real.sqrt ((n+1 : ℕ) : ℝ)) =
      384*((n+1 : ℕ) : ℝ)*sourceFactorialCollar (n+1) := by
    field_simp <;> ring
  unfold factorialMuntzBoundaryError
  apply (div_le_iff₀ (by positivity)).2
  rw [he]
  nlinarith [collar_scaled_lower n]

theorem factorialMuntzSum_boundary_error_uniform (n : ℕ) {t : ℝ} (ht : 0 < t) :
    |factorialMuntzSum n t+1/2| ≤ 12*t := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  refine (factorialMuntzSum_boundary_error n ht).trans ?_
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right (collar_scaled_lower n) ht.le]

def factorialMuntzCorrectedTail (n : ℕ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator
    (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n))

theorem factorialMuntzBoundaryCorrected_sub_ramp (n : ℕ) (x : ℝ) :
    factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x-
      sourceFactorialRamp (n+1) x = factorialMuntzCorrectedTail n x := by
  by_cases hx : x ≤ 0
  · rw [factorialMuntzCorrectedTail, indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      sourceFactorialRamp_zero_of_nonpos (by omega : 1 ≤ n+1) hx, sub_zero]
  · simp only [factorialMuntzCorrectedTail, factorialMuntzBoundaryCorrected,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), add_zero,
      factorialMuntzCompletion_eq_ramp n (le_of_lt (lt_of_not_ge hx)), sub_self]

theorem factorialMuntzCorrectedTail_measurable (n : ℕ) :
    Measurable (factorialMuntzCorrectedTail n) := by
  have hc : Continuous (fun x : ℝ => factorialMuntzBoundaryCoefficient n*Real.exp (x/2)) := by
    fun_prop
  exact ((factorialMuntzCompletion_measurable n).add
    (hc.measurable.indicator measurableSet_Iic)).indicator measurableSet_Iic

theorem factorialMuntzCorrectedTail_abs_le (n : ℕ) (x : ℝ) :
    |factorialMuntzCorrectedTail n x| ≤
      (Iic (0 : ℝ)).indicator (fun y => 12*Real.exp (3*y/2)/Real.sqrt ((n+1 : ℕ) : ℝ)) x := by
  by_cases hx : x ≤ 0
  · have he : factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x =
        Real.exp (x/2)*(Real.exp (-x/2)*factorialMuntzCompletion n x+
          factorialMuntzBoundaryCoefficient n) := by
      rw [factorialMuntzBoundaryCorrected, indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
        mul_add, ← mul_assoc,
        ← Real.exp_add, show x/2+-x/2 = 0 by ring, Real.exp_zero]
      ring
    rw [factorialMuntzCorrectedTail, indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx), he,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (x/2)*(factorialMuntzBoundaryError n*Real.exp x) :=
        mul_le_mul_of_nonneg_left (factorialMuntzCompletion_boundary_error n x)
          (Real.exp_pos _).le
      _ ≤ Real.exp (x/2)*((12/Real.sqrt ((n+1 : ℕ) : ℝ))*Real.exp x) := by
        gcongr
        exact factorialMuntzBoundaryError_uniform n
      _ = _ := by
        have hh : Real.exp (x/2)*Real.exp x = Real.exp (3*x/2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = 12*(Real.exp (x/2)*Real.exp x)/Real.sqrt ((n+1 : ℕ) : ℝ) := by ring
          _ = _ := by rw [hh]
  · simp only [factorialMuntzCorrectedTail,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), abs_zero, le_refl]

private def correctedTailEnvelope (n : ℕ) (s : ℂ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator
    (fun x => 12*Real.exp ((s.re+1)*x)/Real.sqrt ((n+1 : ℕ) : ℝ))

private theorem correctedTailEnvelope_integrable (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    Integrable (correctedTailEnvelope n s) :=
  IntegrableOn.integrable_indicator
    (((integrableOn_exp_mul_Iic (by linarith : 0 < s.re+1) 0).const_mul 12).div_const _)
      measurableSet_Iic

private theorem corrected_tail_readout_bound (n : ℕ) (s : ℂ) (x : ℝ) :
    ‖Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ ≤
      correctedTailEnvelope n s x := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have he : ((s-1/2)*(x : ℂ)).re = (s.re-1/2)*x := by simp
  rw [he]
  by_cases hx : x ≤ 0
  · have hb := factorialMuntzCorrectedTail_abs_le n x
    rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)] at hb
    rw [correctedTailEnvelope, indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx)]
    calc
      _ ≤ Real.exp ((s.re-1/2)*x)*(12*Real.exp (3*x/2)/Real.sqrt ((n+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := by
        have hh : Real.exp ((s.re-1/2)*x)*Real.exp (3*x/2) = Real.exp ((s.re+1)*x) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = 12*(Real.exp ((s.re-1/2)*x)*Real.exp (3*x/2))/
              Real.sqrt ((n+1 : ℕ) : ℝ) := by ring
          _ = _ := by rw [hh]
  · simp only [factorialMuntzCorrectedTail, correctedTailEnvelope,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), abs_zero, mul_zero, le_refl]

theorem factorialMuntzCorrectedTail_readout_integrable (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    Integrable (fun x : ℝ =>
      Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)) := by
  have hk : Continuous (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))) := by fun_prop
  apply (correctedTailEnvelope_integrable n s hs).mono'
    (hk.measurable.mul (Complex.measurable_ofReal.comp
      (factorialMuntzCorrectedTail_measurable n))).aestronglyMeasurable
  exact Eventually.of_forall (corrected_tail_readout_bound n s)

/-- Explicit truncation control remains valid at the negative polar parameter. -/
theorem factorialMuntzCorrectedTail_readout_cutoff_norm_le (n : ℕ) (s : ℂ)
    (hs : -1 < s.re) {a : ℝ} (ha : a ≤ 0) :
    ‖∫ x in Iic a, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ ≤
      12*Real.exp ((s.re+1)*a)/(Real.sqrt ((n+1 : ℕ) : ℝ)*(s.re+1)) := by
  have hi := (factorialMuntzCorrectedTail_readout_integrable n s hs).integrableOn
    (s := Iic a)
  have hj : IntegrableOn (fun x : ℝ => 12*Real.exp ((s.re+1)*x)/
      Real.sqrt ((n+1 : ℕ) : ℝ)) (Iic a) :=
    ((integrableOn_exp_mul_Iic (by linarith : 0 < s.re+1) a).const_mul 12).div_const _
  calc
    _ ≤ ∫ x in Iic a, ‖Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Iic a, 12*Real.exp ((s.re+1)*x)/Real.sqrt ((n+1 : ℕ) : ℝ) := by
      apply integral_mono_ae hi.norm hj
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hb := corrected_tail_readout_bound n s x
      simpa only [correctedTailEnvelope,
        indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx.trans ha)] using hb
    _ = _ := by
      rw [integral_div, integral_const_mul, integral_exp_mul_Iic (by linarith : 0 < s.re+1)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem factorialMuntzCorrectedTail_readout_integral_norm_le (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    (∫ x : ℝ, ‖Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖) ≤
      12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(s.re+1)) := by
  calc
    _ ≤ ∫ x : ℝ, correctedTailEnvelope n s x :=
      integral_mono (factorialMuntzCorrectedTail_readout_integrable n s hs).norm
        (correctedTailEnvelope_integrable n s hs) (corrected_tail_readout_bound n s)
    _ = _ := by
      rw [correctedTailEnvelope, integral_indicator measurableSet_Iic, integral_div,
        integral_const_mul, integral_exp_mul_Iic (by linarith : 0 < s.re+1)]
      simp only [mul_zero, Real.exp_zero]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem factorialMuntzCorrectedTail_readout_norm_le (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    ‖∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ ≤
      12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(s.re+1)) :=
  (norm_integral_le_integral_norm _).trans
    (factorialMuntzCorrectedTail_readout_integral_norm_le n s hs)

private theorem ramp_readout_integrable (n : ℕ) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*
      (sourceFactorialRamp (n+1) x : ℂ)) := by
  have hk : Continuous (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))) := by fun_prop
  have hc := hk.mul (Complex.continuous_ofReal.comp (continuous_sourceFactorialRamp (n+1)))
  exact hc.integrable_of_hasCompactSupport
    ((hasCompactSupport_sourceFactorialRamp (N := n+1) (by omega)).comp_left
      Complex.ofReal_zero).mul_left

private theorem corrected_readout_split (n : ℕ) (s : ℂ) (x : ℝ) :
    Complex.exp ((s-1/2)*(x : ℂ))*
        (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ) =
      Complex.exp ((s-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)+
        Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ) := by
  rw [← factorialMuntzBoundaryCorrected_sub_ramp, Complex.ofReal_sub]
  ring

/-- The actual canonical correction admits every readout on `Re s > -1`. -/
theorem factorialMuntzBoundaryCorrected_readout_integrable_extended (n : ℕ) (s : ℂ)
    (hs : -1 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) := by
  simp_rw [corrected_readout_split]
  exact (ramp_readout_integrable n s).add (factorialMuntzCorrectedTail_readout_integrable n s hs)

theorem factorialMuntzBoundaryCorrected_readout_sub_ramp (n : ℕ) (s : ℂ) (hs : -1 < s.re) :
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*
        (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))-
      (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)) =
      ∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ) := by
  simp_rw [corrected_readout_split]
  rw [integral_add (ramp_readout_integrable n s)
    (factorialMuntzCorrectedTail_readout_integrable n s hs)]
  ring

/-- The tail remainder has no singularity as a zeta zero approaches `Re s=0`. -/
theorem factorialRamp_zeta_readout_boundary_bound (n : ℕ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    ‖∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)‖ ≤
      factorialMuntzBoundaryCoefficient n/‖ρ‖+
        12/(Real.sqrt ((n+1 : ℕ) : ℝ)*(ρ.re+1)) := by
  have he := factorialMuntzBoundaryCorrected_readout_sub_ramp n ρ (by linarith)
  rw [factorialMuntzBoundaryCorrected_zeta_readout n _ hρ hz] at he
  have hid : (∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(sourceFactorialRamp (n+1) x : ℂ)) =
      (factorialMuntzBoundaryCoefficient n : ℂ)/ρ-
        ∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ) := by
    linear_combination -he
  rw [hid]
  calc
    _ ≤ ‖(factorialMuntzBoundaryCoefficient n : ℂ)/ρ‖+
        ‖∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(factorialMuntzCorrectedTail n x : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (factorialMuntzBoundaryCoefficient_pos n)]
      linarith only [factorialMuntzCorrectedTail_readout_norm_le n ρ (by linarith)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
