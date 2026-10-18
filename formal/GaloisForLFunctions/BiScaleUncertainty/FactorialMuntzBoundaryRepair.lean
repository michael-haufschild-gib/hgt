import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzBoundaryPole
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzReadout
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource

/-! Unique polar correction of the actual Müntz completion. The correction
admits both pole moments and leaves an exact, nonzero rational readout at zeta zeros.
No full-Weil domain or positivity assertion is inferred from these facts. -/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

def factorialMuntzBoundaryCorrected (n : ℕ) (c : ℝ) (x : ℝ) : ℝ :=
  factorialMuntzCompletion n x+(Iic (0 : ℝ)).indicator (fun y => c*Real.exp (y/2)) x

private theorem half_exp_cancel (x : ℝ) : Real.exp (-x/2)*Real.exp (x/2) = 1 := by
  rw [← Real.exp_add, show -x/2+x/2 = 0 by ring, Real.exp_zero]

private theorem corrected_negPole (n : ℕ) (c x : ℝ) :
    Real.exp (-x/2)*factorialMuntzBoundaryCorrected n c x =
      Real.exp (-x/2)*factorialMuntzCompletion n x+
        (Iic (0 : ℝ)).indicator (fun _ => c) x := by
  by_cases hx : x ≤ 0
  · simp only [factorialMuntzBoundaryCorrected,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx), mul_add]
    rw [mul_left_comm (Real.exp (-x/2)) c, half_exp_cancel, mul_one]
  · simp only [factorialMuntzBoundaryCorrected,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), add_zero]

private theorem corrected_negPole_decomposition (n : ℕ) (c x : ℝ) :
    Real.exp (-x/2)*factorialMuntzBoundaryCorrected n c x =
      Real.exp (-x/2)*sourceFactorialRamp (n+1) x+
        (Iic (0 : ℝ)).indicator
          (fun y => Real.exp (-y/2)*factorialMuntzCompletion n y+c) x := by
  by_cases hx : x ≤ 0
  · simp only [corrected_negPole,
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      sourceFactorialRamp_zero_of_nonpos (N := n+1) (by omega) hx, mul_zero, zero_add]
  · have he : factorialMuntzCompletion n x = sourceFactorialRamp (n+1) x :=
      factorialMuntzCompletion_eq_ramp n (by linarith)
    simp only [corrected_negPole,
      indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx), he, add_zero]

theorem factorialMuntzBoundaryCorrected_negPole_integrable (n : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-x/2)*
      factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x) := by
  have hw : Continuous (fun x : ℝ => Real.exp (-x/2)) := by fun_prop
  have hm : Measurable (fun x : ℝ =>
      Real.exp (-x/2)*factorialMuntzCompletion n x+factorialMuntzBoundaryCoefficient n) :=
    (hw.measurable.mul (factorialMuntzCompletion_measurable n)).add measurable_const
  have ht : IntegrableOn (fun x : ℝ =>
      Real.exp (-x/2)*factorialMuntzCompletion n x+factorialMuntzBoundaryCoefficient n)
      (Iic (0 : ℝ)) := by
    apply ((integrableOn_exp_Iic 0).const_mul (factorialMuntzBoundaryError n)).mono'
      hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using factorialMuntzCompletion_boundary_error n x
  have hr : Integrable (fun x : ℝ => Real.exp (-x/2)*sourceFactorialRamp (n+1) x) :=
    (hw.mul (continuous_sourceFactorialRamp (n+1))).integrable_of_hasCompactSupport
      (hasCompactSupport_sourceFactorialRamp (N := n+1) (by omega)).mul_left
  apply (hr.add (ht.integrable_indicator measurableSet_Iic)).congr
  exact Eventually.of_forall fun x =>
    (corrected_negPole_decomposition n (factorialMuntzBoundaryCoefficient n) x).symm

/-- Exact classification: a single coefficient, determined by the source,
admits the negative polar moment. -/
theorem factorialMuntzBoundaryCorrected_negPole_integrable_iff (n : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x/2)*factorialMuntzBoundaryCorrected n c x) ↔
      c = factorialMuntzBoundaryCoefficient n := by
  constructor
  · intro h
    have hc : IntegrableOn (fun _ : ℝ => c-factorialMuntzBoundaryCoefficient n)
        (Iic (0 : ℝ)) := by
      apply (h.sub (factorialMuntzBoundaryCorrected_negPole_integrable n)).integrableOn.congr_fun
        ?_ measurableSet_Iic
      intro x hx
      change Real.exp (-x/2)*factorialMuntzBoundaryCorrected n c x-
        Real.exp (-x/2)*factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x =
          c-factorialMuntzBoundaryCoefficient n
      rw [corrected_negPole n c x,
        corrected_negPole n (factorialMuntzBoundaryCoefficient n) x]
      simp only [indicator_of_mem hx]
      ring
    have hz : c-factorialMuntzBoundaryCoefficient n = 0 := by
      rcases (integrableOn_const_iff (C := c-factorialMuntzBoundaryCoefficient n)).mp hc with h | h
      · exact enorm_eq_zero.mp h
      · exfalso
        simpa only [Real.volume_Iic, lt_self_iff_false] using h
    linarith
  · intro hc
    rw [hc]
    exact factorialMuntzBoundaryCorrected_negPole_integrable n

/-- Small unweighted tail mass and zero readouts do not make the original
completion admissible at the negative pole. -/
theorem not_integrable_factorialMuntzCompletion_negPole (n : ℕ) :
    ¬ Integrable (fun x : ℝ => Real.exp (-x/2)*factorialMuntzCompletion n x) := by
  have he : factorialMuntzBoundaryCorrected n 0 = factorialMuntzCompletion n := by
    funext x
    simp [factorialMuntzBoundaryCorrected]
  intro h
  have hc := (factorialMuntzBoundaryCorrected_negPole_integrable_iff n 0).mp
    (by simpa only [he] using h)
  have hp := factorialMuntzBoundaryCoefficient_pos n
  linarith

private theorem boundary_readout_integrand (c : ℝ) (s : ℂ) (x : ℝ) :
    Complex.exp ((s-1/2)*(x : ℂ))*
        (((Iic (0 : ℝ)).indicator (fun y : ℝ => c*Real.exp (y/2)) x : ℝ) : ℂ) =
      (Iic (0 : ℝ)).indicator (fun y => (c : ℂ)*Complex.exp (s*(y : ℂ))) x := by
  by_cases hx : x ≤ 0
  · simp only [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx),
      Complex.ofReal_mul, Complex.ofReal_exp]
    rw [mul_left_comm, ← Complex.exp_add]
    apply congrArg (fun z : ℂ => (c : ℂ)*Complex.exp z)
    push_cast
    ring
  · simp only [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
      Complex.ofReal_zero, mul_zero]

private theorem corrected_readout_integrand (n : ℕ) (c : ℝ) (s : ℂ) (x : ℝ) :
    Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzBoundaryCorrected n c x : ℂ) =
      Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzCompletion n x : ℂ)+
        (Iic (0 : ℝ)).indicator (fun y => (c : ℂ)*Complex.exp (s*(y : ℂ))) x := by
  simp only [factorialMuntzBoundaryCorrected, Complex.ofReal_add, mul_add,
    boundary_readout_integrand]

private theorem boundary_readout_integrable (c : ℝ) (s : ℂ) (hs : 0 < s.re) :
    Integrable ((Iic (0 : ℝ)).indicator (fun x : ℝ => (c : ℂ)*Complex.exp (s*(x : ℂ)))) :=
  IntegrableOn.integrable_indicator
    ((integrableOn_exp_mul_complex_Iic hs 0).const_mul (c : ℂ)) measurableSet_Iic

theorem factorialMuntzBoundaryCorrected_readout_integrable (n : ℕ) (c : ℝ)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ =>
      Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzBoundaryCorrected n c x : ℂ)) := by
  simp_rw [corrected_readout_integrand]
  exact (factorialMuntzCompletion_readout_integrable n s hs).add
    (boundary_readout_integrable c s hs)

/-- The correction changes the entire right-half-plane readout by exactly `c/s`. -/
theorem factorialMuntzBoundaryCorrected_readout_eq (n : ℕ) (c : ℝ)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ x : ℝ, Complex.exp ((s-1/2)*(x : ℂ))*(factorialMuntzBoundaryCorrected n c x : ℂ)) =
      mellin (fun t => (factorialMuntzSum n t : ℂ)) s/
        (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ)+(c : ℂ)/s := by
  simp_rw [corrected_readout_integrand]
  rw [integral_add (factorialMuntzCompletion_readout_integrable n s hs)
      (boundary_readout_integrable c s hs), factorialMuntzCompletion_readout_eq_mellin,
    integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_mul_complex_Iic hs]
  simp [div_eq_mul_inv]

theorem factorialMuntzBoundaryCorrected_posPole_integrable (n : ℕ) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (x/2)*factorialMuntzBoundaryCorrected n c x) := by
  have h := (factorialMuntzBoundaryCorrected_readout_integrable n c (1 : ℂ) (by norm_num)).re
  change Integrable (fun x : ℝ =>
    (Complex.exp (((1 : ℂ)-1/2)*(x : ℂ))*(factorialMuntzBoundaryCorrected n c x : ℂ)).re) at h
  have he (x : ℝ) : Complex.exp (((1 : ℂ)-1/2)*(x : ℂ)) = (Real.exp (x/2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simpa only [he, ← Complex.ofReal_mul, Complex.ofReal_re] using h

theorem factorialMuntzBoundaryCorrected_zeta_readout (n : ℕ) (c : ℝ)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    (∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*(factorialMuntzBoundaryCorrected n c x : ℂ)) =
      (c : ℂ)/ρ := by
  rw [factorialMuntzBoundaryCorrected_readout_eq n c ρ hρ,
    factorialMuntzSum_mellin_zero n ρ hρ hz, zero_div, zero_add]

/-- The unique polar-admissible correction has a nonzero exact readout at every
right-half-plane zeta zero; it is not a null-source certificate. -/
theorem factorialMuntzBoundaryCorrected_canonical_zeta_readout_ne_zero (n : ℕ)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    (∫ x : ℝ, Complex.exp ((ρ-1/2)*(x : ℂ))*
      (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ≠ 0 := by
  rw [factorialMuntzBoundaryCorrected_zeta_readout n _ hρ hz]
  apply div_ne_zero
  · exact_mod_cast (factorialMuntzBoundaryCoefficient_pos n).ne'
  · rintro rfl
    norm_num at hρ

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
