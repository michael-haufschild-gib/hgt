import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularWeightedHorizontalEnergy

/-!
# All complex shifts survive the PW source-square norm

The singular connection at every complex shift has exactly one line of solutions.
Its normalized mode is nowhere zero and has finite positive energy in the square
of the original Gamma log profile. The connection image has finite energy too.
Reflection exchanges opposite shifts with equal energy. These pointwise equations
and integrability statements do not identify a closed physical operator domain,
an adjoint, a Fredholm index, or Xi spectral occurrence.
-/

open Real MeasureTheory GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The normalized mode of the singular PW connection at a complex shift. -/
def pwLogShiftedSourceMode (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((pwLogSingularGaugePotential t : ℂ) + z * (t : ℂ))

/-- Complex-linear extension of the exact singular weighted reflection. -/
def pwLogSingularComplexReflection (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (pwLogSingularGain t : ℂ) * f (-t)

theorem pwLogShiftedSourceMode_zero (z : ℂ) : pwLogShiftedSourceMode z 0 = 1 := by
  simp [pwLogShiftedSourceMode, pwLogSingularGaugePotential]

theorem pwLogShiftedSourceMode_ne_zero (z : ℂ) (t : ℝ) :
    pwLogShiftedSourceMode z t ≠ 0 := Complex.exp_ne_zero _

private theorem pwLogShiftedExponent_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (pwLogSingularGaugePotential u : ℂ) + z * (u : ℂ))
      ((pwLogSingularConnectionPotential t : ℂ) + z) t := by
  have hp : HasDerivAt (fun u : ℝ => (pwLogSingularGaugePotential u : ℂ))
      (pwLogSingularConnectionPotential t : ℂ) t :=
    (hasDerivAt_pwLogSingularGaugePotential t).ofReal_comp
  have hz : HasDerivAt (fun u : ℝ => z * (u : ℂ)) z t := by
    simpa using (hasDerivAt_id t).ofReal_comp.const_mul z
  exact hp.add hz

theorem hasDerivAt_pwLogShiftedSourceMode (z : ℂ) (t : ℝ) :
    HasDerivAt (pwLogShiftedSourceMode z)
      (((pwLogSingularConnectionPotential t : ℂ) + z) * pwLogShiftedSourceMode z t) t := by
  exact (pwLogShiftedExponent_hasDerivAt z t).cexp.congr_deriv
    (by dsimp [pwLogShiftedSourceMode]; ring)

/-- Every solution at a fixed shift is a scalar multiple of the explicit mode. -/
theorem pwLogShiftedSourceMode_classification (z : ℂ) (f : ℝ → ℂ) :
    (∀ t, HasDerivAt f (((pwLogSingularConnectionPotential t : ℂ) + z) * f t) t) ↔
      ∃ c : ℂ, ∀ t, f t = c * pwLogShiftedSourceMode z t := by
  constructor
  · intro hf
    let A : ℝ → ℂ := fun t => (pwLogSingularGaugePotential t : ℂ) + z * (t : ℂ)
    have hzero : ∀ t, HasDerivAt (fun u => f u * Complex.exp (-A u)) 0 t := by
      intro t
      exact ((hf t).mul ((pwLogShiftedExponent_hasDerivAt z t).neg.cexp)).congr_deriv
        (by dsimp [A]; ring)
    have hconst (t : ℝ) := is_const_of_deriv_eq_zero
      (fun u => (hzero u).differentiableAt) (fun u => (hzero u).deriv) t 0
    refine ⟨f 0, fun t => ?_⟩
    apply mul_right_cancel₀ (Complex.exp_ne_zero (-A t))
    have he : pwLogShiftedSourceMode z t * Complex.exp (-A t) = 1 := by
      change Complex.exp (A t) * Complex.exp (-A t) = 1
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [mul_assoc, he, mul_one]
    simpa [A, pwLogSingularGaugePotential] using hconst t
  · rintro ⟨c, hc⟩ t
    have he : f = fun u => c * pwLogShiftedSourceMode z u := funext hc
    rw [he]
    exact ((hasDerivAt_pwLogShiftedSourceMode z t).const_mul c).congr_deriv (by ring)

/-- Exact source-square density of every shifted mode and every amplitude. -/
theorem pwLogShiftedSourceMode_energy_density (z c : ℂ) (t : ℝ) :
    pwLogGammaSourceDensity t * ‖c * pwLogShiftedSourceMode z t‖ ^ (2 : ℕ) =
      ‖c‖ ^ (2 : ℕ) * Real.exp (-2 * Real.cosh t + 2 * z.re * t) := by
  rw [norm_mul, mul_pow]
  calc
    pwLogGammaSourceDensity t * (‖c‖ ^ (2 : ℕ) * ‖pwLogShiftedSourceMode z t‖ ^ (2 : ℕ)) =
        ‖c‖ ^ (2 : ℕ) * (pwLogGammaSourceDensity t * ‖pwLogShiftedSourceMode z t‖ ^ (2 : ℕ)) := by ring
    _ = _ := by
      congr 1
      unfold pwLogGammaSourceDensity pwLogShiftedSourceMode expShift
      rw [Complex.norm_exp]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        mul_zero, sub_zero, Nat.cast_zero, add_zero, pow_two, ← Real.exp_add]
      congr 1
      rw [pwLogSingularGaugePotential, Real.sinh_eq, Real.cosh_eq]
      ring

/-- The even source core has every real exponential moment. -/
theorem pwLogGammaSourceCore_all_exponential_moments (b : ℝ) :
    Integrable (fun t => Real.exp (-2 * Real.cosh t + b * t)) := by
  have hA : 0 < |b| + 1 := by positivity
  have hmajor : Integrable (expShift (|b| + 1) 0) := by
    simpa only [iteratedDeriv_zero] using integrable_iteratedDeriv_expShift hA 0
  apply (hmajor.add hmajor.comp_neg).mono' (by fun_prop)
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hpos (u : ℝ) : 0 ≤ expShift (|b| + 1) 0 u := (Real.exp_pos _).le
  by_cases ht : 0 ≤ t
  · apply le_trans _ (le_add_of_nonneg_right (hpos (-t)))
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_zero, add_zero, Real.cosh_eq]
    have hb := mul_le_mul_of_nonneg_right (le_abs_self b) ht
    have he := Real.exp_pos (-t)
    nlinarith
  · apply le_trans _ (le_add_of_nonneg_left (hpos t))
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_zero, add_zero, Real.cosh_eq]
    have hb := mul_le_mul_of_nonneg_right (neg_le_abs b)
      (le_of_lt (neg_pos.mpr (lt_of_not_ge ht)))
    have he := Real.exp_pos t
    nlinarith

theorem pwLogShiftedSourceMode_energy_integrable (z c : ℂ) :
    Integrable (fun t => pwLogGammaSourceDensity t * ‖c * pwLogShiftedSourceMode z t‖ ^ (2 : ℕ)) := by
  simp only [pwLogShiftedSourceMode_energy_density]
  exact (pwLogGammaSourceCore_all_exponential_moments (2 * z.re)).const_mul _

theorem pwLogShiftedSourceMode_energy_pos (z : ℂ) :
    0 < ∫ t, pwLogGammaSourceDensity t * ‖pwLogShiftedSourceMode z t‖ ^ (2 : ℕ) := by
  have he (t : ℝ) : pwLogGammaSourceDensity t * ‖pwLogShiftedSourceMode z t‖ ^ (2 : ℕ) =
      Real.exp (-2 * Real.cosh t + 2 * z.re * t) := by
    simpa only [one_mul, norm_one, one_pow] using pwLogShiftedSourceMode_energy_density z 1 t
  simp only [he]
  exact integral_exp_pos (pwLogGammaSourceCore_all_exponential_moments (2 * z.re))

/-- Exact reflection pairs opposite shifts without excluding either one. -/
theorem pwLogSingularComplexReflection_shiftedMode (z : ℂ) :
    pwLogSingularComplexReflection (pwLogShiftedSourceMode z) = pwLogShiftedSourceMode (-z) := by
  funext t
  unfold pwLogSingularComplexReflection pwLogShiftedSourceMode pwLogSingularGain
  rw [Complex.ofReal_exp, ← Complex.exp_add, pwLogSingularGaugePotential_neg]
  congr 1
  push_cast
  ring

/-- The reflected pair has equal finite total source energy at every shift. -/
theorem pwLogShiftedSourceMode_reflected_energy (z : ℂ) :
    (∫ t, pwLogGammaSourceDensity t * ‖pwLogShiftedSourceMode (-z) t‖ ^ (2 : ℕ)) =
      ∫ t, pwLogGammaSourceDensity t * ‖pwLogShiftedSourceMode z t‖ ^ (2 : ℕ) := by
  have he (v : ℂ) (t : ℝ) :
      pwLogGammaSourceDensity t * ‖pwLogShiftedSourceMode v t‖ ^ (2 : ℕ) =
        Real.exp (-2 * Real.cosh t + 2 * v.re * t) := by
    simpa only [one_mul, norm_one, one_pow] using pwLogShiftedSourceMode_energy_density v 1 t
  simp only [he]
  convert integral_neg_eq_self (fun t => Real.exp (-2 * Real.cosh t + 2 * z.re * t)) volume using 1
  congr 1
  funext t
  simp only [Real.cosh_neg, Complex.neg_re]
  congr 1
  ring

/-- Every complex connection shift has a normalized, nowhere zero mode whose source-square
energy and connection-image energy are finite. No condition on the shift is assumed. -/
theorem pwLogGammaSource_every_complex_shift_admitted :
    ∀ z : ℂ, ∃ f : ℝ → ℂ,
      f 0 = 1 ∧ (∀ t, f t ≠ 0) ∧
      (∀ t, HasDerivAt f (((pwLogSingularConnectionPotential t : ℂ) + z) * f t) t) ∧
      Integrable (fun t => pwLogGammaSourceDensity t * ‖f t‖ ^ (2 : ℕ)) ∧
      Integrable (fun t => pwLogGammaSourceDensity t * ‖z * f t‖ ^ (2 : ℕ)) ∧
      (0 < ∫ t, pwLogGammaSourceDensity t * ‖f t‖ ^ (2 : ℕ)) ∧
      (∀ t, pwLogGammaSourceDensity t * ‖f t‖ ^ (2 : ℕ) =
        Real.exp (-2 * Real.cosh t + 2 * z.re * t)) := by
  intro z
  refine ⟨pwLogShiftedSourceMode z, pwLogShiftedSourceMode_zero z,
    pwLogShiftedSourceMode_ne_zero z, hasDerivAt_pwLogShiftedSourceMode z,
    ?_, pwLogShiftedSourceMode_energy_integrable z z, pwLogShiftedSourceMode_energy_pos z, ?_⟩
  · simpa only [one_mul] using pwLogShiftedSourceMode_energy_integrable z 1
  · intro t
    simpa only [one_mul, norm_one, one_pow] using pwLogShiftedSourceMode_energy_density z 1 t

end

end RHTower
