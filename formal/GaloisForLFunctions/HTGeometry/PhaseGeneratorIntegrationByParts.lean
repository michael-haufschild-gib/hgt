import GaloisForLFunctions.HTGeometry.InverseFamilyDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integrating by parts against an invertible phase generator

If a propagator satisfies `E' = −i E C` with `C` invertible, then `E = i E' C⁻¹`, so every integral
of `E` against a commuting amplitude can be integrated by parts once, trading the amplitude `G` for
`(C⁻¹G)'` and producing the boundary term `i[E C⁻¹ G]`.

Iterating the step twice with `G = 1` and then `G = (C⁻¹)'` gives the card's two-fold expansion

`∫ E = i[E C⁻¹] + [E C⁻¹(C⁻¹)'] − ∫ E [C⁻¹(C⁻¹)']'`,

in which each successive term carries one more power of the resolvent.  Nothing here is oscillatory
in the classical sense: the gain comes entirely from invertibility of the generator, so a generator
whose numerical floor grows with the frequency yields a genuine decay at every step.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- **One integration by parts against the phase generator.** -/
theorem phase_ibp_step {E Eder V Vder G : ℝ → R} {a b : ℝ}
    (hE : ∀ t ∈ uIcc a b, HasDerivAt E (Eder t) t)
    (hV : ∀ t ∈ uIcc a b, HasDerivAt V (Vder t) t)
    (hEint : IntervalIntegrable Eder volume a b)
    (hVint : IntervalIntegrable Vder volume a b)
    (hprod₁ : IntervalIntegrable (fun t => Eder t * V t) volume a b)
    (hprod₂ : IntervalIntegrable (fun t => E t * Vder t) volume a b)
    (hrel : ∀ t ∈ uIcc a b, E t * G t = (Complex.I : ℂ) • (Eder t * V t)) :
    (∫ t in a..b, E t * G t)
      = (Complex.I : ℂ) • ((E b * V b - E a * V a) - ∫ t in a..b, E t * Vder t) := by
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub hE hV hEint hVint
  have hsplit : (∫ t in a..b, (Eder t * V t + E t * Vder t))
      = (∫ t in a..b, Eder t * V t) + ∫ t in a..b, E t * Vder t :=
    intervalIntegral.integral_add hprod₁ hprod₂
  rw [hsplit] at hIBP
  have hfirst : (∫ t in a..b, Eder t * V t)
      = (E b * V b - E a * V a) - ∫ t in a..b, E t * Vder t := by
    rw [← hIBP]
    abel
  have hcongr : (∫ t in a..b, E t * G t)
      = (Complex.I : ℂ) • ∫ t in a..b, Eder t * V t := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun t ht => hrel t ht
  rw [hcongr, hfirst]

/-! ## The relation supplied by the phase equation -/

omit [CompleteSpace R] in
/-- **The phase equation inverts.**  From `E' = −i E C` with `C` a unit, `E` is recovered as
`i E' C⁻¹`, and the same holds after multiplying by any amplitude. -/
theorem phase_rel_of_generator {E Eder C : ℝ → R} {t : ℝ}
    (hgen : Eder t = (-(Complex.I) : ℂ) • (E t * C t))
    (hu : IsUnit (C t)) (G : ℝ → R) :
    E t * G t = (Complex.I : ℂ) • (Eder t * (invFamily C t * G t)) := by
  have hcancel : C t * invFamily C t = 1 := Ring.mul_inverse_cancel _ hu
  rw [hgen, smul_mul_assoc, smul_smul]
  have hnum : (Complex.I : ℂ) * (-(Complex.I) : ℂ) = 1 := by
    simp [Complex.I_mul_I]
  rw [hnum, one_smul, mul_assoc, ← mul_assoc (C t), hcancel, one_mul]

/-! ## The two-fold expansion -/

/-- **`(18)`: two integrations by parts.**  Each step trades one power of the amplitude for one
power of the resolvent, leaving the two boundary terms and a remainder whose amplitude is
`[C⁻¹(C⁻¹)']'`. -/
theorem phase_ibp_twice {E Eder C C₁ C₂ : ℝ → R} {a b : ℝ}
    (hgen : ∀ t ∈ uIcc a b, Eder t = (-(Complex.I) : ℂ) • (E t * C t))
    (hu : ∀ t ∈ uIcc a b, IsUnit (C t))
    (hC : ∀ t ∈ uIcc a b, HasDerivAt C (C₁ t) t)
    (hC₁ : ∀ t ∈ uIcc a b, HasDerivAt C₁ (C₂ t) t)
    (hE : ∀ t ∈ uIcc a b, HasDerivAt E (Eder t) t)
    (hEint : IntervalIntegrable Eder volume a b)
    (hDint : IntervalIntegrable (invFamilyDeriv C C₁) volume a b)
    (hPint : IntervalIntegrable (invFamilyProductDeriv C C₁ C₂) volume a b)
    (hp₁ : IntervalIntegrable (fun t => Eder t * invFamily C t) volume a b)
    (hp₂ : IntervalIntegrable (fun t => E t * invFamilyDeriv C C₁ t) volume a b)
    (hp₃ : IntervalIntegrable (fun t => Eder t * invFamilyProduct C C₁ t) volume a b)
    (hp₄ : IntervalIntegrable (fun t => E t * invFamilyProductDeriv C C₁ C₂ t) volume a b) :
    (∫ t in a..b, E t * 1)
      = (Complex.I : ℂ) • (E b * invFamily C b - E a * invFamily C a)
        + (E b * invFamilyProduct C C₁ b - E a * invFamilyProduct C C₁ a)
        - ∫ t in a..b, E t * invFamilyProductDeriv C C₁ C₂ t := by
  have hDderiv : ∀ t ∈ uIcc a b, HasDerivAt (invFamily C) (invFamilyDeriv C C₁ t) t :=
    fun t ht => hasDerivAt_invFamily (hC t ht) (hu t ht)
  have hPderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (invFamilyProduct C C₁) (invFamilyProductDeriv C C₁ C₂ t) t :=
    fun t ht => hasDerivAt_invFamilyProduct (hC t ht) (hu t ht) (hC₁ t ht)
  -- first step, amplitude `1`
  have hrel₁ : ∀ t ∈ uIcc a b, E t * (1 : R) = (Complex.I : ℂ) • (Eder t * invFamily C t) := by
    intro t ht
    have := phase_rel_of_generator (hgen t ht) (hu t ht) (fun _ => (1 : R))
    simpa using this
  have hstep₁ := phase_ibp_step (G := fun _ => (1 : R)) hE hDderiv hEint hDint hp₁ hp₂ hrel₁
  -- second step, amplitude `(C⁻¹)'`
  have hrel₂ : ∀ t ∈ uIcc a b, E t * invFamilyDeriv C C₁ t
      = (Complex.I : ℂ) • (Eder t * invFamilyProduct C C₁ t) := by
    intro t ht
    have := phase_rel_of_generator (hgen t ht) (hu t ht) (invFamilyDeriv C C₁)
    rw [invFamilyProduct]
    exact this
  have hstep₂ := phase_ibp_step (G := invFamilyDeriv C C₁) hE hPderiv hEint hPint hp₃ hp₄ hrel₂
  rw [hstep₁, hstep₂]
  have hII : (Complex.I : ℂ) • ((Complex.I : ℂ) •
      ((E b * invFamilyProduct C C₁ b - E a * invFamilyProduct C C₁ a)
        - ∫ t in a..b, E t * invFamilyProductDeriv C C₁ C₂ t))
      = -(((E b * invFamilyProduct C C₁ b - E a * invFamilyProduct C C₁ a)
        - ∫ t in a..b, E t * invFamilyProductDeriv C C₁ C₂ t)) := by
    rw [smul_smul, Complex.I_mul_I]
    simp
  rw [smul_sub, hII]
  abel

end GaloisForLFunctions.HTGeometry
