import GaloisForLFunctions.HTGeometry.PhaseGeneratorIntegrationByParts
import GaloisForLFunctions.HTGeometry.InverseFamilyThirdDerivative

/-!
# The three-fold expansion of a phase integral

Two integrations by parts leave the amplitude `∂D₁ = O(w²)`; a third leaves `∂D₂ = O(w³)`.  After
transport the remaining integral is weighted by the inverse propagator's growth `t^p`, so the
two-fold remainder integrates `t^{p-2}` — divergent once `p > 1` — while the three-fold remainder
integrates `t^{p-3}`, absolutely convergent for every `p < 2`.

The third step is the same step as the first two: the relation `E·G = i(E'·C⁻¹G)` holds for *every*
amplitude `G`, so with `G = ∂D₁` the new boundary amplitude is `C⁻¹∂D₁ = D₂`.  Only the
differentiability data grows: the symbol must now be three times differentiable with continuous third
derivative, and on a compact interval that makes every integrand continuous, hence integrable.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

set_option maxHeartbeats 1000000 in
/-- **The third step alone.**  With the amplitude `∂D₁` the new boundary term is `D₂ = C⁻¹∂D₁`. -/
theorem phase_ibp_third_step_of_continuousOn {E Eder C C₁ C₂ C₃ : ℝ → R} {a b : ℝ}
    (hgen : ∀ t ∈ uIcc a b, Eder t = (-(Complex.I) : ℂ) • (E t * C t))
    (hu : ∀ t ∈ uIcc a b, IsUnit (C t))
    (hE : ∀ t ∈ uIcc a b, HasDerivAt E (Eder t) t)
    (hC : ∀ t ∈ uIcc a b, HasDerivAt C (C₁ t) t)
    (hC₁ : ∀ t ∈ uIcc a b, HasDerivAt C₁ (C₂ t) t)
    (hC₂ : ∀ t ∈ uIcc a b, HasDerivAt C₂ (C₃ t) t)
    (hC₃ : ContinuousOn C₃ (uIcc a b)) :
    (∫ t in a..b, E t * invFamilyProductDeriv C C₁ C₂ t)
      = (Complex.I : ℂ) • ((E b * invFamilyProduct2 C C₁ C₂ b
          - E a * invFamilyProduct2 C C₁ C₂ a)
        - ∫ t in a..b, E t * invFamilyProduct2Deriv C C₁ C₂ C₃ t) := by
  have hC₁c : ContinuousOn C₁ (uIcc a b) := fun t ht =>
    ((hC₁ t ht).continuousAt).continuousWithinAt
  have hC₂c : ContinuousOn C₂ (uIcc a b) := fun t ht =>
    ((hC₂ t ht).continuousAt).continuousWithinAt
  have hEc : ContinuousOn E (uIcc a b) := fun t ht =>
    ((hE t ht).continuousAt).continuousWithinAt
  have hCc : ContinuousOn C (uIcc a b) := fun t ht =>
    ((hC t ht).continuousAt).continuousWithinAt
  have hEderc : ContinuousOn Eder (uIcc a b) := by
    refine ContinuousOn.congr ?_ hgen
    exact ((hEc.mul hCc).const_smul (-(Complex.I) : ℂ))
  have hQc : ContinuousOn (invFamilyProduct2 C C₁ C₂) (uIcc a b) :=
    continuousOn_invFamilyProduct2_of_unit hC hu hC₁c hC₂c
  have hQderivc : ContinuousOn (invFamilyProduct2Deriv C C₁ C₂ C₃) (uIcc a b) :=
    continuousOn_invFamilyProduct2Deriv_of_unit hC hu hC₁c hC₂c hC₃
  have hQderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (invFamilyProduct2 C C₁ C₂) (invFamilyProduct2Deriv C C₁ C₂ C₃ t) t :=
    fun t ht => hasDerivAt_invFamilyProduct2 (hC t ht) (hu t ht) (hC₁ t ht) (hC₂ t ht)
  have hrel₃ : ∀ t ∈ uIcc a b, E t * invFamilyProductDeriv C C₁ C₂ t
      = (Complex.I : ℂ) • (Eder t * invFamilyProduct2 C C₁ C₂ t) := by
    intro t ht
    have := phase_rel_of_generator (hgen t ht) (hu t ht) (invFamilyProductDeriv C C₁ C₂)
    rw [invFamilyProduct2]
    exact this
  exact phase_ibp_step (G := invFamilyProductDeriv C C₁ C₂) hE hQderiv
    hEderc.intervalIntegrable hQderivc.intervalIntegrable
    (hEderc.mul hQc).intervalIntegrable (hEc.mul hQderivc).intervalIntegrable hrel₃

set_option maxHeartbeats 1000000 in
/-- **The three-fold expansion `(45)`.** -/
theorem phase_ibp_thrice_of_continuousOn {E Eder C C₁ C₂ C₃ : ℝ → R} {a b : ℝ}
    (hgen : ∀ t ∈ uIcc a b, Eder t = (-(Complex.I) : ℂ) • (E t * C t))
    (hu : ∀ t ∈ uIcc a b, IsUnit (C t))
    (hE : ∀ t ∈ uIcc a b, HasDerivAt E (Eder t) t)
    (hC : ∀ t ∈ uIcc a b, HasDerivAt C (C₁ t) t)
    (hC₁ : ∀ t ∈ uIcc a b, HasDerivAt C₁ (C₂ t) t)
    (hC₂ : ∀ t ∈ uIcc a b, HasDerivAt C₂ (C₃ t) t)
    (hC₃ : ContinuousOn C₃ (uIcc a b)) :
    (∫ t in a..b, E t * 1)
      = (Complex.I : ℂ) • (E b * invFamily C b - E a * invFamily C a)
        + (E b * invFamilyProduct C C₁ b - E a * invFamilyProduct C C₁ a)
        - (Complex.I : ℂ) • (E b * invFamilyProduct2 C C₁ C₂ b
            - E a * invFamilyProduct2 C C₁ C₂ a)
        + (Complex.I : ℂ) • ∫ t in a..b, E t * invFamilyProduct2Deriv C C₁ C₂ C₃ t := by
  have hC₂c : ContinuousOn C₂ (uIcc a b) := fun t ht =>
    ((hC₂ t ht).continuousAt).continuousWithinAt
  have h2 := phase_ibp_twice_of_continuousOn hgen hu hE hC hC₁ hC₂c
  -- continuity of every piece
  have hEc : ContinuousOn E (uIcc a b) := fun t ht =>
    ((hE t ht).continuousAt).continuousWithinAt
  have hCc : ContinuousOn C (uIcc a b) := fun t ht =>
    ((hC t ht).continuousAt).continuousWithinAt
  have hC₁c : ContinuousOn C₁ (uIcc a b) := fun t ht =>
    ((hC₁ t ht).continuousAt).continuousWithinAt
  have hDc : ContinuousOn (invFamily C) (uIcc a b) := fun t ht =>
    ((hasDerivAt_invFamily (hC t ht) (hu t ht)).continuousAt).continuousWithinAt
  have hEderc : ContinuousOn Eder (uIcc a b) := by
    refine ContinuousOn.congr ?_ hgen
    exact ((hEc.mul hCc).const_smul (-(Complex.I) : ℂ))
  have hDderivc : ContinuousOn (invFamilyDeriv C C₁) (uIcc a b) :=
    continuousOn_invFamilyDeriv_of_unit hC hu hC₁c
  have hPderivc : ContinuousOn (invFamilyProductDeriv C C₁ C₂) (uIcc a b) :=
    continuousOn_invFamilyProductDeriv_of_unit hC hu hC₁c hC₂c
  have hQc : ContinuousOn (invFamilyProduct2 C C₁ C₂) (uIcc a b) :=
    continuousOn_invFamilyProduct2_of_unit hC hu hC₁c hC₂c
  have hQderivc : ContinuousOn (invFamilyProduct2Deriv C C₁ C₂ C₃) (uIcc a b) :=
    continuousOn_invFamilyProduct2Deriv_of_unit hC hu hC₁c hC₂c hC₃
  have hQderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (invFamilyProduct2 C C₁ C₂) (invFamilyProduct2Deriv C C₁ C₂ C₃ t) t :=
    fun t ht => hasDerivAt_invFamilyProduct2 (hC t ht) (hu t ht) (hC₁ t ht) (hC₂ t ht)
  have hrel₃ : ∀ t ∈ uIcc a b, E t * invFamilyProductDeriv C C₁ C₂ t
      = (Complex.I : ℂ) • (Eder t * invFamilyProduct2 C C₁ C₂ t) := by
    intro t ht
    have := phase_rel_of_generator (hgen t ht) (hu t ht) (invFamilyProductDeriv C C₁ C₂)
    rw [invFamilyProduct2]
    exact this
  have hstep₃ := phase_ibp_step (G := invFamilyProductDeriv C C₁ C₂) hE hQderiv
    hEderc.intervalIntegrable hQderivc.intervalIntegrable
    (hEderc.mul hQc).intervalIntegrable (hEc.mul hQderivc).intervalIntegrable hrel₃
  rw [h2, hstep₃]
  simp only [smul_sub]
  abel

end GaloisForLFunctions.HTGeometry
