import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerInvariantEvaluationGaugeFrontier
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPointwiseXiComparisonSharpness

/-!
# One fixed source criterion for the positive Meyer frontier

There is one compactly supported literal Meyer source whose Mellin transform
is nonzero at every actual Xi divisor point.  Its algebraic cohomology class
therefore simultaneously witnesses every nonzero zeroth-jet eigenfunctional.

This file proves that RH is equivalent to boundedness of the centered
evaluation orbit of this one fixed class at every actual divisor point.  No
zero-dependent source selection, full divisor packet, spectral synthesis,
completion, or Hodge norm occurs.  The open analytic problem is consequently
one explicit uniform-orbit estimate for one source object.
-/

open Complex

namespace RHTower

noncomputable section

/-- Cohomology class of the fixed compact Meyer source avoiding every actual Xi zero. -/
def deningerMeyerXiAvoidingCohomologyClass :
    DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk deningerMeyerXiAvoidingSource

/-- Every actual zeroth Xi evaluation is nonzero on the same fixed Meyer class. -/
theorem deningerMeyerXiAvoidingCohomologyClass_evaluation_ne_zero
    (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        deningerMeyerXiAvoidingCohomologyClass ≠ 0 := by
  rw [deningerMeyerXiAvoidingCohomologyClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  simpa [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using
      deningerMeyerXiAvoidingSource_nonzero_on_support rho

/-- A single nonvanishing exponential evaluation orbit bounded for all real
flow times has purely imaginary exponent. -/
theorem re_eq_zero_of_bounded_eigenfunctional_orbit
    {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (V : ℝ → X →ₗ[ℂ] X) (E : X →ₗ[ℂ] ℂ)
    (u : X) (hu : E u ≠ 0) (z : ℂ)
    (heigen : ∀ c : ℝ,
      E (V c u) = Complex.exp ((c : ℂ) * z) * E u)
    (hbounded : ∃ C : ℝ, ∀ c : ℝ, ‖E (V c u)‖ ≤ C) :
    z.re = 0 := by
  obtain ⟨C, hbound⟩ := hbounded
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbound 0)
  let A : ℝ := ‖E u‖
  have hA : 0 < A := norm_pos_iff.mpr hu
  by_contra hz
  let T : ℝ := C / A + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let c : ℝ := Real.log T / z.re
  have hcre : c * z.re = Real.log T := by
    dsimp [c]
    field_simp
  have hre : (((c : ℝ) : ℂ) * z).re = Real.log T := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact hcre
  have h := hbound c
  rw [heigen c, norm_mul, Complex.norm_exp,
    hre, Real.exp_log hT] at h
  change T * A ≤ C at h
  have hTA : T * A = C + A := by
    dsimp [T]
    rw [add_mul, div_mul_cancel₀ C hA.ne']
    ring
  rw [hTA] at h
  linarith

/-- Concrete fixed-source orbit bound left by the updated positive-completion frontier. -/
def DeningerMeyerXiAvoidingCenteredOrbitBounded : Prop :=
  ∀ rho : XiDivisorSupport,
    ∃ C : ℝ, ∀ c : ℝ,
      ‖deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerStrongLogCenteredCohomologyFlow c
          deningerMeyerXiAvoidingCohomologyClass)‖ ≤ C

/-- **Fixed-source positive frontier.** The centered evaluation orbit of one
explicit compact Meyer class is bounded at every actual Xi point exactly when
RH holds. -/
theorem deningerMeyerXiAvoidingCenteredOrbitBounded_iff_riemannHypothesis :
    DeningerMeyerXiAvoidingCenteredOrbitBounded ↔ RiemannHypothesis := by
  constructor
  · intro hbounded
    rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
    intro rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    have hz := re_eq_zero_of_bounded_eigenfunctional_orbit
      deningerMeyerStrongLogCenteredCohomologyFlow
      (deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho))
      deningerMeyerXiAvoidingCohomologyClass
      (deningerMeyerXiAvoidingCohomologyClass_evaluation_ne_zero rho)
      ((rho : ℂ) - 1 / 2)
      (deningerMeyerXiSupportEvaluationLM_centeredFlow rho ·
        deningerMeyerXiAvoidingCohomologyClass)
      (hbounded rho)
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
    linarith
  · intro hRH rho
    have hre : (rho : ℂ).re = 1 / 2 := by
      have hfracture :=
        (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) rho
      exact
        (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
          (rho : ℂ)).mp hfracture
    let E := deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho)
    refine ⟨‖E deningerMeyerXiAvoidingCohomologyClass‖, ?_⟩
    intro c
    rw [deningerMeyerXiSupportEvaluationLM_centeredFlow,
      norm_mul, Complex.norm_exp]
    have hexp : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      rw [hre]
      ring
    rw [hexp, Real.exp_zero, one_mul]

end

end RHTower
