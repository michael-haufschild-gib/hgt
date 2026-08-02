import GaloisForLFunctions.RHTower.DeningerMeyerXiSpectralInclusion
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Positive admissible completion frontier for the Meyer Xi spectrum

Literal Meyer cohomology already has one nonzero zeroth-jet eigenfunctional at every actual Xi
divisor point.  A positive completion would solve RH if its centered dual flow were
norm-conservative and retained those eigencharacters.  This file proves that exact last-mile
implication without postulating the completion itself.

The certificate below is deliberately a property of one proposed completed dual action.  It does
not assert that such an action exists.
-/

open Complex

namespace RHTower

noncomputable section

/-- A completed dual action is positively admissible for the actual Xi spectrum when it is
norm-conservative and retains a nonzero copy of every centered Xi character. -/
def DeningerMeyerPositiveAdmissibleDualSpectrum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : E →ₗ[ℂ] E) : Prop :=
  (∀ y : E, ‖V y‖ = ‖y‖) ∧
    ∀ rho : XiDivisorSupport,
      ∃ x : E, x ≠ 0 ∧
        V x =
          centeredComplexModularCharacter (rho : ℂ) (1 : ℂ) • x

/-- A nonzero centered complex eigencharacter in a norm-conservative representation is unitary,
hence its spectral point lies on the critical line. -/
theorem normConservative_centeredXiCharacter_forces_re_half
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : E →ₗ[ℂ] E) (x : E) (hx : x ≠ 0) (rho : ℂ)
    (hconservative : ∀ y : E, ‖V y‖ = ‖y‖)
    (heigen :
      V x = centeredComplexModularCharacter rho (1 : ℂ) • x) :
    rho.re = 1 / 2 := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm := hconservative x
  rw [heigen, norm_smul] at hnorm
  have hunitary :
      ‖centeredComplexModularCharacter rho (1 : ℂ)‖ = 1 := by
    nlinarith
  exact
    (norm_centeredComplexModularCharacter_eq_one_iff
      rho (t := 1) one_ne_zero).mp hunitary

/-- **Exact positive-completion frontier.**  If one norm-conservative completed dual action
retains every actual centered Xi eigencharacter nontrivially, then RH follows. -/
theorem riemannHypothesis_of_deningerMeyerPositiveAdmissibleDualSpectrum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : E →ₗ[ℂ] E)
    (hV : DeningerMeyerPositiveAdmissibleDualSpectrum V) :
    RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  intro rho
  apply
    (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (rho : ℂ)).2
  obtain ⟨x, hx, heigen⟩ := hV.2 rho
  exact
    normConservative_centeredXiCharacter_forces_re_half
      V x hx (rho : ℂ) hV.1 heigen

end

end RHTower

