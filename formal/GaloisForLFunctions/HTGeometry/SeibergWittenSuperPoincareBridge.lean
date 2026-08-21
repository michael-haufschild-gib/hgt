import GaloisForLFunctions.HTGeometry.SuperPoincareSpinor
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Finite Seiberg--Witten invariant as Weyl supermomentum

The corpus already defines four-dimensional Weyl supermomentum as the Hermitian outer square of a
two-component spinor.  That is definitionally the finite Seiberg--Witten invariant.  This module
therefore transports the supertranslation self-bracket, future-null property, and common-phase
invariance to the finite Seiberg--Witten invariant and its gauge flows.

This is an exact pointwise algebraic identification.  It neither introduces a supersymmetric
Seiberg--Witten PDE nor identifies the finite matrix carrier with continuum supergravity data.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The finite Seiberg--Witten curvature invariant is exactly the Weyl supermomentum matrix. -/
theorem seibergWittenInvariant_eq_weylSuperMomentum (psi : SeibergWittenSpinor) :
    seibergWittenInvariant psi = weylSuperMomentum psi := rfl

/-- The diagonal Weyl supertranslation bracket is twice the finite Seiberg--Witten invariant. -/
theorem weylSuperTranslationBracket_self_eq_seibergWittenInvariant
    (psi : SeibergWittenSpinor) :
    weylSuperTranslationBracket psi psi = (2 : ℂ) • seibergWittenInvariant psi := by
  simpa [seibergWittenInvariant_eq_weylSuperMomentum] using
    weylSuperTranslationBracket_self psi

/-- The finite invariant obeys the inherited future-null Lorentz-coordinate relation. -/
theorem seibergWittenInvariant_future_null (psi : SeibergWittenSpinor) :
    0 ≤ higgsSpinorTime psi ∧
      higgsSpinorTime psi ^ 2 - higgsSpinorX psi ^ 2 - higgsSpinorY psi ^ 2 -
        higgsSpinorZ psi ^ 2 = 0 :=
  weylSuperMomentum_future_null psi

/-- Weyl supermomentum is invariant under the finite Seiberg--Witten phase gauge action. -/
theorem weylSuperMomentum_gaugeInvariant (u : Circle) (psi : SeibergWittenSpinor) :
    weylSuperMomentum (u • psi) = weylSuperMomentum psi := by
  change seibergWittenInvariant (u • psi) = seibergWittenInvariant psi
  exact seibergWittenInvariant_gaugeInvariant u psi

/-- Weyl supermomentum is constant along every finite Seiberg--Witten gauge flow. -/
theorem seibergWittenGaugeFlow_superMomentumInvariant
    (phase : ℝ → Circle) (t : ℝ) (psi : SeibergWittenSpinor) :
    weylSuperMomentum (seibergWittenGaugeFlow phase psi t) = weylSuperMomentum psi := by
  change seibergWittenInvariant (seibergWittenGaugeFlow phase psi t) =
    seibergWittenInvariant psi
  exact seibergWittenGaugeFlow_invariant phase t psi

end GaloisForLFunctions.HTGeometry
