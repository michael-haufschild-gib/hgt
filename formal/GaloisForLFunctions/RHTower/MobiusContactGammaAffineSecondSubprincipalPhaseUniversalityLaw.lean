import GaloisForLFunctions.RHTower.GammaAffineSecondSubprincipalPhaseSeparationUniversalityLaw
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma affine/second-subprincipal phase universality

The finite Möbius contact-charge defect is the exact moving-pole coordinate of Gamma's affine
order--energy phase. For weighted sources with cancelled principal and first-partial channels, an
affine actual profile therefore enters a contact-normalized simple-pole phase. A surviving complete
second-subprincipal boundary instead forces nonlinear profile degree and cofinal exact order on
both native and covariant Gamma branches. The two phases cannot overlap.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Moving-pole affine order--energy phase written directly in the finite Möbius contact
coordinate. -/
def GammaMobiusContactAffineOrderEnergyPhase
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) : Prop :=
  GammaPoleProfileAtMostSimple n (constantMovingGammaSource P) ∧
    ∀ branch : ℕ,
      meromorphicOrderAt
          (fun x : ℂ => gammaPolyJetEval (n + 1)
            (-(branch : ℂ) +
              ((-2 - mobiusGammaContactPartialCharge branch) / 2) * x)
            (constantMovingGammaSource P)) 0 =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ¬ ∃ C : ℝ, ∀ m : ℕ,
          (∫ t : ℝ, ‖_root_.RHTower.boundaryPoleApproachProfile 0
            (((MvPolynomial.pderiv (0 : Fin (n + 1))
              (constantMovingGammaSource P)).coeff 0).eval
                (-(branch : ℂ))) m t‖ ^ (2 : ℕ)) ≤ C

/-- Contact-coordinate and reciprocal-factorial presentations of the affine phase are exactly
equivalent. -/
theorem gammaMobiusContactAffineOrderEnergyPhase_iff
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) :
    GammaMobiusContactAffineOrderEnergyPhase P ↔
      GaloisForLFunctions.GammaScaleSeparatedAffineOrderEnergyPhase P := by
  simp only [GammaMobiusContactAffineOrderEnergyPhase,
    GaloisForLFunctions.GammaScaleSeparatedAffineOrderEnergyPhase,
    mobiusContactGammaFactorialScale_eq]

/-- Complete contact-coordinate certificate separating affine and nonlinear Gamma pole-profile
phases. -/
structure GammaMobiusContactAffineSecondSubprincipalPhaseSeparationCertificate
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (W : ℕ) : Prop where
  contactAffineForcesBoundaryZero :
    (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 →
      gammaPoleSecondSubprincipalBoundarySymbol n P = 0
  contactAffineForcesOrderEnergy :
    (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 →
      GammaMobiusContactAffineOrderEnergyPhase P
  secondSubprincipalForcesNonlinearCofinal :
    gammaPoleSecondSubprincipalBoundarySymbol n P ≠ 0 →
      2 ≤ (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ∧
        GaloisForLFunctions.GammaSecondSubprincipalCofinalPhase n P W
  phasesDisjoint :
    ¬ ((gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 ∧
      gammaPoleSecondSubprincipalBoundarySymbol n P ≠ 0)

/-- **Möbius-contact Gamma affine/second-subprincipal phase universality law.** Arithmetic contact
charge is the affine moving-pole coordinate, while every surviving second-subprincipal boundary
forces the disjoint nonlinear cofinal-order phase. -/
theorem gammaMobiusContactAffineSecondSubprincipal_phaseSeparationUniversality
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : gammaPolePrincipalReflectionSymbol (n + 1) P = 0)
    (hpartial : gammaPolePrincipalReflectionSymbol (n + 1)
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) = 0) :
    GammaMobiusContactAffineSecondSubprincipalPhaseSeparationCertificate n P W := by
  have hcert :=
    GaloisForLFunctions.gammaAffineSecondSubprincipal_phaseSeparationUniversalCertificate
      n P hP hW hcancel hpartial
  exact {
    contactAffineForcesBoundaryZero := hcert.affineForcesBoundaryZero
    contactAffineForcesOrderEnergy := fun hscale =>
      (gammaMobiusContactAffineOrderEnergyPhase_iff P).2
        (hcert.affineForcesOrderEnergy hscale)
    secondSubprincipalForcesNonlinearCofinal :=
      hcert.secondSubprincipalForcesNonlinearCofinal
    phasesDisjoint := hcert.phasesDisjoint }

end

end GaloisForLFunctions.RHTower
