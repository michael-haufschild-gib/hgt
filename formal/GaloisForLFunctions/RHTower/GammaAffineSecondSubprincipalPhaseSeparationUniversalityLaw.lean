import GaloisForLFunctions.HTGeometry.GammaPoleAffineSecondSubprincipalExclusionUniversalityLaw
import GaloisForLFunctions.RHTower.GammaScaleSeparatedAffineOrderEnergyUniversalityLaw

/-!
# Gamma affine/second-subprincipal phase separation

For one actual scale-separated Gamma source, the affine simple-pole order--energy phase and the
nonlinear second-subprincipal phase are disjoint.  The former kills the complete boundary symbol;
the latter forces degree at least two and exact order on arbitrarily remote native and covariant
branches.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions

noncomputable section

/-- Moving-pole order--energy phase attached to the constant extension of a complex Gamma source. -/
def GammaScaleSeparatedAffineOrderEnergyPhase
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ) : Prop :=
  GammaPoleProfileAtMostSimple n (constantMovingGammaSource P) ∧
    ∀ branch : ℕ,
      meromorphicOrderAt
          (fun x : ℂ => gammaPolyJetEval (n + 1)
            (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)
            (constantMovingGammaSource P)) 0 =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ¬ ∃ C : ℝ, ∀ m : ℕ,
          (∫ t : ℝ, ‖RHTower.boundaryPoleApproachProfile 0
            (((MvPolynomial.pderiv (0 : Fin (n + 1))
              (constantMovingGammaSource P)).coeff 0).eval
                (-(branch : ℂ))) m t‖ ^ (2 : ℕ)) ≤ C

/-- Joint native/covariant exact second-subprincipal phase on arbitrarily remote branches. -/
def GammaSecondSubprincipalCofinalPhase
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (W : ℕ) : Prop :=
  ∀ B : ℕ, ∃ branch : ℕ, B ≤ branch ∧
    meromorphicOrderAt (gammaPoleWeightedJetEval branch (n + 1) P) 0 =
      ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ∧
    meromorphicOrderAt (gammaAffineWeightedJetEval branch (n + 1) P) 0 =
      ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ)

/-- Complete separation certificate for the two Gamma profile phases. -/
structure GammaAffineSecondSubprincipalPhaseSeparationUniversalCertificate
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (W : ℕ) : Prop where
  affineForcesBoundaryZero :
    (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 →
      gammaPoleSecondSubprincipalBoundarySymbol n P = 0
  affineForcesOrderEnergy :
    (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 →
      GammaScaleSeparatedAffineOrderEnergyPhase P
  secondSubprincipalForcesNonlinearCofinal :
    gammaPoleSecondSubprincipalBoundarySymbol n P ≠ 0 →
      2 ≤ (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ∧
        GammaSecondSubprincipalCofinalPhase n P W
  phasesDisjoint :
    ¬ ((gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 ∧
      gammaPoleSecondSubprincipalBoundarySymbol n P ≠ 0)

/-- **Gamma affine/second-subprincipal phase-separation law.**  A weighted source with cancelled
principal and first-partial channels lies in a simple-pole order--energy phase whenever its actual
profile is affine.  Any surviving complete second-subprincipal boundary instead forces nonlinear
profile and cofinal exact order on both Gamma realizations; the phases cannot overlap. -/
theorem gammaAffineSecondSubprincipal_phaseSeparationUniversalCertificate
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : gammaPolePrincipalReflectionSymbol (n + 1) P = 0)
    (hpartial : gammaPolePrincipalReflectionSymbol (n + 1)
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) = 0) :
    GammaAffineSecondSubprincipalPhaseSeparationUniversalCertificate n P W := by
  refine {
    affineForcesBoundaryZero := fun hscale =>
      gammaPoleSecondSubprincipalBoundarySymbol_eq_zero_of_affineProfile
        n P hscale hpartial
    affineForcesOrderEnergy := fun hscale =>
      gammaScaleSeparatedAffineHorizon_orderEnergyUniversality P hscale
    secondSubprincipalForcesNonlinearCofinal := ?_
    phasesDisjoint := ?_ }
  · intro hboundary
    have hchannels :=
      (gammaPoleSecondSubprincipalBoundarySymbol_ne_zero_iff_channels
        n P hpartial).1 hboundary
    have hcofinal := exists_cofinal_gammaPoleSecondSubprincipal_nonlinearProfile_exactOrder
      n P hP hW hcancel hpartial hchannels
    exact ⟨
      two_le_gammaScaleSeparatedSimplePoleProfileEval_natDegree_of_secondSubprincipal
        n P hpartial hboundary,
      fun B => (hcofinal B).2⟩
  · rintro ⟨hscale, hboundary⟩
    exact hboundary
      (gammaPoleSecondSubprincipalBoundarySymbol_eq_zero_of_affineProfile
        n P hscale hpartial)

end

end GaloisForLFunctions
