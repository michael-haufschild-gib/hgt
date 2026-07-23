import GaloisForLFunctions.HTGeometry.GammaPoleScaleSeparatedAffineHorizon
import GaloisForLFunctions.HTGeometry.GammaPoleWeightedSecondSubprincipalCofinal

/-!
# Gamma affine/second-subprincipal exclusion universality

The actual factorially scaled Gamma profile detects affine source polynomials exactly.  Affine
sources have neither the first-jet nor the Hessian channel required by a nonzero complete
second-subprincipal boundary.  Hence second-subprincipal survival forces genuine nonlinear pole
profile and all cofinal exact-order realizations lie strictly beyond the affine horizon.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

noncomputable section

/-- An actual Gamma profile inside the affine simple-pole horizon has both intrinsic
second-subprincipal channels equal to zero. -/
theorem gammaPole_secondSubprincipalChannels_eq_zero_of_affineProfile
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hprofile : (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1) :
    gammaPolePrincipalReflectionSymbol (n + 1)
        (MvPolynomial.pderiv (1 : Fin (n + 2)) P) = 0 ∧
      gammaPolePrincipalReflectionSymbol (n + 1)
        (MvPolynomial.pderiv (0 : Fin (n + 2))
          (MvPolynomial.pderiv (0 : Fin (n + 2)) P)) = 0 := by
  obtain ⟨a, b, rfl⟩ :=
    (gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine P).1 hprofile
  simp

/-- A cancelled first partial and affine actual profile force the complete second-subprincipal
boundary symbol to vanish. -/
theorem gammaPoleSecondSubprincipalBoundarySymbol_eq_zero_of_affineProfile
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hprofile : (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1)
    (hpartial : gammaPolePrincipalReflectionSymbol (n + 1)
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) = 0) :
    gammaPoleSecondSubprincipalBoundarySymbol n P = 0 := by
  have hchannels := gammaPole_secondSubprincipalChannels_eq_zero_of_affineProfile
    n P hprofile
  by_contra hboundary
  exact (gammaPoleSecondSubprincipalBoundarySymbol_ne_zero_iff_channels
    n P hpartial).1 hboundary |>.elim
      (fun hfirst => hfirst hchannels.1)
      (fun hhessian => hhessian hchannels.2)

/-- **Affine-horizon exclusion law.**  Every nonzero complete second-subprincipal boundary with
cancelled first partial forces actual Gamma pole-profile degree at least two. -/
theorem two_le_gammaScaleSeparatedSimplePoleProfileEval_natDegree_of_secondSubprincipal
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hpartial : gammaPolePrincipalReflectionSymbol (n + 1)
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) = 0)
    (hboundary : gammaPoleSecondSubprincipalBoundarySymbol n P ≠ 0) :
    2 ≤ (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree := by
  by_contra hdegree
  have hprofile :
      (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ≤ 1 := by
    omega
  exact hboundary
    (gammaPoleSecondSubprincipalBoundarySymbol_eq_zero_of_affineProfile
      n P hprofile hpartial)

/-- **Cofinal nonlinear second-subprincipal law.**  Intrinsic channel survival simultaneously
forces nonlinear actual pole profile and realizes the exact second-subprincipal order on an
arbitrarily remote common covariant/native Gamma branch. -/
theorem exists_cofinal_gammaPoleSecondSubprincipal_nonlinearProfile_exactOrder
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 2)) W)
    (hW : 2 ≤ W)
    (hcancel : gammaPolePrincipalReflectionSymbol (n + 1) P = 0)
    (hpartial : gammaPolePrincipalReflectionSymbol (n + 1)
      (MvPolynomial.pderiv (0 : Fin (n + 2)) P) = 0)
    (hchannels :
      gammaPolePrincipalReflectionSymbol (n + 1)
          (MvPolynomial.pderiv (1 : Fin (n + 2)) P) ≠ 0 ∨
        gammaPolePrincipalReflectionSymbol (n + 1)
          (MvPolynomial.pderiv (0 : Fin (n + 2))
            (MvPolynomial.pderiv (0 : Fin (n + 2)) P)) ≠ 0)
    (B : ℕ) :
    2 ≤ (gammaScaleSeparatedSimplePoleProfileEval (n + 1) P).natDegree ∧
      ∃ branch : ℕ, B ≤ branch ∧
        meromorphicOrderAt (gammaPoleWeightedJetEval branch (n + 1) P) 0 =
          ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ∧
        meromorphicOrderAt (gammaAffineWeightedJetEval branch (n + 1) P) 0 =
          ((-((W - 2 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hboundary : gammaPoleSecondSubprincipalBoundarySymbol n P ≠ 0 :=
    (gammaPoleSecondSubprincipalBoundarySymbol_ne_zero_iff_channels
      n P hpartial).2 hchannels
  exact ⟨two_le_gammaScaleSeparatedSimplePoleProfileEval_natDegree_of_secondSubprincipal
      n P hpartial hboundary,
    exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_secondSubprincipal_channels
      n P hP hW hcancel hpartial hchannels B⟩

end

end GaloisForLFunctions.HTGeometry
