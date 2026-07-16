import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDerivationLawHorizon
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolHyperplaneHorizon

/-!
# Finite holography of the varying-derivation dependence spectrum

The determinant horizon is now eliminated from the statement.  For a regular coefficient-flat
finite-rank principal law whose first symbol is linear, the actual differential-algebraic
dependence locus of a finite observable family is exactly a finite union of kernels of supported
joint characters.  There are at most as many such characters as states in the principal fiber.

This is the general finite holography theorem: every law-direction dependence transition is
recorded by a finite boundary character, and no additional differential-algebraic phase can be
hidden at higher jet order.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {k K L h ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k L] [Algebra K L] [IsAlgClosed K]
  [AddCommGroup h] [Module K h] [Fintype ι] [DecidableEq ι]

/-- **General finite holography theorem.**  Under an explicit principal lower law, regularity,
coefficient flatness, and linear dependence of the first principal symbol on law space, the full
varying-derivation differential-dependence spectrum is exactly a finite central hyperplane
arrangement.  Its supported character type has cardinality at most the principal fiber rank. -/
theorem derivationLawDependentSet_eq_finiteHyperplaneHorizon
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K (fun p : ℕ × ι ↦ source p.1 p.2))
    (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol 0 A = S A) :
    letI := normalizedPrincipalJointCharacterFintype symbol hflat e he 0
    (∀ A : h,
      A ∈ derivationLawDependentSet (K := K) law observable ↔
        ∃ χ : { χ : h → K //
            normalizedPrincipalJointMaxGenEigenspace symbol e 0 χ ≠ ⊥ },
          coefficientNormalizedPrincipalJointCharacterLinearMap
            symbol hflat e he 0 S hS χ.1 χ.2 A = 0) ∧
      Fintype.card { χ : h → K //
          normalizedPrincipalJointMaxGenEigenspace symbol e 0 χ ≠ ⊥ } ≤
        Fintype.card ι := by
  letI := normalizedPrincipalJointCharacterFintype symbol hflat e he 0
  have hspectrum :
      derivationLawDependentSet (K := K) law observable =
        matrixSymbolSingularSet symbol 0 :=
    derivationLawDependentSet_eq_firstSingularSet_of_coefficientFlat
      source observable law symbol hflat e he hlaw hsource
  have hhorizon := regularFlatLinearPrincipalSymbol_hyperplaneHorizon
    symbol hflat e he 0 S hS
  constructor
  · intro A
    rw [hspectrum]
    exact hhorizon.1 A
  · exact hhorizon.2

/-- A law is in the regular hypertranscendental phase exactly when every supported boundary
character is nonzero there. -/
theorem derivationIndependentOver_iff_all_supportedCharacters_ne_zero
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K (fun p : ℕ × ι ↦ source p.1 p.2))
    (S : h →ₗ[K] Matrix ι ι K)
    (hS : ∀ A, symbol 0 A = S A)
    (A : h) :
    letI := normalizedPrincipalJointCharacterFintype symbol hflat e he 0
    DerivationIndependentOver K (law A) observable ↔
      ∀ χ : { χ : h → K //
          normalizedPrincipalJointMaxGenEigenspace symbol e 0 χ ≠ ⊥ },
        coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he 0 S hS χ.1 χ.2 A ≠ 0 := by
  classical
  letI := normalizedPrincipalJointCharacterFintype symbol hflat e he 0
  have hholography :=
    (derivationLawDependentSet_eq_finiteHyperplaneHorizon
      source observable law symbol hflat e he hlaw hsource S hS).1 A
  rw [show DerivationIndependentOver K (law A) observable ↔
      ¬ A ∈ derivationLawDependentSet (K := K) law observable by
    simp [derivationLawDependentSet]]
  rw [hholography]
  push Not
  rfl

end

end GaloisForLFunctions.HTGeometry
