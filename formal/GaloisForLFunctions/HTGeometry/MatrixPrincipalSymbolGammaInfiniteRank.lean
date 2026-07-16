import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolHyperplaneHorizon
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The reciprocal-Gamma horizon forces curvature or infinite rank

The entire reciprocal Gamma function has zeros at every nonpositive integer.  Homogenize this
one-dimensional boundary sequence as the laws `(1,-m)` in a two-dimensional law space.  A nonzero
linear character can vanish on at most one such law.  The finite hyperplane-collapse theorem then
implies that no regular coefficient-flat finite-rank linear principal-symbol tower can contain the
whole reciprocal-Gamma horizon.

This is an exact obstruction to a finite-state, zero-curvature realization of the simplest natural
hypertranscendental quantum determinant boundary.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The homogeneous law representing the reciprocal-Gamma zero at `-m`. -/
def gammaPoleLaw (m : ℕ) : ℂ × ℂ := (1, -(m : ℂ))

/-- Evaluation of a linear character on the homogeneous Gamma pole laws. -/
theorem linearCharacter_gammaPoleLaw
    (L : (ℂ × ℂ) →ₗ[ℂ] ℂ) (m : ℕ) :
    L (gammaPoleLaw m) = L (1, 0) - (m : ℂ) * L (0, 1) := by
  calc
    L (gammaPoleLaw m) =
        L ((1 : ℂ) • (1, 0) + (-(m : ℂ)) • (0, 1)) := by
      congr 1
      ext <;> simp [gammaPoleLaw]
    _ = (1 : ℂ) * L (1, 0) + (-(m : ℂ)) * L (0, 1) := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
    _ = L (1, 0) - (m : ℂ) * L (0, 1) := by ring

/-- A nonzero linear character meets the homogeneous Gamma pole sequence at most once. -/
theorem eq_of_linearCharacter_gammaPoleLaw_eq_zero
    (L : (ℂ × ℂ) →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    {i j : ℕ} (hi : L (gammaPoleLaw i) = 0)
    (hj : L (gammaPoleLaw j) = 0) :
    i = j := by
  rw [linearCharacter_gammaPoleLaw] at hi hj
  have hb : L (0, 1) ≠ 0 := by
    intro hb
    have ha : L (1, 0) = 0 := by simpa [hb] using hi
    apply hL
    apply LinearMap.ext
    rintro ⟨x, y⟩
    calc
      L (x, y) = L (x • (1, 0) + y • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = x * L (1, 0) + y * L (0, 1) := by
        rw [map_add, map_smul, map_smul]
        simp only [smul_eq_mul]
      _ = 0 := by rw [ha, hb]; simp
  have hi' : L (1, 0) = (i : ℂ) * L (0, 1) := sub_eq_zero.mp hi
  have hj' : L (1, 0) = (j : ℂ) * L (0, 1) := sub_eq_zero.mp hj
  have hcast : (i : ℂ) = (j : ℂ) :=
    mul_right_cancel₀ hb (hi'.symm.trans hj')
  exact Nat.cast_injective hcast

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Gamma infinite-rank obstruction.**  If every homogeneous reciprocal-Gamma pole law is
singular at a linear principal-symbol layer with a regular reference law, then that tower cannot
be coefficient-flat in finite rank. -/
theorem not_matrixCoefficientPrincipalSymbolFlat_of_all_gammaPoleLaw_singular
    (symbol : ℕ → (ℂ × ℂ) → Matrix ι ι ℂ)
    (e : ℂ × ℂ) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : (ℂ × ℂ) →ₗ[ℂ] Matrix ι ι ℂ)
    (hS : ∀ A, symbol n A = S A)
    (hpoles : ∀ m : ℕ, (symbol n (gammaPoleLaw m)).det = 0) :
    ¬ MatrixCoefficientPrincipalSymbolFlat symbol := by
  intro hflat
  have hcapacity := regularFlatLinearPrincipalSymbol_horizonCapacity
    symbol hflat e he n S hS
    (fun i : Fin (Fintype.card ι + 1) ↦ gammaPoleLaw i)
    (fun i ↦ hpoles i)
    (fun χ i j hi hj ↦ by
      apply Fin.ext
      exact eq_of_linearCharacter_gammaPoleLaw_eq_zero
        (coefficientNormalizedPrincipalJointCharacterLinearMap
          symbol hflat e he n S hS χ.1 χ.2)
        (coefficientNormalizedPrincipalJointCharacterLinearMap_ne_zero
          symbol hflat e he n S hS χ.1 χ.2)
        hi hj)
  have : Fintype.card ι + 1 ≤ Fintype.card ι := by
    simpa only [Fintype.card_fin] using hcapacity
  omega

/-- The actual entire reciprocal-Gamma observation on the affine rank coordinate. -/
def reciprocalGammaRankObservation (A : ℂ × ℂ) : ℂ :=
  (Complex.Gamma A.2)⁻¹

/-- **Actual Gamma horizon no-go.**  A linear principal-symbol layer whose determinant zero set is
the reciprocal-Gamma boundary cannot be both finite-rank regular and coefficient-flat. -/
theorem not_matrixCoefficientPrincipalSymbolFlat_of_reciprocalGamma_horizon
    (symbol : ℕ → (ℂ × ℂ) → Matrix ι ι ℂ)
    (e : ℂ × ℂ) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : (ℂ × ℂ) →ₗ[ℂ] Matrix ι ι ℂ)
    (hS : ∀ A, symbol n A = S A)
    (hrealize : ∀ A,
      (symbol n A).det = 0 ↔ reciprocalGammaRankObservation A = 0) :
    ¬ MatrixCoefficientPrincipalSymbolFlat symbol := by
  apply not_matrixCoefficientPrincipalSymbolFlat_of_all_gammaPoleLaw_singular
    symbol e he n S hS
  intro m
  apply (hrealize (gammaPoleLaw m)).2
  simp [reciprocalGammaRankObservation, gammaPoleLaw, Complex.Gamma_neg_nat_eq_zero]

/-! ## A localized quantum-field-theory divisor

For one weight of a two-dimensional `N = (2,2)` chiral multiplet on the sphere, supersymmetric
localization produces the meromorphic one-loop factor `Gamma(z) / Gamma(1 - z)` after restricting
to its effective complex mass coordinate.  The function below is its reciprocal.  The physical
identification is external to Lean; the Gamma-ratio divisor and the obstruction theorem are not.
-/

/-- The reciprocal of the one-weight `S²` chiral-multiplet Gamma ratio on its complex mass slice. -/
def reciprocalS2ChiralOneLoopObservation (A : ℂ × ℂ) : ℂ :=
  Complex.Gamma (1 - A.2) / Complex.Gamma A.2

/-- Every nonpositive integral mass lies on the reciprocal chiral one-loop divisor. -/
theorem reciprocalS2ChiralOneLoopObservation_gammaPoleLaw (m : ℕ) :
    reciprocalS2ChiralOneLoopObservation (gammaPoleLaw m) = 0 := by
  simp [reciprocalS2ChiralOneLoopObservation, gammaPoleLaw,
    Complex.Gamma_neg_nat_eq_zero]

/-- **Localized-QFT horizon no-go.**  If a regular finite-rank linear principal layer contains
the complete negative-integer divisor of the reciprocal `S²` chiral one-loop factor, then its
principal tower has nonzero coefficient curvature.  Equality of zero sets is not required. -/
theorem not_matrixCoefficientPrincipalSymbolFlat_of_reciprocalS2ChiralOneLoop_divisor
    (symbol : ℕ → (ℂ × ℂ) → Matrix ι ι ℂ)
    (e : ℂ × ℂ) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : (ℂ × ℂ) →ₗ[ℂ] Matrix ι ι ℂ)
    (hS : ∀ A, symbol n A = S A)
    (hcontains : ∀ A,
      reciprocalS2ChiralOneLoopObservation A = 0 →
        (symbol n A).det = 0) :
    ¬ MatrixCoefficientPrincipalSymbolFlat symbol := by
  apply not_matrixCoefficientPrincipalSymbolFlat_of_all_gammaPoleLaw_singular
    symbol e he n S hS
  intro m
  exact hcontains (gammaPoleLaw m)
    (reciprocalS2ChiralOneLoopObservation_gammaPoleLaw m)

/-- The localized-QFT divisor forces a nonzero principal curvature tensor somewhere in law space. -/
theorem exists_matrixCoefficientPrincipalCurvature_ne_zero_of_reciprocalS2ChiralOneLoop_divisor
    (symbol : ℕ → (ℂ × ℂ) → Matrix ι ι ℂ)
    (e : ℂ × ℂ) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (S : (ℂ × ℂ) →ₗ[ℂ] Matrix ι ι ℂ)
    (hS : ∀ A, symbol n A = S A)
    (hcontains : ∀ A,
      reciprocalS2ChiralOneLoopObservation A = 0 →
        (symbol n A).det = 0) :
    ∃ m A B, matrixCoefficientPrincipalCurvature symbol m A B ≠ 0 := by
  have hnflat :=
    not_matrixCoefficientPrincipalSymbolFlat_of_reciprocalS2ChiralOneLoop_divisor
      symbol e he n S hS hcontains
  rw [matrixCoefficientPrincipalSymbolFlat_iff_curvature_zero] at hnflat
  push Not at hnflat
  exact hnflat

end

end GaloisForLFunctions.HTGeometry
