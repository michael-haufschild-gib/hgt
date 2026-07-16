import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolUniversalShiftField
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolGammaInfiniteRank

/-!
# Universal realization of the projective Gamma horizon

The reciprocal-Gamma poles `g_n = (1,-n)` determine the countable central arrangement with
characters `λ_m(a,b)=b+ma`.  The universal shift field realizes this entire arrangement as its
exact selected-derivation dependence spectrum.  Each Gamma pole law lies on exactly one component.

Together with the finite-rank Gamma obstruction, this gives a constructive alternative: the Gamma
horizon cannot be represented by a regular coefficient-flat finite-rank linear principal layer,
while it does have an unconditional infinite-rank rational differential-field realization.  The
universal realization is generally curved in the cumulative-symbol sense.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- The projective character whose kernel contains the `m`-th homogeneous Gamma pole law. -/
def gammaProjectiveCharacter (m : ℕ) : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun A := A.2 + (m : ℂ) * A.1
  map_add' A B := by
    simp
    ring
  map_smul' c A := by
    simp
    ring

/-- Evaluation of the `m`-th Gamma character on the `n`-th pole law. -/
theorem gammaProjectiveCharacter_gammaPoleLaw (m n : ℕ) :
    gammaProjectiveCharacter m (gammaPoleLaw n) = (m : ℂ) - (n : ℂ) := by
  simp [gammaProjectiveCharacter, gammaPoleLaw]
  ring

/-- Distinct Gamma pole rays lie on distinct components of the projective arrangement. -/
theorem gammaProjectiveCharacter_gammaPoleLaw_eq_zero_iff (m n : ℕ) :
    gammaProjectiveCharacter m (gammaPoleLaw n) = 0 ↔ m = n := by
  rw [gammaProjectiveCharacter_gammaPoleLaw, sub_eq_zero]
  exact Nat.cast_inj

/-- The countable central arrangement obtained by homogenizing all reciprocal-Gamma poles. -/
def gammaProjectiveHorizon : Set (ℂ × ℂ) :=
  {A | ∃ m : ℕ, gammaProjectiveCharacter m A = 0}

/-- Every homogeneous reciprocal-Gamma pole law lies on the projective Gamma horizon. -/
theorem gammaPoleLaw_mem_gammaProjectiveHorizon (n : ℕ) :
    gammaPoleLaw n ∈ gammaProjectiveHorizon := by
  exact ⟨n, (gammaProjectiveCharacter_gammaPoleLaw_eq_zero_iff n n).2 rfl⟩

/-- A component of the Gamma arrangement contains precisely its matching pole law. -/
theorem gammaProjectiveCharacter_vanishes_on_gammaPoleLaw_iff (m n : ℕ) :
    gammaProjectiveCharacter m (gammaPoleLaw n) = 0 ↔ m = n :=
  gammaProjectiveCharacter_gammaPoleLaw_eq_zero_iff m n

/-- **Countable Gamma-horizon realization.**  A concrete infinite-rank rational differential
field has the complete projective Gamma arrangement as its exact selected-law dependence
spectrum.  No existence hypothesis is used. -/
theorem universalGammaShift_completeDependenceSpectrum_eq_gammaProjectiveHorizon :
    {A | ¬ AlgebraicIndependent ℂ
        (fun p : ℕ × ℕ ↦
          selectedDerivationJet
              (universalWeightedShiftDerivation gammaProjectiveCharacter A) p.2
            (universalShiftAncestor (K := ℂ) 0 p.1))} =
      gammaProjectiveHorizon := by
  exact universalShift_completeDependenceSpectrum_eq_hyperplaneArrangement
    gammaProjectiveCharacter

/-- Pointwise form: outside the projective Gamma horizon, all universal Gamma-sector jets are
algebraically independent; on the horizon, at least one sector freezes. -/
theorem universalGammaShift_completeJet_algebraicIndependent_iff (A : ℂ × ℂ) :
    AlgebraicIndependent ℂ
        (fun p : ℕ × ℕ ↦
          selectedDerivationJet
              (universalWeightedShiftDerivation gammaProjectiveCharacter A) p.2
            (universalShiftAncestor (K := ℂ) 0 p.1)) ↔
      A ∉ gammaProjectiveHorizon := by
  rw [universalShift_completeJet_algebraicIndependent_iff]
  simp [gammaProjectiveHorizon]

end

end GaloisForLFunctions.HTGeometry
