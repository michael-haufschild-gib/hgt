import GaloisForLFunctions.HTGeometry.PureFibreCardinality
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Data.Set.PowersetCard

/-!
# The pure critical fibre is the exterior occupation basis

The occupation labels of the pure critical horizon fibre are the `m`-element subsets of the `L`
modes, which is exactly the standard index set of the basis of the `m`-th exterior power of the
`L`-dimensional mode space.  So the fibre itself indexes a basis of `⋀^m K^L`: the occupation
states of `m` indistinguishable fermions in `L` simple modes.

Exchanging the two horizons is complementation of the occupied set — particle–hole conjugation.

This records the exterior-state dictionary of the pure-tail fibre card as Lean statements.  No
dynamics is asserted: the identification is of state *labels*, coming from the static polynomial
constraint.

## Main results

* `occupationStateEquivPowersetCard` — occupation states are the exterior basis index;
* `occupationComplement` — horizon exchange is particle–hole complementation, an involution;
* `pureFibreExteriorBasis` — a basis of `⋀^m K^L` indexed by the pure critical fibre;
* `finrank_exteriorPower_eq_choose` — its rank is the fibre count `C(L, m)`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Occupation states are literally the standard index set of the `m`-th exterior power basis. -/
def occupationStateEquivPowersetCard (m n : ℕ) :
    criticalHorizonOccupationStates m n ≃ Set.powersetCard (Fin (m + n)) m where
  toFun S := ⟨S.1, by simp⟩
  invFun s := ⟨s.1, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Horizon exchange is particle–hole complementation.**  Complementing the occupied set of modes
exchanges the two horizon roles. -/
def occupationComplement (m n : ℕ) :
    criticalHorizonOccupationStates m n ≃ {S : Finset (Fin (m + n)) // S.card = n} where
  toFun S := ⟨S.1ᶜ, by
    rw [Finset.card_compl, S.2, Fintype.card_fin]
    omega⟩
  invFun S := ⟨S.1ᶜ, by
    rw [Finset.card_compl, S.2, Fintype.card_fin]
    omega⟩
  left_inv S := by
    refine Subtype.ext ?_
    simp
  right_inv S := by
    refine Subtype.ext ?_
    simp

@[simp]
theorem coe_occupationComplement (m n : ℕ) (S : criticalHorizonOccupationStates m n) :
    (occupationComplement m n S).1 = S.1ᶜ := rfl

/-- Complementation is an involution: complementing twice returns the occupied set. -/
theorem occupationComplement_involutive (m n : ℕ)
    (S : criticalHorizonOccupationStates m n) :
    ((occupationComplement m n S).1)ᶜ = S.1 := by
  simp

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- The pure critical fibre is the standard index set of the `m`-th exterior power basis. -/
def pureFibreEquivPowersetCard (hL : 0 < m + n) :
    Set.powersetCard (Fin (m + n)) m ≃ pureCriticalFibre K m n :=
  (occupationStateEquivPowersetCard m n).symm.trans
    (Equiv.ofBijective _ (occupationToFibre_bijective (K := K) hL))

/-- **The exterior occupation basis.**  The `m`-th exterior power of the `L`-dimensional mode space
carries a basis indexed by the pure critical fibre itself: the occupation states of `m`
indistinguishable fermions in `L` simple modes. -/
def pureFibreExteriorBasis (hL : 0 < m + n) :
    Module.Basis (pureCriticalFibre K m n) K (⋀[K]^m (Fin (m + n) → K)) :=
  ((Pi.basisFun K (Fin (m + n))).exteriorPower m).reindex (pureFibreEquivPowersetCard hL)

/-- **The exterior power has the critical binomial multiplicity as its rank.** -/
theorem finrank_exteriorPower_eq_choose (hL : 0 < m + n) :
    Module.finrank K (⋀[K]^m (Fin (m + n) → K)) = (m + n).choose m := by
  classical
  letI : Fintype (pureCriticalFibre K m n) :=
    Fintype.ofEquiv _ (pureFibreEquivPowersetCard (K := K) hL)
  rw [Module.finrank_eq_card_basis (pureFibreExteriorBasis (K := K) hL)]
  rw [Fintype.card_congr (pureFibreEquivPowersetCard (K := K) hL).symm]
  rw [Fintype.card_congr (occupationStateEquivPowersetCard (m := m) (n := n)).symm]
  rw [card_criticalHorizonOccupationStates, criticalHorizonMultiplicity]

end GaloisForLFunctions.HTGeometry
