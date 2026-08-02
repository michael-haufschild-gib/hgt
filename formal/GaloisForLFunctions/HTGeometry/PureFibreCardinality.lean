import GaloisForLFunctions.HTGeometry.PureFibreOccupationBijection

/-!
# The pure critical fibre has exactly the binomial multiplicity of points

Packaging the two directions of the identification as a bijection: the occupation states are in
bijection with the monic degree-`m` factors of `1 + t^L`, so the pure critical fibre has exactly
`C(L, m)` points.

This is the count as a statement about the fibre itself rather than about an index set.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (m n : ℕ)

/-- The pure critical fibre: the monic factors of `1 + t^L` of the raw critical degree. -/
def pureCriticalFibre : Type _ :=
  {A : K[X] // A.Monic ∧ A.natDegree = m ∧
    ∃ B, A * B = pureCriticalCyclicPolynomial (K := K) (m + n)}

variable {K m n}

/-- The map from occupation states to the pure critical fibre. -/
noncomputable def occupationToFibre (hL : 0 < m + n)
    (S : criticalHorizonOccupationStates m n) : pureCriticalFibre K m n :=
  ⟨criticalHorizonLeftFactorFromRoots (pureCriticalRootLabeling (K := K) hL) S,
    monic_criticalHorizonLeftFactorFromRoots _ S,
    natDegree_criticalHorizonLeftFactorFromRoots _ S,
    ⟨criticalHorizonRightFactorFromRoots (pureCriticalRootLabeling (K := K) hL) S,
      pureCriticalRootFactors_mul hL S⟩⟩

theorem occupationToFibre_bijective (hL : 0 < m + n) :
    Function.Bijective (occupationToFibre (K := K) (m := m) (n := n) hL) := by
  constructor
  · intro S T hST
    exact criticalHorizonLeftFactorFromRoots_injective (pureCriticalRootLabeling_injective hL)
      (congrArg Subtype.val hST)
  · rintro ⟨A, hA, hAdeg, B, hfac⟩
    obtain ⟨S, hS⟩ := exists_occupationState_of_pureFactorisation hL hA hAdeg hfac
    exact ⟨S, Subtype.ext hS⟩

/-- **The pure critical fibre has exactly the critical binomial multiplicity of points.** -/
theorem card_pureCriticalFibre (hL : 0 < m + n) :
    Nat.card (pureCriticalFibre K m n) = (m + n).choose m := by
  rw [← Nat.card_eq_of_bijective _ (occupationToFibre_bijective (K := K) hL),
    Nat.card_eq_fintype_card, card_criticalHorizonOccupationStates,
    criticalHorizonMultiplicity]

end GaloisForLFunctions.HTGeometry
