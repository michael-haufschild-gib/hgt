import GaloisForLFunctions.HTGeometry.SeparableSplitDivisorCount
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPostcriticalRigidity

/-!
# The pure critical fibre counts the occupation states

The pure critical polynomial is monic, separable and splits over an algebraically closed field, so
the general count of the monic divisors of a separable split polynomial applies to it: its monic
divisors of a prescribed degree are as many as the occupation states of the pure critical fibre.

No intersection theory enters: the count of the fibre is the count of subsets of a root set.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

omit [CharZero K] [IsAlgClosed K] in
/-- The pure critical polynomial is monic. -/
theorem pureCriticalCyclicPolynomial_monic {L : ℕ} (hL : 0 < L) :
    (pureCriticalCyclicPolynomial (K := K) L).Monic := by
  have h : pureCriticalCyclicPolynomial (K := K) L = X ^ L + C 1 := by
    rw [pureCriticalCyclicPolynomial, map_one, add_comm]
  rw [h]
  exact monic_X_pow_add_C 1 hL.ne'

omit [CharZero K] [IsAlgClosed K] in
/-- The pure critical polynomial has degree the horizon length. -/
theorem pureCriticalCyclicPolynomial_natDegree (L : ℕ) :
    (pureCriticalCyclicPolynomial (K := K) L).natDegree = L := by
  have h : pureCriticalCyclicPolynomial (K := K) L = X ^ L + C 1 := by
    rw [pureCriticalCyclicPolynomial, map_one, add_comm]
  rw [h]
  exact natDegree_X_pow_add_C

/-- **The pure critical polynomial is the product of its distinct linear factors.** -/
theorem pureCriticalCyclicPolynomial_eq_prod [DecidableEq K] {L : ℕ} (hL : 0 < L) :
    pureCriticalCyclicPolynomial (K := K) L
      = ∏ r ∈ (pureCriticalCyclicPolynomial (K := K) L).roots.toFinset, (X - C r) :=
  eq_prod_roots_toFinset (pureCriticalCyclicPolynomial_monic hL)
    (pureCriticalCyclicPolynomial_separable hL) (IsAlgClosed.splits _)

/-- The root set of the pure critical polynomial has the horizon length. -/
theorem card_roots_toFinset_pureCritical [DecidableEq K] {L : ℕ} (hL : 0 < L) :
    ((pureCriticalCyclicPolynomial (K := K) L).roots.toFinset : Finset K).card = L := by
  rw [card_roots_toFinset (pureCriticalCyclicPolynomial_separable hL) (IsAlgClosed.splits _),
    pureCriticalCyclicPolynomial_natDegree L]

/-! ## The count -/

/-- **The monic divisors of a prescribed degree of the pure critical polynomial number exactly the
critical binomial multiplicity.** -/
theorem nat_card_monic_divisors_pureCritical [DecidableEq K] {m n : ℕ} (hL : 0 < m + n) :
    Nat.card {A : K[X] //
        A.Monic ∧ A ∣ pureCriticalCyclicPolynomial (K := K) (m + n) ∧ A.natDegree = m}
      = criticalHorizonMultiplicity m n := by
  rw [nat_card_monic_divisors (pureCriticalCyclicPolynomial_monic hL)
      (pureCriticalCyclicPolynomial_separable hL) (IsAlgClosed.splits _) m,
    pureCriticalCyclicPolynomial_natDegree (m + n)]
  rfl

/-- **The same, matched against the occupation states.** -/
theorem nat_card_monic_divisors_pureCritical_eq_states [DecidableEq K] {m n : ℕ}
    (hL : 0 < m + n) :
    Nat.card {A : K[X] //
        A.Monic ∧ A ∣ pureCriticalCyclicPolynomial (K := K) (m + n) ∧ A.natDegree = m}
      = Fintype.card (criticalHorizonOccupationStates m n) := by
  rw [nat_card_monic_divisors_pureCritical hL, card_criticalHorizonOccupationStates]

end GaloisForLFunctions.HTGeometry
