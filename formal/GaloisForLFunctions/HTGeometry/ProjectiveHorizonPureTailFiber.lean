import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import Mathlib.Data.Fintype.Powerset
import Mathlib.FieldTheory.Separable

/-!
# The pure critical projective-horizon fiber

At the pure critical observation, the only prescribed tail terms are `X^m` and `X^n`.  The
truncated inverse constraint then closes to the exact cyclic factorization

`(A + X^m) (B + X^n) = 1 + X^(m+n)`.

This file formalizes that equivalence, separability of the cyclic polynomial in characteristic
zero, and the exact binomial cardinality of its exterior/occupation labels.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The low part of the product at the pure `(m,n)` critical observation. -/
noncomputable def pureCriticalLowProduct {K : Type*} [CommRing K]
    (m n : ℕ) (A B : K[X]) : K[X] :=
  A * B + A * X ^ n + X ^ m * B

/-- The complete pure critical factors. -/
noncomputable def pureCriticalLeftFactor {K : Type*} [CommRing K]
    (m : ℕ) (A : K[X]) : K[X] :=
  A + X ^ m

noncomputable def pureCriticalRightFactor {K : Type*} [CommRing K]
    (n : ℕ) (B : K[X]) : K[X] :=
  B + X ^ n

/-- The static cyclic polynomial selected by the pure critical observation. -/
noncomputable def pureCriticalCyclicPolynomial {K : Type*} [CommRing K]
    (L : ℕ) : K[X] :=
  1 + X ^ L

/-- Exact algebraic closure of the truncated pure-tail compatibility equation. -/
theorem pureCritical_factorization_iff {K : Type*} [CommRing K]
    (m n : ℕ) (A B : K[X]) :
    pureCriticalLowProduct m n A B = 1 ↔
      pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
        pureCriticalCyclicPolynomial (K := K) (m + n) := by
  simp only [pureCriticalLowProduct, pureCriticalLeftFactor, pureCriticalRightFactor,
    pureCriticalCyclicPolynomial]
  constructor <;> intro h
  · calc
      (A + X ^ m) * (B + X ^ n) =
          (A * B + A * X ^ n + X ^ m * B) + X ^ (m + n) := by
            rw [pow_add]
            ring
      _ = 1 + X ^ (m + n) := by rw [h]
  · have hexpand :
        (A + X ^ m) * (B + X ^ n) =
          (A * B + A * X ^ n + X ^ m * B) + X ^ (m + n) := by
        rw [pow_add]
        ring
    rw [hexpand] at h
    exact add_right_cancel h

/-- In characteristic zero the cyclic polynomial has no repeated root. -/
theorem pureCriticalCyclicPolynomial_separable {K : Type*} [Field K] [CharZero K]
    {L : ℕ} (hL : 0 < L) :
    (pureCriticalCyclicPolynomial (K := K) L).Separable := by
  have hcast : (L : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hsep := (Polynomial.separable_X_pow_sub_C (-1 : K) hcast (by simp) :
    (X ^ L - C (-1 : K)).Separable)
  have heq : (X ^ L - C (-1 : K) : K[X]) =
      pureCriticalCyclicPolynomial (K := K) L := by
    simp [pureCriticalCyclicPolynomial, sub_eq_add_neg, add_comm]
  rw [heq] at hsep
  exact hsep

/-- Occupation labels for the pure critical fiber: choose `m` modes out of `m+n`. -/
def criticalHorizonOccupationStates (m n : ℕ) :=
  {S : Finset (Fin (m + n)) // S.card = m}

instance (m n : ℕ) : Fintype (criticalHorizonOccupationStates m n) := by
  unfold criticalHorizonOccupationStates
  infer_instance

/-- The occupation-state space has exactly the critical binomial multiplicity. -/
theorem card_criticalHorizonOccupationStates (m n : ℕ) :
    Fintype.card (criticalHorizonOccupationStates m n) =
      criticalHorizonMultiplicity m n := by
  change Fintype.card {S : Finset (Fin (m + n)) // S.card = m} = (m + n).choose m
  rw [Fintype.card_finset_len]
  simp

end GaloisForLFunctions.HTGeometry
