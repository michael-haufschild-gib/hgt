import GaloisForLFunctions.HTGeometry.SeparableSplitDivisorCount
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPureTailFiber

/-!
# The fibre over a monomial-tail observation

For an arbitrary pair of observed tails the truncated compatibility equation closes to an exact
factorization whose target is determined by the observation alone: the low part of the product is one
exactly when the two completed factors multiply to `1 + U V`.

When the two tails are monomials the target is `1 + c X^L` up to a unit, which is separable in
characteristic zero, so the fibre is counted by the same binomial coefficient as at the pure critical
observation.  The pure observation is the case of both scalars equal to one; the count is constant on
the whole monomial-tail family.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## The compatibility equation for an arbitrary observation -/

/-- The low part of the product for observed tails `U` and `V`. -/
noncomputable def criticalLowProduct {K : Type*} [CommRing K] (U V A B : K[X]) : K[X] :=
  A * B + A * V + U * B

/-- **The truncated compatibility equation closes to an exact factorization**, with target
determined by the observed tails alone. -/
theorem criticalLowProduct_factorization_iff {K : Type*} [CommRing K] (U V A B : K[X]) :
    criticalLowProduct U V A B = 1 ↔ (A + U) * (B + V) = 1 + U * V := by
  simp only [criticalLowProduct]
  constructor <;> intro h
  · calc (A + U) * (B + V) = (A * B + A * V + U * B) + U * V := by ring
      _ = 1 + U * V := by rw [h]
  · have hexpand : (A + U) * (B + V) = (A * B + A * V + U * B) + U * V := by ring
    rw [hexpand] at h
    exact add_right_cancel h

/-- The pure critical observation is the case of monomial tails. -/
theorem criticalLowProduct_pure {K : Type*} [CommRing K] (m n : ℕ) (A B : K[X]) :
    criticalLowProduct (X ^ m) (X ^ n) A B = pureCriticalLowProduct m n A B := rfl

/-! ## The truncation is vacuous exactly at the critical degrees -/

/-- A product with one factor below a degree and the other at most a degree stays below the sum. -/
theorem degree_mul_lt_of_lt_of_le {K : Type*} [CommRing K] {p q : K[X]} {i j : ℕ}
    (hp : p.degree < (i : ℕ)) (hq : q.degree ≤ (j : ℕ)) :
    (p * q).degree < ((i + j : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hi : p.natDegree < i := by
    rw [Polynomial.degree_eq_natDegree hp0] at hp
    exact_mod_cast hp
  have hj : q.natDegree ≤ j := by
    rw [Polynomial.degree_eq_natDegree hq0] at hq
    exact_mod_cast hq
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, ← Nat.cast_add]
  exact_mod_cast (by omega : p.natDegree + q.natDegree < i + j)

/-- **The low product has degree below the horizon** when the observed tails have exactly the
critical degrees.  So for such an observation nothing is lost by truncating. -/
theorem degree_criticalLowProduct_lt {K : Type*} [CommRing K] {m n : ℕ} {U V A B : K[X]}
    (hA : A.degree < (m : ℕ)) (hB : B.degree < (n : ℕ)) (hU : U.degree ≤ (m : ℕ))
    (hV : V.degree ≤ (n : ℕ)) :
    (criticalLowProduct U V A B).degree < ((m + n : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact degree_mul_lt_of_lt_of_le hA hB.le
    · exact degree_mul_lt_of_lt_of_le hA hV
  · rw [mul_comm U B, show m + n = n + m from Nat.add_comm m n]
    exact degree_mul_lt_of_lt_of_le hB hU

/-- **A polynomial of degree below the horizon is one exactly when it is one to that order.**  This
is what makes the truncated compatibility equation equivalent to the exact one. -/
theorem dvd_sub_one_iff_eq_one {K : Type*} [CommRing K] [IsDomain K] {L : ℕ} {p : K[X]}
    (hdeg : (p - 1).degree < (L : ℕ)) :
    (X : K[X]) ^ L ∣ (p - 1) ↔ p = 1 := by
  constructor
  · intro hdvd
    by_cases h0 : p - 1 = 0
    · exact sub_eq_zero.1 h0
    · exfalso
      have hle := Polynomial.degree_le_of_dvd hdvd h0
      rw [Polynomial.degree_X_pow] at hle
      exact absurd (lt_of_le_of_lt hle hdeg) (lt_irrefl _)
  · intro h
    rw [h, sub_self]
    exact dvd_zero _

/-! ## The count for a radical target -/

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The monic divisors of a prescribed degree of `X ^ L - C a` are counted by a binomial
coefficient**, for every nonzero `a`. -/
theorem nat_card_monic_divisors_X_pow_sub_C {L : ℕ} (hL : 0 < L) {a : K} (ha : a ≠ 0) (m : ℕ) :
    Nat.card {A : K[X] // A.Monic ∧ A ∣ (X ^ L - C a) ∧ A.natDegree = m} = L.choose m := by
  classical
  have hcast : (L : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hmonic : (X ^ L - C a : K[X]).Monic := monic_X_pow_sub_C a hL.ne'
  have hsep : (X ^ L - C a : K[X]).Separable := Polynomial.separable_X_pow_sub_C a hcast ha
  have h := nat_card_monic_divisors hmonic hsep (IsAlgClosed.splits _) m
  rwa [natDegree_X_pow_sub_C] at h

/-- **The fibre over a monomial-tail observation.**  With tails `c X ^ m` and `d X ^ n` the target of
the factorization is `1 + c d X ^ (m + n)`, whose monic divisors of degree `m` number the critical
binomial multiplicity. -/
theorem nat_card_monic_divisors_monomialTail {m n : ℕ} (hL : 0 < m + n) {c d : K} (hc : c ≠ 0)
    (hd : d ≠ 0) :
    Nat.card {A : K[X] //
        A.Monic ∧ A ∣ (1 + C (c * d) * X ^ (m + n)) ∧ A.natDegree = m}
      = criticalHorizonMultiplicity m n := by
  classical
  have hcd : c * d ≠ 0 := mul_ne_zero hc hd
  have hassoc : (1 + C (c * d) * X ^ (m + n) : K[X])
      = C (c * d) * (X ^ (m + n) - C (-(c * d)⁻¹)) := by
    rw [mul_sub, ← C_mul, show c * d * -(c * d)⁻¹ = -1 from by field_simp, map_neg, map_one]
    ring
  have hdvd : ∀ A : K[X], A ∣ (1 + C (c * d) * X ^ (m + n))
      ↔ A ∣ (X ^ (m + n) - C (-(c * d)⁻¹)) := by
    intro A
    rw [hassoc]
    exact (isUnit_C.2 hcd.isUnit).dvd_mul_left
  have hcongr : Nat.card {A : K[X] //
      A.Monic ∧ A ∣ (1 + C (c * d) * X ^ (m + n)) ∧ A.natDegree = m}
      = Nat.card {A : K[X] //
        A.Monic ∧ A ∣ (X ^ (m + n) - C (-(c * d)⁻¹)) ∧ A.natDegree = m} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun A => by rw [hdvd A])
  rw [hcongr, nat_card_monic_divisors_X_pow_sub_C hL (neg_ne_zero.2 (inv_ne_zero hcd)) m]
  rfl

end GaloisForLFunctions.HTGeometry
