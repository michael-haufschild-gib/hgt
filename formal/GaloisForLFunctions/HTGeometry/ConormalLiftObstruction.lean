import GaloisForLFunctions.HTGeometry.LowTangentJacobianKernel

/-!
# The conormal functional obstructs first-order lifting

Let a state carry a low tangent `(U, V)`, so `X^(m+n) ∣ U Y + A V`, and let an observation
deformation `(dP, dQ)` lift to first order, i.e. `X^(m+n) ∣ (da + dP) Y + A (db + dQ)` for some low
`(da, db)`.  Multiplying the lifting relation by `V`, substituting `A V ≡ -U Y` and cancelling the
invertible `Y` gives

```text
X^(m+n) ∣ (V da - U db) + (V dP - U dQ) ,
```

and the first bracket is a sum of products of two low polynomials, so it has no coefficient at
`m + n - 1`.  Reading that coefficient therefore yields

```text
conormal_eq_zero_of_lifts
    ** (U dQ - dP V).coeff (m + n - 1) = 0 **
```

which is exactly the conormal functional of `ConormalTangentDetermination`.  So the conormal of the
tangent annihilates every liftable deformation: it is the first-order equation of the branch.

The two auxiliary facts — cancelling the reciprocal jet from a horizon divisibility, and the
vanishing of the top coefficient of a product of two low polynomials — are proved here as well.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- Cancelling the reciprocal jet from a horizon divisibility. -/
theorem dvd_of_mul_reciprocal {L : ℕ} {A Y Z : F[X]}
    (hInv : (X : F[X]) ^ L ∣ A * Y - 1) (h : (X : F[X]) ^ L ∣ Y * Z) :
    (X : F[X]) ^ L ∣ Z := by
  have hid : Z = A * (Y * Z) - (A * Y - 1) * Z := by ring
  rw [hid]
  exact dvd_sub (Dvd.dvd.mul_left h A) (Dvd.dvd.mul_right hInv Z)

/-- A product of two low polynomials has no coefficient at the top of the horizon. -/
theorem coeff_mul_eq_zero_of_low {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {V da : F[X]}
    (hV : V.degree < (n : ℕ)) (hda : da.degree < (m : ℕ)) :
    (V * da).coeff (m + n - 1) = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m + n - 1 := Finset.mem_antidiagonal.mp hx
  rcases lt_or_ge x.1 n with h1 | h1
  · have hle : m ≤ x.2 := by omega
    rw [Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hda (by exact_mod_cast hle)), mul_zero]
  · rw [Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hV (by exact_mod_cast h1)), zero_mul]

/-- **The conormal functional obstructs lifting.**  If an observation deformation lifts to first
order at a state carrying a low tangent, the conormal functional of that tangent kills it. -/
theorem conormal_eq_zero_of_lifts {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A Y U V dP dQ da db : F[X]}
    (hInv : (X : F[X]) ^ (m + n) ∣ A * Y - 1)
    (htan : (X : F[X]) ^ (m + n) ∣ U * Y + A * V)
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ))
    (hda : da.degree < (m : ℕ)) (hdb : db.degree < (n : ℕ))
    (hlift : (X : F[X]) ^ (m + n) ∣ (da + dP) * Y + A * (db + dQ)) :
    (U * dQ - dP * V).coeff (m + n - 1) = 0 := by
  have hkey : (X : F[X]) ^ (m + n) ∣ Y * (V * (da + dP) - U * (db + dQ)) := by
    have hmul : (X : F[X]) ^ (m + n) ∣ V * ((da + dP) * Y + A * (db + dQ)) :=
      Dvd.dvd.mul_left hlift V
    have hsecond : (X : F[X]) ^ (m + n) ∣ (U * Y + A * V) * (db + dQ) :=
      Dvd.dvd.mul_right htan (db + dQ)
    have hres := dvd_sub hmul hsecond
    have hid : V * ((da + dP) * Y + A * (db + dQ)) - (U * Y + A * V) * (db + dQ)
        = Y * (V * (da + dP) - U * (db + dQ)) := by ring
    rwa [hid] at hres
  have hcancel : (X : F[X]) ^ (m + n) ∣ (V * da - U * db) + (V * dP - U * dQ) := by
    have h := dvd_of_mul_reciprocal hInv hkey
    have hid : V * (da + dP) - U * (db + dQ)
        = (V * da - U * db) + (V * dP - U * dQ) := by ring
    rwa [hid] at h
  have hVda : (V * da).coeff (m + n - 1) = 0 := coeff_mul_eq_zero_of_low hm hn hV hda
  have hUdb : (U * db).coeff (m + n - 1) = 0 := by
    have h := coeff_mul_eq_zero_of_low hn hm hU hdb
    rwa [Nat.add_comm n m] at h
  obtain ⟨t, ht⟩ := hcancel
  have htop : ((V * da - U * db) + (V * dP - U * dQ)).coeff (m + n - 1) = 0 := by
    rw [ht, Polynomial.coeff_X_pow_mul']
    simp only [ite_eq_right_iff]
    intro hle
    omega
  rw [Polynomial.coeff_add, Polynomial.coeff_sub, hVda, hUdb, sub_zero, zero_add,
    Polynomial.coeff_sub] at htop
  rw [Polynomial.coeff_sub, show dP * V = V * dP from by ring]
  linear_combination -htop

end GaloisForLFunctions.HTGeometry
