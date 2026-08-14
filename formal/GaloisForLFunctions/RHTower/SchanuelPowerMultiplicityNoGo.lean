import Mathlib.Algebra.Field.GeomSum

namespace GaloisForLFunctions.RHTower

noncomputable section

open Finset

/-- Cofactor relating a power difference to its underlying first power difference. -/
def powerDifferenceCofactor
    {R : Type*} [CommRing R] (a b : R) (n : ℕ) : R :=
  ∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)

/-- Exact factorization showing that scalar powering cannot create an independent vanishing
equation from one existing equality. -/
theorem pow_sub_pow_eq_sub_mul_powerDifferenceCofactor
    {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    a ^ n - b ^ n = (a - b) * powerDifferenceCofactor a b n := by
  exact ((Commute.all a b).mul_geom_sum₂ n).symm

/-- On the diagonal, the power-difference cofactor specializes to the expected derivative
`n * a^(n-1)`. -/
theorem map_powerDifferenceCofactor_of_eq
    {R K : Type*} [CommRing R] [Field K]
    (phi : R →+* K) (a b : R) (n : ℕ) (hab : phi a = phi b) :
    phi (powerDifferenceCofactor a b n) = (n : K) * (phi a) ^ (n - 1) := by
  simp only [powerDifferenceCofactor, map_sum, map_mul, map_pow, hab]
  exact geom_sum₂_self (phi b) n

/-- At a nonzero diagonal point in characteristic zero, the cofactor is nonzero. Thus, in the
local analytic ring it is a unit and powering preserves the original zero multiplicity. -/
theorem map_powerDifferenceCofactor_ne_zero_of_eq
    {R K : Type*} [CommRing R] [Field K] [CharZero K]
    (phi : R →+* K) (a b : R) (n : ℕ) (hn : 0 < n)
    (hab : phi a = phi b) (ha : phi a ≠ 0) :
    phi (powerDifferenceCofactor a b n) ≠ 0 := by
  rw [map_powerDifferenceCofactor_of_eq phi a b n hab]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (pow_ne_zero _ ha)

end


end GaloisForLFunctions.RHTower

