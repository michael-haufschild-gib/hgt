import GaloisForLFunctions.HTGeometry.DifferentialPolynomial
import Mathlib.Tactic

/-!
# Logarithmic-current transport for toric tails

The character lattice of an algebraic torus is Laurent-monomial.  This file formalizes the
source-pure differential identity behind the toric stable tail: logarithmic current converts every
Laurent monomial into the corresponding integral linear combination.  Thus an isogeny acts on the
surviving log-cotangent frame by its character-lattice matrix.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The logarithmic current of a nonzero torus character. -/
def toricLogCurrent {K : Type*} [Field K] [Differential K] (x : K) : K := x′ / x

/-- Logarithmic current turns multiplication of nonzero characters into addition. -/
theorem toricLogCurrent_mul
    {K : Type*} [Field K] [Differential K]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    toricLogCurrent (x * y) = toricLogCurrent x + toricLogCurrent y := by
  simp only [toricLogCurrent, Derivation.leibniz, smul_eq_mul]
  field_simp [hx, hy]
  ring

/-- A Laurent power transports logarithmic current by its integral exponent. -/
theorem toricLogCurrent_zpow
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (n : ℤ) (hx : x ≠ 0) :
    toricLogCurrent (x ^ n) = (n : K) * toricLogCurrent x := by
  have hpow : x ^ (n - 1) * x = x ^ n := by
    calc
      x ^ (n - 1) * x = x ^ (n - 1) * x ^ (1 : ℤ) := by rw [zpow_one]
      _ = x ^ ((n - 1) + 1) := (zpow_add₀ hx _ _).symm
      _ = x ^ n := by congr 1; omega
  simp only [toricLogCurrent, Derivation.leibniz_zpow, zsmul_eq_mul, smul_eq_mul]
  field_simp [hx]
  calc
    (n : K) * x ^ (n - 1) * x′ * x = (n : K) * (x ^ (n - 1) * x) * x′ := by ring
    _ = (n : K) * x ^ n * x′ := by rw [hpow]
    _ = (n : K) * x′ * x ^ n := by ring

/-- The logarithmic-current row of a Laurent monomial is its character-lattice exponent row. -/
theorem toricLogCurrent_laurentMonomial
    {ι K : Type*} [DecidableEq ι] [Field K] [CharZero K] [Differential K]
    (s : Finset ι) (x : ι → K) (a : ι → ℤ) (hx : ∀ i ∈ s, x i ≠ 0) :
    toricLogCurrent (∏ i ∈ s, x i ^ a i) =
      ∑ i ∈ s, (a i : K) * toricLogCurrent (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toricLogCurrent]
  | @insert i s hi ih =>
      have hxi : x i ≠ 0 := hx i (Finset.mem_insert_self i s)
      have hxs : ∀ j ∈ s, x j ≠ 0 := fun j hj => hx j (Finset.mem_insert_of_mem hj)
      have hprod : ∏ j ∈ s, x j ^ a j ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j hj => zpow_ne_zero _ (hxs j hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        toricLogCurrent_mul _ _ (zpow_ne_zero _ hxi) hprod,
        toricLogCurrent_zpow _ _ hxi, ih hxs]

end


end GaloisForLFunctions
