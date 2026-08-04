import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Monomial families and the logarithmic derivative of a torus

An integer matrix acts on a family of nonzero elements of a differential field by monomial
substitution: the `i`-th new coordinate is the product of the old ones raised to the entries of the
`i`-th row.  This is the coordinate form of an isogeny of the split torus `G_m ^ r`, and composing
substitutions multiplies the matrices.

On logarithmic derivatives the action linearizes exactly: the velocity of a monomial family is the
matrix applied to the velocity of the original family.  This is the rank-`r` form of the
Maurer--Cartan transport law, with `d a` the integer matrix itself.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

/-- The logarithmic derivative of an integer power. -/
theorem logDeriv_zpow {R : Type*} [Field R] [Differential R] (a : R) (ha : a ≠ 0) (n : ℤ) :
    Differential.logDeriv (a ^ n) = (n : R) * Differential.logDeriv a := by
  have hinv : ∀ b : R, b ≠ 0 → Differential.logDeriv b⁻¹ = -Differential.logDeriv b := by
    intro b hb
    have h := Differential.logDeriv_div 1 b one_ne_zero hb
    rw [one_div, Differential.logDeriv_one, zero_sub] at h
    exact h
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Differential.logDeriv_pow]
    norm_cast
  · rw [zpow_negSucc, hinv _ (pow_ne_zero _ ha), Differential.logDeriv_pow]
    push_cast
    ring

theorem zpow_sum_of_ne_zero {E : Type*} [Field E] {x : E} (hx : x ≠ 0) {ι : Type*}
    (s : Finset ι) (e : ι → ℤ) :
    x ^ (∑ j ∈ s, e j) = ∏ j ∈ s, x ^ e j := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

variable {E : Type*} [Field E]

/-- The monomial substitution of a family by an integer matrix. -/
def monomialFamily {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → E) : Fin r → E :=
  fun i ↦ ∏ j, x j ^ M i j

theorem monomialFamily_apply {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → E) (i : Fin r) :
    monomialFamily M x i = ∏ j, x j ^ M i j := rfl

theorem monomialFamily_ne_zero {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) {x : Fin r → E}
    (hx : ∀ j, x j ≠ 0) (i : Fin r) : monomialFamily M x i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hx j)

@[simp] theorem monomialFamily_one {r : ℕ} (x : Fin r → E) :
    monomialFamily (1 : Matrix (Fin r) (Fin r) ℤ) x = x := by
  funext i
  rw [monomialFamily_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    rw [Matrix.one_apply_ne (Ne.symm hji), zpow_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Monomial substitutions compose by matrix multiplication.** -/
theorem monomialFamily_mul {r : ℕ} (M N : Matrix (Fin r) (Fin r) ℤ) {x : Fin r → E}
    (hx : ∀ j, x j ≠ 0) :
    monomialFamily (M * N) x = monomialFamily M (monomialFamily N x) := by
  funext i
  rw [monomialFamily_apply, monomialFamily_apply]
  calc ∏ k, x k ^ (M * N) i k
      = ∏ k, ∏ j, x k ^ (M i j * N j k) := by
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        rw [Matrix.mul_apply, zpow_sum_of_ne_zero (hx k)]
    _ = ∏ j, ∏ k, x k ^ (M i j * N j k) := Finset.prod_comm
    _ = ∏ j, monomialFamily N x j ^ M i j := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        calc ∏ k, x k ^ (M i j * N j k)
            = ∏ k, (x k ^ N j k) ^ M i j := by
              refine Finset.prod_congr rfl fun k _ ↦ ?_
              rw [← zpow_mul, mul_comm]
          _ = (∏ k, x k ^ N j k) ^ M i j :=
              (map_prod (zpowGroupHom (M i j) : E →* E) _ Finset.univ).symm
          _ = monomialFamily N x j ^ M i j := by rw [monomialFamily_apply]

/-- **The velocity of a monomial family is the matrix applied to the velocity.** -/
theorem logDeriv_monomialFamily [Differential E] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    {x : Fin r → E} (hx : ∀ j, x j ≠ 0) (i : Fin r) :
    Differential.logDeriv (monomialFamily M x i)
      = ∑ j, (M i j : E) * Differential.logDeriv (x j) := by
  rw [monomialFamily_apply,
    Differential.logDeriv_prod _ Finset.univ _ (fun j _ ↦ zpow_ne_zero _ (hx j))]
  exact Finset.sum_congr rfl fun j _ ↦ logDeriv_zpow (x j) (hx j) (M i j)

end

end GaloisForLFunctions.HTGeometry
