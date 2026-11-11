import Mathlib

/-!
# A common prime of two columns gives a Jacobi sum

When two columns share a prime modulus and carry the same character `χ` there, the local factor
of their correlation is the sum of `χ(x) \bar χ(y)` over the line `a x − b y = k` of the residue
field.

* At a nonzero frequency `k` it is the Jacobi sum of `χ` and `χ⁻¹` after a change of variable:
  `∑_x χ(x) χ⁻¹((a x − k)/b) = −χ(b/a)` for nontrivial `χ` (`sum_mulChar_mul_inv_line`). Its
  modulus is one: a shared prime with a nonprincipal local character contributes no growth at the
  frequencies prime to it.
* At the frequency `k = 0` the line passes through the origin and the sum is
  `(card F − 1) χ(b/a)` (`sum_mulChar_mul_inv_line_zero`).
-/

open Finset

namespace GaloisForLFunctions.FamilyContinuationTheory

variable {F : Type*} [Field F] [Fintype F]

/-- The sum of `χ(s) χ⁻¹(s − 1)` over a finite field is `−1` for a nontrivial character. -/
theorem sum_mulChar_mul_inv_sub_one {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    ∑ s : F, χ s * χ⁻¹ (s - 1) = -1 := by
  have hJ := jacobiSum_nontrivial_inv hχ
  unfold jacobiSum at hJ
  have hneg : ∀ s : F, χ⁻¹ (s - 1) = χ⁻¹ (-1) * χ⁻¹ (1 - s) := fun s => by
    rw [← map_mul]
    congr 1
    ring
  have hterm : ∀ s : F, χ s * χ⁻¹ (s - 1) = χ⁻¹ (-1) * (χ s * χ⁻¹ (1 - s)) := fun s => by
    rw [hneg s]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hJ, MulChar.inv_apply' χ, inv_neg, inv_one]
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_mul_neg, mul_one, map_one]
  linear_combination -hsq

/-- **A common prime at a nonzero frequency.** For a nontrivial character `χ` of a finite field
and `a, b, k ≠ 0`, the sum of `χ(x) χ⁻¹(y)` over the line `a x − b y = k` is `−χ(b/a)`. -/
theorem sum_mulChar_mul_inv_line {χ : MulChar F ℂ} (hχ : χ ≠ 1) {a b k : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (hk : k ≠ 0) :
    ∑ x : F, χ x * χ⁻¹ ((a * x - k) / b) = -χ (b / a) := by
  have hka : k / a ≠ 0 := div_ne_zero hk ha
  -- substitute `x = (k/a) s`
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ (k / a) hka)]
  have hterm : ∀ s : F, χ ((Equiv.mulLeft₀ (k / a) hka) s) *
      χ⁻¹ ((a * (Equiv.mulLeft₀ (k / a) hka) s - k) / b) =
      χ (b / a) * (χ s * χ⁻¹ (s - 1)) := by
    intro s
    have h1 : (Equiv.mulLeft₀ (k / a) hka) s = k / a * s := rfl
    have h2 : (a * (k / a * s) - k) / b = k / b * (s - 1) := by
      field_simp
    rw [h1, h2, map_mul, map_mul, MulChar.inv_apply' χ (k / b)]
    have h3 : χ (k / a) * χ ((k / b)⁻¹) = χ (b / a) := by
      rw [← map_mul]
      congr 1
      field_simp
    linear_combination (χ s * χ⁻¹ (s - 1)) * h3
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_mulChar_mul_inv_sub_one hχ]
  ring

/-- **A common prime at the zero frequency.** The line through the origin gives
`(card F − 1) χ(b/a)`. -/
theorem sum_mulChar_mul_inv_line_zero (χ : MulChar F ℂ) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ x : F, χ x * χ⁻¹ ((a * x - 0) / b) = ((Fintype.card F : ℂ) - 1) * χ (b / a) := by
  classical
  have hterm : ∀ x : F, χ x * χ⁻¹ ((a * x - 0) / b) = if x = 0 then 0 else χ (b / a) := by
    intro x
    split_ifs with hx
    · rw [hx, MulChar.map_zero, zero_mul]
    · rw [sub_zero, MulChar.inv_apply' χ, ← map_mul]
      congr 1
      field_simp
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hcard : (Finset.univ.filter fun x : F => ¬x = 0).card = Fintype.card F - 1 := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.filter_eq' Finset.univ (0 : F)]
    simp
  rw [hcard, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

end GaloisForLFunctions.FamilyContinuationTheory
