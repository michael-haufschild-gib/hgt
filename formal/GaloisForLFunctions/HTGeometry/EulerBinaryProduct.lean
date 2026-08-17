import Mathlib

/-!
# Euler's binary product and the dyadic digit factorization

Every natural number has a unique binary expansion, and the corresponding factorization of the
geometric series is the identity

`(1 - q) * ∏_{j < J} (1 + q ^ 2 ^ j) = 1 - q ^ 2 ^ J`,

whose limit for `|q| < 1` is Euler's `∏_{j ≥ 0} (1 + q ^ 2 ^ j) = (1 - q)⁻¹`.

Dividing the monomial of a binary word by these factors turns the geometric law with ratio `q` into
the product of independent Bernoulli digits: the finite form is
`∏_{j < J} q ^ (2 ^ j ε j) / (1 + q ^ 2 ^ j) = q ^ (∑ 2 ^ j ε j) (1 - q) / (1 - q ^ 2 ^ J)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {R : Type*} [CommRing R]

/-- **The telescoping binary product.** -/
theorem one_sub_mul_prod_one_add_pow (q : R) (J : ℕ) :
    (1 - q) * ∏ j ∈ Finset.range J, (1 + q ^ 2 ^ j) = 1 - q ^ 2 ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih]
      have hpow : q ^ 2 ^ (J + 1) = q ^ 2 ^ J * q ^ 2 ^ J := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      ring

/-- **Euler's binary product.** -/
theorem tendsto_prod_one_add_pow {q : ℝ} (hq : |q| < 1) :
    Filter.Tendsto (fun J => ∏ j ∈ Finset.range J, (1 + q ^ 2 ^ j)) Filter.atTop
      (nhds ((1 - q)⁻¹)) := by
  have hq1 : (1 : ℝ) - q ≠ 0 := by
    rcases abs_lt.mp hq with ⟨h1, h2⟩
    linarith
  have hpow : Filter.Tendsto (fun J : ℕ => q ^ 2 ^ J) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun J : ℕ => (2 : ℕ) ^ J) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).comp h1
  have heq : ∀ J : ℕ, ∏ j ∈ Finset.range J, (1 + q ^ 2 ^ j) = (1 - q ^ 2 ^ J) / (1 - q) := by
    intro J
    rw [eq_div_iff hq1, mul_comm]
    exact one_sub_mul_prod_one_add_pow q J
  simp only [heq]
  have : Filter.Tendsto (fun J : ℕ => (1 - q ^ 2 ^ J) / (1 - q)) Filter.atTop
      (nhds ((1 - 0) / (1 - q))) :=
    (tendsto_const_nhds.sub hpow).div_const _
  simpa using this

/-- **The dyadic digit factorization of the geometric law, finite form.** -/
theorem prod_digit_div (q : R) (ε : ℕ → ℕ) (J : ℕ) :
    (∏ j ∈ Finset.range J, (1 + q ^ 2 ^ j)) * (q ^ ∑ j ∈ Finset.range J, 2 ^ j * ε j)
      * (1 - q)
      = (1 - q ^ 2 ^ J) * ∏ j ∈ Finset.range J, q ^ (2 ^ j * ε j) := by
  have hprod : ∏ j ∈ Finset.range J, q ^ (2 ^ j * ε j)
      = q ^ ∑ j ∈ Finset.range J, 2 ^ j * ε j := by
    rw [← Finset.prod_pow_eq_pow_sum]
  rw [hprod, ← one_sub_mul_prod_one_add_pow q J]
  ring

/-- The digit factorization in the form used for probabilities: over a field, the product of the
digit weights of a binary word is the geometric weight of the number it represents. -/
theorem prod_digit_div_field {K : Type*} [Field K] {q : K} (hq : q ≠ 1)
    (hden : ∀ j : ℕ, (1 + q ^ 2 ^ j) ≠ 0) (ε : ℕ → ℕ) (J : ℕ) :
    ∏ j ∈ Finset.range J, (q ^ (2 ^ j * ε j) / (1 + q ^ 2 ^ j))
      = q ^ (∑ j ∈ Finset.range J, 2 ^ j * ε j) * (1 - q) / (1 - q ^ 2 ^ J) := by
  have h1 : (1 : K) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hJ : (1 : K) - q ^ 2 ^ J ≠ 0 := by
    rw [← one_sub_mul_prod_one_add_pow q J]
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.mpr fun j _ => hden j)
  rw [Finset.prod_div_distrib, ← Finset.prod_pow_eq_pow_sum]
  rw [div_eq_div_iff (Finset.prod_ne_zero_iff.mpr fun j _ => hden j) hJ]
  rw [← one_sub_mul_prod_one_add_pow q J]
  ring

end GaloisForLFunctions.HTGeometry
