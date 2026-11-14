import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationSums
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationParity
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Linarith

/-!
# Pole orders of monic integer polynomials

At a rational pole, the leading term of a monic integer polynomial has
strictly smaller valuation than every lower term. Its value is therefore
nonzero and has valuation equal to the degree times the argument's
valuation. No splitting or separability assumption is needed.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- Integer polynomials preserve local integrality. -/
theorem integerPolynomial_eval_integral (f : ℤ[X]) {x : ℚ}
    (hx : 0 ≤ padicValRat p x) :
    0 ≤ padicValRat p (f.eval₂ (Int.castRingHom ℚ) x) := by
  rw [eval₂_eq_sum_range]
  apply val_finset_sum_nonneg
  intro i _
  change 0 ≤ padicValRat p ((f.coeff i : ℚ) * x ^ i)
  by_cases ht : (f.coeff i : ℚ) * x ^ i = 0
  · simp only [ht, padicValRat.zero, le_refl]
  · obtain ⟨hc, hxp⟩ := mul_ne_zero_iff.mp ht
    rw [padicValRat.mul hc hxp, padicValRat.of_int, padicValRat.pow]
    exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hx)

/-- At a pole, every lower-degree monomial is at least one valuation
step above the leading monomial of degree `n`. -/
theorem integer_monomial_above_leading (a : ℤ) {x : ℚ} {i n : ℕ}
    (hx : padicValRat p x < 0) (hi : i < n) :
    (a : ℚ) * x ^ i = 0 ∨
      (n : ℤ) * padicValRat p x + 1 ≤ padicValRat p ((a : ℚ) * x ^ i) := by
  by_cases ht : (a : ℚ) * x ^ i = 0
  · exact Or.inl ht
  right
  obtain ⟨ha, hxp⟩ := mul_ne_zero_iff.mp ht
  rw [padicValRat.mul ha hxp, padicValRat.of_int, padicValRat.pow]
  have ha0 : (0 : ℤ) ≤ padicValInt p a := Nat.cast_nonneg _
  have hgap : (0 : ℤ) ≤ (n : ℤ) - i - 1 := by omega
  have hmul := mul_nonneg hgap (neg_nonneg.mpr hx.le)
  nlinarith only [hmul, ha0, hx]

/-- Exact pole order and nonvanishing for every monic integer polynomial. -/
theorem monic_integerPolynomial_eval_of_neg (f : ℤ[X]) (hf : f.Monic) {x : ℚ}
    (hx : padicValRat p x < 0) :
    f.eval₂ (Int.castRingHom ℚ) x ≠ 0 ∧
      padicValRat p (f.eval₂ (Int.castRingHom ℚ) x) =
        (f.natDegree : ℤ) * padicValRat p x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let lower := ∑ i ∈ Finset.range f.natDegree, (f.coeff i : ℚ) * x ^ i
  have heq : f.eval₂ (Int.castRingHom ℚ) x = lower + x ^ f.natDegree := by
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul]
    rfl
  have hlead := pow_ne_zero f.natDegree hx0
  by_cases hlower : lower = 0
  · rw [heq, hlower, zero_add]
    exact ⟨hlead, padicValRat.pow x⟩
  · have hbound : (f.natDegree : ℤ) * padicValRat p x + 1 ≤ padicValRat p lower :=
      val_finset_sum_ge (Finset.range f.natDegree) _ _ (fun i hi =>
        integer_monomial_above_leading (f.coeff i) hx (Finset.mem_range.mp hi)) hlower
    have hne : padicValRat p lower ≠ padicValRat p (x ^ f.natDegree) := by
      rw [padicValRat.pow]
      omega
    have hsum := add_ne_zero_of_val_ne hne
    rw [heq]
    refine ⟨hsum, ?_⟩
    rw [padicValRat.add_eq_min hsum hlower hlead hne, padicValRat.pow,
      min_eq_right (by omega)]

/-- Positive-degree monic integer polynomials detect integrality exactly. -/
theorem monic_integerPolynomial_integral_iff (f : ℤ[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) (x : ℚ) :
    0 ≤ padicValRat p (f.eval₂ (Int.castRingHom ℚ) x) ↔ 0 ≤ padicValRat p x := by
  constructor
  · intro h
    by_contra hx
    have hv := (monic_integerPolynomial_eval_of_neg f hf (lt_of_not_ge hx)).2
    have hn : (0 : ℤ) < f.natDegree := by exact_mod_cast hdeg
    have hneg := mul_neg_of_pos_of_neg hn (lt_of_not_ge hx)
    rw [hv] at h
    exact (not_le_of_gt hneg) h
  · exact integerPolynomial_eval_integral f

#print axioms monic_integerPolynomial_eval_of_neg
#print axioms monic_integerPolynomial_integral_iff

end GaloisForLFunctions.HTGeometry.Arithmetic
