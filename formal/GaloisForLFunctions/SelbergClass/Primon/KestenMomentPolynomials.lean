import GaloisForLFunctions.SelbergClass.Primon.KestenMomentRecurrence

/-!
# Positive Catalan polynomials for every finite-prime moment

A Catalan renewal recurrence constructs polynomials with natural coefficients.
Their values at `1/p` are exactly the even moments of the prime phase law.
The constant term is Catalan, so the semicircle limit is already visible
inside each finite-prime polynomial.
-/

open Polynomial Finset
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Natural-coefficient moment polynomials defined by a Catalan renewal recurrence. -/
def primonMomentPolynomial : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 => (1 + X) * ∑ i : Fin (n + 1),
      C (catalan i) * primonMomentPolynomial (n - i)
termination_by n => n
decreasing_by omega

@[simp] theorem primonMomentPolynomial_zero : primonMomentPolynomial 0 = 1 := by
  rw [primonMomentPolynomial]

/-- The first-return recurrence preserves natural coefficients at every degree. -/
theorem primonMomentPolynomial_succ (n : ℕ) :
    primonMomentPolynomial (n + 1) = (1 + X) * ∑ i : Fin (n + 1),
      C (catalan i) * primonMomentPolynomial (n - i) := by
  rw [primonMomentPolynomial]

/-- Real evaluation of the natural-coefficient moment polynomial. -/
def primonMomentValue (r : ℝ) (n : ℕ) : ℝ :=
  (primonMomentPolynomial n).eval₂ (Nat.castRingHom ℝ) r

@[simp] theorem primonMomentValue_zero (r : ℝ) : primonMomentValue r 0 = 1 := by
  simp only [primonMomentValue, primonMomentPolynomial_zero, Polynomial.eval₂_one]

/-- Real moment polynomials satisfy the same Catalan renewal equation. -/
theorem primonMomentValue_succ (r : ℝ) (n : ℕ) :
    primonMomentValue r (n + 1) = (1 + r) * ∑ i : Fin (n + 1),
      (catalan i : ℝ) * primonMomentValue r (n - i) := by
  rw [primonMomentValue, primonMomentPolynomial_succ]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_one,
    Polynomial.eval₂_X, Polynomial.eval₂_finsetSum, Polynomial.eval₂_C]
  rfl

private theorem primonMomentValue_succ_range (r : ℝ) (n : ℕ) :
    primonMomentValue r (n + 1) = (1 + r) * ∑ i ∈ range (n + 1),
      (catalan i : ℝ) * primonMomentValue r (n - i) := by
  rw [primonMomentValue_succ, Fin.sum_univ_eq_sum_range
    (fun i => (catalan i : ℝ) * primonMomentValue r (n - i))]

private theorem catalan_real_convolution (n : ℕ) :
    (∑ i ∈ range (n + 1), (catalan i : ℝ) * (catalan (n - i) : ℝ)) =
      (catalan (n + 1) : ℝ) := by
  rw [catalan_succ, Nat.cast_sum]
  simp only [Nat.cast_mul]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => (catalan i : ℝ) * (catalan (n - i) : ℝ)) (n + 1)).symm

/-- The renewal polynomials obey the same linear relation as the phase moments. -/
theorem primonMomentValue_shift_relation (r : ℝ) (n : ℕ) :
    r * primonMomentValue r (n + 1) =
      (1 + r) ^ 2 * primonMomentValue r n - (1 + r) * (catalan n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [primonMomentValue_succ_range r 0]
      simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_self, catalan_zero,
        Nat.cast_one, primonMomentValue_zero, mul_one]
      ring
    | succ n =>
      have hs : r * (∑ i ∈ range (n + 1), (catalan i : ℝ) *
          primonMomentValue r (n + 1 - i)) =
          (1 + r) ^ 2 * (∑ i ∈ range (n + 1), (catalan i : ℝ) *
            primonMomentValue r (n - i)) - (1 + r) * (catalan (n + 1) : ℝ) := by
        rw [← catalan_real_convolution n, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i ≤ n := by have := Finset.mem_range.mp hi; omega
        rw [show n + 1 - i = (n - i) + 1 by omega]
        have h := ih (n - i) (by omega)
        linear_combination (catalan i : ℝ) * h
      rw [primonMomentValue_succ_range r (n + 1), Finset.sum_range_succ,
        Nat.sub_self, primonMomentValue_zero, mul_one, primonMomentValue_succ_range r n]
      linear_combination (1 + r) * hs

/-- Setting the prime reciprocal to zero leaves exactly the Catalan moment. -/
theorem primonMomentValue_at_zero (n : ℕ) : primonMomentValue 0 n = (catalan n : ℝ) := by
  have h := primonMomentValue_shift_relation 0 n
  simpa only [zero_mul, add_zero, one_pow, one_mul, sub_eq_zero] using h.symm

/-- The positive polynomial recurrence agrees with the prime-dependent moment recurrence. -/
theorem primonMomentValue_prime_succ (p : Nat.Primes) (n : ℕ) :
    primonMomentValue (p : ℝ)⁻¹ (n + 1) =
      ((p : ℝ) + 1) ^ 2 / (p : ℝ) * primonMomentValue (p : ℝ)⁻¹ n -
        ((p : ℝ) + 1) * (catalan n : ℝ) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have h := primonMomentValue_shift_relation (p : ℝ)⁻¹ n
  field_simp [hp] at h ⊢
  nlinarith only [h]

/-- Every even prime-phase moment is the value of a polynomial with natural coefficients. -/
theorem kestenMoment_even_eq_polynomial (p : Nat.Primes) (n : ℕ) :
    kestenMoment p (2 * n) = primonMomentValue (p : ℝ)⁻¹ n := by
  induction n with
  | zero => simp only [Nat.mul_zero, kestenMoment_zero, primonMomentValue_zero]
  | succ n ih => rw [kestenMoment_even_succ, primonMomentValue_prime_succ, ih]

/-- The semicircle moment is exactly the constant coefficient of the finite-prime polynomial. -/
theorem primonMomentPolynomial_coeff_zero (n : ℕ) :
    (primonMomentPolynomial n).coeff 0 = catalan n := by
  have h := primonMomentValue_at_zero n
  rw [primonMomentValue, Polynomial.eval₂_at_zero] at h
  change ((primonMomentPolynomial n).coeff 0 : ℝ) = (catalan n : ℝ) at h
  exact_mod_cast h

private theorem primonMomentValue_pos_of_nonneg (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    0 < primonMomentValue r n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [primonMomentValue_zero]; exact zero_lt_one
    | succ n =>
      rw [primonMomentValue_succ_range]
      apply mul_pos (by linarith only [hr])
      apply Finset.sum_pos'
      · intro i _
        exact mul_nonneg (Nat.cast_nonneg _) (ih (n - i) (by omega)).le
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        simpa only [catalan_zero, Nat.cast_one, Nat.sub_zero, one_mul] using ih n (by omega)

private theorem primonMomentValue_mono_of_nonneg (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s)
    (n : ℕ) : primonMomentValue r n ≤ primonMomentValue s n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp only [primonMomentValue_zero, le_refl]
    | succ n =>
      rw [primonMomentValue_succ_range, primonMomentValue_succ_range]
      apply mul_le_mul (by linarith only [hrs])
      · apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (ih (n - i) (by omega)) (Nat.cast_nonneg _)
      · exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
          (primonMomentValue_pos_of_nonneg r hr (n - i)).le
      · linarith only [hr, hrs]

private theorem primonMomentValue_strict_of_nonneg (r s : ℝ) (hr : 0 ≤ r) (hrs : r < s)
    (n : ℕ) : primonMomentValue r (n + 1) < primonMomentValue s (n + 1) := by
  have hsum : (∑ i ∈ range (n + 1), (catalan i : ℝ) * primonMomentValue r (n - i)) ≤
      ∑ i ∈ range (n + 1), (catalan i : ℝ) * primonMomentValue s (n - i) := by
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (primonMomentValue_mono_of_nonneg r s hr hrs.le (n - i)) (Nat.cast_nonneg _)
  have hpos : 0 < ∑ i ∈ range (n + 1),
      (catalan i : ℝ) * primonMomentValue r (n - i) := by
    apply Finset.sum_pos'
    · exact fun i _ => mul_nonneg (Nat.cast_nonneg _)
        (primonMomentValue_pos_of_nonneg r hr (n - i)).le
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simpa only [catalan_zero, Nat.cast_one, Nat.sub_zero, one_mul] using
        primonMomentValue_pos_of_nonneg r hr n
  rw [primonMomentValue_succ_range, primonMomentValue_succ_range]
  exact (mul_lt_mul_of_pos_right (by linarith only [hrs] : 1 + r < 1 + s) hpos).trans_le
    (mul_le_mul_of_nonneg_left hsum (by linarith only [hr, hrs]))

/-- All moment polynomials are positive on the nonnegative real axis. -/
theorem primonMomentValue_pos (r : NNReal) (n : ℕ) : 0 < primonMomentValue r n :=
  primonMomentValue_pos_of_nonneg r r.property n

/-- Natural-coefficient moment polynomials increase with the nonnegative reciprocal parameter. -/
theorem monotone_primonMomentValue (n : ℕ) :
    Monotone (fun r : NNReal => primonMomentValue r n) := by
  intro r s hrs
  exact primonMomentValue_mono_of_nonneg r s r.property hrs n

/-- Every positive-degree moment polynomial is strictly increasing on the nonnegative axis. -/
theorem strictMono_primonMomentValue_succ (n : ℕ) :
    StrictMono (fun r : NNReal => primonMomentValue r (n + 1)) := by
  intro r s hrs
  exact primonMomentValue_strict_of_nonneg r s r.property hrs n

/-- Every positive even moment lies strictly above its semicircle limit at each finite prime. -/
theorem catalan_lt_kestenMoment_even_succ (p : Nat.Primes) (n : ℕ) :
    (catalan (n + 1) : ℝ) < kestenMoment p (2 * (n + 1)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [kestenMoment_even_eq_polynomial, ← primonMomentValue_at_zero]
  exact primonMomentValue_strict_of_nonneg 0 (p : ℝ)⁻¹ le_rfl (inv_pos.mpr hp) n

/-- Catalan numbers give a lower bound for every even prime-phase moment. -/
theorem catalan_le_kestenMoment_even (p : Nat.Primes) (n : ℕ) :
    (catalan n : ℝ) ≤ kestenMoment p (2 * n) := by
  cases n with
  | zero => simp only [catalan_zero, Nat.cast_one, Nat.mul_zero, kestenMoment_zero, le_refl]
  | succ n => exact (catalan_lt_kestenMoment_even_succ p n).le

/-- The ordering of positive even moments is exactly the reverse ordering of the primes. -/
theorem kestenMoment_even_lt_iff (p q : Nat.Primes) (n : ℕ) :
    kestenMoment p (2 * (n + 1)) < kestenMoment q (2 * (n + 1)) ↔ (q : ℕ) < (p : ℕ) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property.pos
  rw [kestenMoment_even_eq_polynomial, kestenMoment_even_eq_polynomial]
  constructor
  · intro h
    by_contra hqp
    have hinv : (q : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := by
      apply le_of_not_gt
      intro hbad
      exact hqp (by exact_mod_cast (inv_lt_inv₀ hp hq).mp hbad)
    exact (not_lt_of_ge (primonMomentValue_mono_of_nonneg (q : ℝ)⁻¹ (p : ℝ)⁻¹
      (inv_nonneg.mpr hq.le) hinv (n + 1))) h
  · intro hqp
    exact primonMomentValue_strict_of_nonneg (p : ℝ)⁻¹ (q : ℝ)⁻¹
      (inv_nonneg.mpr hp.le) ((inv_lt_inv₀ hp hq).mpr (by exact_mod_cast hqp)) n

end
end GaloisForLFunctions.SelbergClass.Primon
