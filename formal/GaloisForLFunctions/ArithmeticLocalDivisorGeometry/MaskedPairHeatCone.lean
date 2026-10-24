import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedHeatIndex
import GaloisForLFunctions.HTGeometry.PolynomialHeatFactorBounds

/-!
# The full heat cone of a centrally masked adverse pair

All even coefficients of `exp(sD²)[X^(2m)(X²-a)²]` are retained. The monomial heat formula
connects their signs to the finite quadratic-index family, including the highest adverse order.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The even coefficient of the heat of a monomial, with its exact vanishing range. -/
def evenHeatMonomialCoeff (s : ℝ) (r j : ℕ) : ℝ :=
  if j ≤ r then s ^ (r - j) / (r - j).factorial *
    ((2 * r).factorial / (2 * j).factorial : ℝ) else 0

theorem forwardPolyHeat_even_monomial_coeff (s : ℝ) (r j : ℕ) :
    (forwardPolyHeat s (X ^ (2 * r))).coeff (2 * j) = evenHeatMonomialCoeff s r j := by
  rw [forwardPolyHeat_eq_sum (N := r + 1) (by rw [natDegree_X_pow]; omega)]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul,
    coeff_X_pow, descFactorial_two_mul_cast, mul_ite, mul_one, mul_zero]
  by_cases hj : j ≤ r
  · rw [evenHeatMonomialCoeff, if_pos hj, Finset.sum_eq_single (r - j)]
    · rw [if_pos (show 2 * j + 2 * (r - j) = 2 * r by omega),
        show 2 * j + 2 * (r - j) = 2 * r by omega]
    · intro k hk hne
      rw [if_neg (show ¬ 2 * j + 2 * k = 2 * r by omega)]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · rw [evenHeatMonomialCoeff, if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (show ¬ 2 * j + 2 * k = 2 * r by omega)]

theorem forwardPolyHeat_even_monomial_coeff_odd (s : ℝ) (r j : ℕ) :
    (forwardPolyHeat s (X ^ (2 * r))).coeff (2 * j + 1) = 0 := by
  rw [forwardPolyHeat_eq_sum (N := r + 1) (by rw [natDegree_X_pow]; omega)]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg (show ¬ 2 * j + 1 + 2 * k = 2 * r by omega)]
  ring

/-- An adverse pair at its ordinate, behind a central zero of multiplicity `m`. -/
def centralMaskedPair (a : ℝ) (m : ℕ) : ℝ[X] := X ^ (2 * m) * (X ^ 2 - C a) ^ 2

theorem centralMaskedPair_eq (a : ℝ) (m : ℕ) :
    centralMaskedPair a m = X ^ (2 * (m + 2)) + C (-2 * a) * X ^ (2 * (m + 1)) +
      C (a ^ 2) * X ^ (2 * m) := by
  simp only [centralMaskedPair, mul_add, pow_add, map_mul, map_neg, map_ofNat, map_pow]
  ring

theorem centralMaskedPair_heat_coeff_even (a s : ℝ) (m j : ℕ) :
    (forwardPolyHeat s (centralMaskedPair a m)).coeff (2 * j) =
      evenHeatMonomialCoeff s (m + 2) j - 2 * a * evenHeatMonomialCoeff s (m + 1) j +
        a ^ 2 * evenHeatMonomialCoeff s m j := by
  rw [centralMaskedPair_eq, forwardPolyHeat_add, forwardPolyHeat_add,
    forwardPolyHeat_C_mul, forwardPolyHeat_C_mul]
  simp only [coeff_add, coeff_C_mul, forwardPolyHeat_even_monomial_coeff]
  ring

theorem centralMaskedPair_heat_coeff_odd (a s : ℝ) (m j : ℕ) :
    (forwardPolyHeat s (centralMaskedPair a m)).coeff (2 * j + 1) = 0 := by
  rw [centralMaskedPair_eq, forwardPolyHeat_add, forwardPolyHeat_add,
    forwardPolyHeat_C_mul, forwardPolyHeat_C_mul]
  simp only [coeff_add, coeff_C_mul, forwardPolyHeat_even_monomial_coeff_odd, mul_zero, add_zero]

theorem evenHeatMonomialCoeff_pos {s : ℝ} (hs : 0 < s) {r j : ℕ} (hj : j ≤ r) :
    0 < evenHeatMonomialCoeff s r j := by
  rw [evenHeatMonomialCoeff, if_pos hj]
  positivity

theorem evenHeatMonomialCoeff_self (s : ℝ) (r : ℕ) :
    evenHeatMonomialCoeff s r r = 1 := by
  have hf : ((2 * r).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp [evenHeatMonomialCoeff, hf]

/-- Raising the monomial degree by two changes only three factorial factors. -/
theorem evenHeatMonomialCoeff_succ (s : ℝ) {r j : ℕ} (hj : j ≤ r) :
    ((r + 1 - j : ℕ) : ℝ) * evenHeatMonomialCoeff s (r + 1) j =
      (2 * r + 2 : ℝ) * (2 * r + 1) * s * evenHeatMonomialCoeff s r j := by
  have hd : r + 1 - j = (r - j) + 1 := by omega
  have hf : ((2 * (r + 1)).factorial : ℝ) =
      (2 * r + 2 : ℝ) * (2 * r + 1) * (2 * r).factorial := by
    rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hfac : ((r - j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hjfac : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hnext : ((r - j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  rw [evenHeatMonomialCoeff, if_pos (by omega), evenHeatMonomialCoeff, if_pos hj,
    hf, hd, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

/-- The two adjacent monomial recurrences expose the complete signed index weight. -/
theorem centralMaskedPair_heat_coeff_scaled (a t : ℝ) (m j : ℕ) (hj : j ≤ m) :
    ((m + 1 - j : ℕ) : ℝ) * (((m + 1 - j : ℕ) : ℝ) + 1) *
      (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * j) =
    a ^ 2 * evenHeatMonomialCoeff (a * t) m j * maskedHeatIndex m t (m + 1 - j) := by
  have h₁ := evenHeatMonomialCoeff_succ (a * t) hj
  have h₂ := evenHeatMonomialCoeff_succ (a * t) (show j ≤ m + 1 by omega)
  rw [show m + 1 + 1 - j = (m + 1 - j) + 1 by omega] at h₂
  push_cast at h₂
  rw [centralMaskedPair_heat_coeff_even]
  unfold maskedHeatIndex
  linear_combination
    ((m + 1 - j : ℕ) : ℝ) * h₂ +
      ((2 * m + 4 : ℝ) * (2 * m + 3) * a * t -
        2 * a * (((m + 1 - j : ℕ) : ℝ) + 1)) * h₁

theorem centralMaskedPair_heat_coeff_nonneg_iff {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (m j : ℕ) (hj : j ≤ m) :
    0 ≤ (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * j) ↔
      0 ≤ maskedHeatIndex m t (m + 1 - j) := by
  have hk : (0 : ℝ) < ((m + 1 - j : ℕ) : ℝ) := by exact_mod_cast (show 0 < m + 1 - j by omega)
  have hkk : 0 < ((m + 1 - j : ℕ) : ℝ) * (((m + 1 - j : ℕ) : ℝ) + 1) := by positivity
  have hc := evenHeatMonomialCoeff_pos (mul_pos ha ht) hj
  have hfac : 0 < a ^ 2 * evenHeatMonomialCoeff (a * t) m j := mul_pos (sq_pos_of_pos ha) hc
  have heq := centralMaskedPair_heat_coeff_scaled a t m j hj
  constructor
  · intro h
    have hh := mul_nonneg hkk.le h
    rw [heq] at hh
    exact (mul_nonneg_iff_of_pos_left hfac).mp hh
  · intro h
    have hh := mul_nonneg hfac.le h
    rw [← heq] at hh
    exact (mul_nonneg_iff_of_pos_left hkk).mp hh

/-- The highest adverse coefficient is the zero-index member of the sign family. -/
theorem centralMaskedPair_heat_coeff_penultimate (a t : ℝ) (m : ℕ) :
    (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * (m + 1)) =
      a * ((2 * m + 4 : ℝ) * (2 * m + 3) * t - 2) := by
  have h := evenHeatMonomialCoeff_succ (a * t) (le_refl (m + 1))
  rw [evenHeatMonomialCoeff_self] at h
  norm_num only [show m + 1 + 1 - (m + 1) = 1 by omega, Nat.cast_one, one_mul,
    Nat.cast_add, Nat.cast_one] at h
  rw [centralMaskedPair_heat_coeff_even, evenHeatMonomialCoeff_self,
    show evenHeatMonomialCoeff (a * t) m (m + 1) = 0 by
      rw [evenHeatMonomialCoeff, if_neg (by omega)], mul_zero, add_zero]
  linear_combination h

theorem centralMaskedPair_heat_coeff_leading (a t : ℝ) (m : ℕ) :
    (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * (m + 2)) = 1 := by
  rw [centralMaskedPair_heat_coeff_even, evenHeatMonomialCoeff_self]
  simp only [evenHeatMonomialCoeff, if_neg (show ¬m + 2 ≤ m + 1 by omega),
    if_neg (show ¬m + 2 ≤ m by omega), mul_zero, sub_zero, add_zero]

theorem centralMaskedPair_heat_coeff_above (a t : ℝ) (m j : ℕ) (hj : m + 2 < j) :
    (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * j) = 0 := by
  rw [centralMaskedPair_heat_coeff_even]
  simp only [evenHeatMonomialCoeff, if_neg (show ¬j ≤ m + 2 by omega),
    if_neg (show ¬j ≤ m + 1 by omega), if_neg (show ¬j ≤ m by omega),
    mul_zero, sub_zero, add_zero]

theorem centralMaskedPair_heat_coeff_index_nonneg_iff {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (m k : ℕ) (hk : k ≤ m + 1) :
    0 ≤ (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * (m + 1 - k)) ↔
      0 ≤ maskedHeatIndex m t k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [Nat.sub_zero, centralMaskedPair_heat_coeff_penultimate,
      mul_nonneg_iff_of_pos_left ha]
    have heq : maskedHeatIndex m t 0 =
        ((2 * m + 2 : ℝ) * (2 * m + 1) * t) *
          ((2 * m + 4 : ℝ) * (2 * m + 3) * t - 2) := by
      unfold maskedHeatIndex
      norm_num only [Nat.cast_zero, zero_add, zero_mul]
      ring
    rw [heq, mul_nonneg_iff_of_pos_left (show 0 < (2 * m + 2 : ℝ) * (2 * m + 1) * t by positivity)]
  · rw [centralMaskedPair_heat_coeff_nonneg_iff ha ht m (m + 1 - k) (by omega),
      show m + 1 - (m + 1 - k) = k by omega]

private theorem zero_iff_of_positive_weights {A B x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : A * x = B * y) : x = 0 ↔ y = 0 := by
  constructor
  · intro hx
    have hy : B * y = 0 := by rw [← h, hx, mul_zero]
    exact (mul_eq_zero.mp hy).resolve_left hB.ne'
  · intro hy
    have hx : A * x = 0 := by rw [h, hy, mul_zero]
    exact (mul_eq_zero.mp hx).resolve_left hA.ne'

/-- Vanishing, as well as sign, transfers through the strictly positive heat weights. -/
theorem centralMaskedPair_heat_coeff_index_zero_iff {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (m k : ℕ) (hk : k ≤ m + 1) :
    (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * (m + 1 - k)) = 0 ↔
      maskedHeatIndex m t k = 0 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · apply zero_iff_of_positive_weights
      (show 0 < (2 * m + 2 : ℝ) * (2 * m + 1) * t by positivity) ha
    rw [Nat.sub_zero, centralMaskedPair_heat_coeff_penultimate]
    unfold maskedHeatIndex
    norm_num only [Nat.cast_zero, zero_add, zero_mul]
    ring
  · have hj : m + 1 - k ≤ m := by omega
    have h := centralMaskedPair_heat_coeff_scaled a t m (m + 1 - k) hj
    rw [show m + 1 - (m + 1 - k) = k by omega] at h
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    apply zero_iff_of_positive_weights (show 0 < (k : ℝ) * (k + 1) by positivity)
      (mul_pos (sq_pos_of_pos ha) (evenHeatMonomialCoeff_pos (mul_pos ha ht) hj)) h

theorem centralMaskedPair_heat_coeff_index_pos_iff {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (m k : ℕ) (hk : k ≤ m + 1) :
    0 < (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff (2 * (m + 1 - k)) ↔
      0 < maskedHeatIndex m t k := by
  have hnonneg := centralMaskedPair_heat_coeff_index_nonneg_iff ha ht m k hk
  have hzero := centralMaskedPair_heat_coeff_index_zero_iff ha ht m k hk
  constructor
  · intro h
    exact lt_of_le_of_ne (hnonneg.mp h.le) fun heq => h.ne' (hzero.mpr heq.symm)
  · intro h
    exact lt_of_le_of_ne (hnonneg.mpr h.le) fun heq => h.ne' (hzero.mp heq.symm)

/-- The full coefficient cone is a finite quadratic-index test; no order is discarded. -/
theorem coeffNonneg_centralMaskedPair_heat_iff {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (m : ℕ) :
    CoeffNonneg (forwardPolyHeat (a * t) (centralMaskedPair a m)) ↔
      ∀ k ≤ m + 1, 0 ≤ maskedHeatIndex m t k := by
  constructor
  · intro h k hk
    exact (centralMaskedPair_heat_coeff_index_nonneg_iff ha ht m k hk).mp (h _)
  · intro h n
    by_cases heven : n % 2 = 0
    · rw [show n = 2 * (n / 2) by omega]
      by_cases hj : n / 2 ≤ m
      · exact (centralMaskedPair_heat_coeff_nonneg_iff ha ht m (n / 2) hj).mpr
          (h _ (by omega))
      · by_cases hnext : n / 2 = m + 1
        · rw [hnext]
          simpa only [Nat.sub_zero] using
            (centralMaskedPair_heat_coeff_index_nonneg_iff ha ht m 0 (by omega)).mpr (h 0 (by omega))
        · by_cases htop : n / 2 = m + 2
          · rw [htop, centralMaskedPair_heat_coeff_leading]
            norm_num
          · rw [centralMaskedPair_heat_coeff_above a t m (n / 2) (by omega)]
    · rw [show n = 2 * (n / 2) + 1 by omega, centralMaskedPair_heat_coeff_odd]

/-- Inverse multiplicity scale suffices for every coefficient simultaneously. -/
theorem coeffNonneg_centralMaskedPair_heat_of_upper {a t : ℝ} (ha : 0 < a) (m : ℕ)
    (ht : 1 ≤ (8 * m + 5 : ℝ) * t) :
    CoeffNonneg (forwardPolyHeat (a * t) (centralMaskedPair a m)) := by
  have htpos : 0 < t := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (8 * m + 5 : ℝ) by positivity) (le_of_not_gt hn)
    linarith only [ht, hp]
  exact (coeffNonneg_centralMaskedPair_heat_iff ha htpos m).mpr
    fun k _ => (maskedHeatIndex_pos_of_upper m k ht).le

/-- A floor-selected actual coefficient is negative below the lower multiplicity bound. -/
theorem centralMaskedPair_heat_floor_coeff_neg {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (m : ℕ) (hsmall : (8 * m + 10 : ℝ) * t < 1) :
    (forwardPolyHeat (a * t) (centralMaskedPair a m)).coeff
      (2 * (m + 1 - Nat.floor (((2 * m + 2 : ℝ) * (2 * m + 1)) * t))) < 0 := by
  obtain ⟨hk, hneg⟩ := maskedHeatIndex_floor_neg m ht hsmall
  apply lt_of_not_ge
  intro h
  exact (not_le_of_gt hneg)
    ((centralMaskedPair_heat_coeff_index_nonneg_iff ha ht m _ hk).mp h)

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
