import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.DivisorTransitions

/-!
# Universal coefficient-cone cancellation

Multiplication preserves and reflects coefficient nonnegativity for every polynomial exactly
when the multiplier is a positive monomial. Every other nonzero coefficient-positive multiplier
hides a negative coefficient in a polynomial strictly positive on the entire nonnegative axis.
The constructive witness has degree at most twice the degree of the multiplier.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The polynomial with coefficient one at each index from zero through `n`. -/
def flatPolynomial (n : ℕ) : ℝ[X] := ∑ j ∈ Finset.range (n + 1), X ^ j

theorem flatPolynomial_coeff (n k : ℕ) :
    (flatPolynomial n).coeff k = if k ≤ n then 1 else 0 := by
  classical
  simp [flatPolynomial, eq_comm, Nat.lt_succ_iff]

theorem coeffNonneg_flatPolynomial (n : ℕ) : CoeffNonneg (flatPolynomial n) := by
  intro k
  rw [flatPolynomial_coeff]
  split_ifs <;> norm_num

/-- On the central band a long flat convolution sees every coefficient of the multiplier. -/
theorem coeff_mul_flatPolynomial_band (q : ℝ[X]) {k : ℕ}
    (hk : q.natDegree ≤ k) (hk' : k ≤ 2 * q.natDegree) :
    (q * flatPolynomial (2 * q.natDegree)).coeff k = q.eval 1 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ,
    eval_eq_sum_range' (show q.natDegree < k + 1 by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one]
  by_cases hdeg : j ≤ q.natDegree
  · rw [flatPolynomial_coeff, if_pos (show k - j ≤ 2 * q.natDegree by omega), mul_one]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hdeg), zero_mul]

/-- The flat polynomial dominates its middle monomial uniformly on the nonnegative axis. -/
theorem middle_monomial_le_flatPolynomial (D : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (D + 1 : ℝ) * y ^ D ≤ (flatPolynomial (2 * D)).eval y := by
  simp only [flatPolynomial, eval_finsetSum, eval_pow, eval_X]
  by_cases hy1 : y ≤ 1
  · have hfirst : (D + 1 : ℝ) * y ^ D ≤ ∑ j ∈ Finset.range (D + 1), y ^ j := by
      calc
        _ = ∑ j ∈ Finset.range (D + 1), y ^ D := by simp
        _ ≤ _ := Finset.sum_le_sum fun j hj =>
          pow_le_pow_of_le_one hy hy1 (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
    have hsubset : Finset.range (D + 1) ⊆ Finset.range (2 * D + 1) := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    exact hfirst.trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset fun j _ _ => pow_nonneg hy j)
  · have hy1' : 1 ≤ y := (lt_of_not_ge hy1).le
    rw [show 2 * D + 1 = D + (D + 1) by omega, Finset.sum_range_add]
    have hlast : (D + 1 : ℝ) * y ^ D ≤ ∑ j ∈ Finset.range (D + 1), y ^ (D + j) := by
      calc
        _ = ∑ j ∈ Finset.range (D + 1), y ^ D := by simp
        _ ≤ _ := Finset.sum_le_sum fun j _ => pow_le_pow_right₀ hy1' (by omega)
    have hfirst : 0 ≤ ∑ j ∈ Finset.range D, y ^ j :=
      Finset.sum_nonneg fun j _ => pow_nonneg hy j
    linarith

/-- A slightly lowered middle coefficient defeats every nonmonomial positive multiplier. -/
def coefficientReflectionWitness (D : ℕ) (b : ℝ) : ℝ[X] :=
  flatPolynomial (2 * D) - C b * X ^ D

theorem coefficientReflectionWitness_coeff (D k : ℕ) (b : ℝ) :
    (coefficientReflectionWitness D b).coeff k =
      (if k ≤ 2 * D then 1 else 0) - (if k = D then b else 0) := by
  rw [coefficientReflectionWitness, coeff_sub, flatPolynomial_coeff, coeff_C_mul_X_pow]

theorem coefficientReflectionWitness_not_nonneg (D : ℕ) {b : ℝ} (hb : 1 < b) :
    ¬ CoeffNonneg (coefficientReflectionWitness D b) := by
  intro h
  have hm := h D
  rw [coefficientReflectionWitness_coeff, if_pos (by omega), if_pos rfl] at hm
  linarith

theorem coefficientReflectionWitness_eval_pos {D : ℕ} (hD : 0 < D) {b : ℝ}
    (hb : b < D + 1) {y : ℝ} (hy : 0 ≤ y) :
    0 < (coefficientReflectionWitness D b).eval y := by
  by_cases hy0 : y = 0
  · subst y
    simp [coefficientReflectionWitness, flatPolynomial, hD.ne']
  · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have hflat := middle_monomial_le_flatPolynomial D hy
    have hgap := mul_pos (sub_pos.mpr hb) (pow_pos hyp D)
    simp only [coefficientReflectionWitness, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    nlinarith only [hflat, hgap]

/-- Only the central band can lose coefficients; there every convolution coefficient is the sum. -/
theorem coeffNonneg_mul_coefficientReflectionWitness {q : ℝ[X]} (hq : CoeffNonneg q)
    {b : ℝ} (hbound : ∀ i, b * q.coeff i ≤ q.eval 1) :
    CoeffNonneg (q * coefficientReflectionWitness q.natDegree b) := by
  intro k
  have heq : q * coefficientReflectionWitness q.natDegree b =
      q * flatPolynomial (2 * q.natDegree) - C b * (q * X ^ q.natDegree) := by
    unfold coefficientReflectionWitness
    ring
  rw [heq, coeff_sub, coeff_C_mul, coeff_mul_X_pow']
  by_cases hlo : q.natDegree ≤ k
  · rw [if_pos hlo]
    by_cases hhi : k ≤ 2 * q.natDegree
    · rw [coeff_mul_flatPolynomial_band q hlo hhi]
      exact sub_nonneg.mpr (hbound _)
    · have hdeg : q.natDegree < k - q.natDegree := by omega
      rw [coeff_eq_zero_of_natDegree_lt hdeg, mul_zero, sub_zero]
      exact hq.mul (coeffNonneg_flatPolynomial _) k
  · rw [if_neg hlo, mul_zero, sub_zero]
    exact hq.mul (coeffNonneg_flatPolynomial _) k


/-- Every nonmonomial positive multiplier hides a defect in a polynomial that stays strictly
positive on the nonnegative axis. The witness degree is at most twice the multiplier degree. -/
theorem exists_positive_reflection_counterexample {q : ℝ[X]} (hq : CoeffNonneg q)
    (hq0 : q ≠ 0) (hmono : ¬ ∃ a : ℕ, ∃ c : ℝ, 0 < c ∧ q = C c * X ^ a) :
    ∃ p : ℝ[X], CoeffNonneg (q * p) ∧ ¬ CoeffNonneg p ∧
      (∀ y : ℝ, 0 ≤ y → 0 < p.eval y) ∧ p.natDegree ≤ 2 * q.natDegree := by
  classical
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image
    (Finset.range (q.natDegree + 1)) (fun i => q.coeff i)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have haD : a ≤ q.natDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha
  have hcD : q.coeff q.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hq0
  have hapos : 0 < q.coeff a :=
    (lt_of_le_of_ne (hq _) (Ne.symm hcD)).trans_le
      (hmax _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))
  have hother : ∃ j, j ≠ a ∧ q.coeff j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hmono
    refine ⟨a, q.coeff a, hapos, ?_⟩
    ext j
    rw [coeff_C_mul_X_pow]
    split_ifs with hja
    · subst j
      rfl
    · exact hn j hja
  obtain ⟨j, hja, hj⟩ := hother
  have hjD : j ≤ q.natDegree := by
    by_contra hn
    exact hj (coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn))
  have hD : 0 < q.natDegree := by omega
  have hjpos : 0 < q.coeff j := lt_of_le_of_ne (hq _) (Ne.symm hj)
  have hsum : q.eval 1 = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i := by
    rw [eval_eq_sum_range]
    simp only [one_pow, mul_one]
  have hsumgt : q.coeff a < q.eval 1 := by
    rw [hsum]
    exact Finset.single_lt_sum hja ha (Finset.mem_range.mpr (by omega)) hjpos
      (fun i _ _ => hq i)
  have hsumle : q.eval 1 ≤ (q.natDegree + 1 : ℝ) * q.coeff a := by
    rw [hsum]
    calc
      _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff a :=
        Finset.sum_le_sum fun i hi => hmax i hi
      _ = _ := by simp
  let b : ℝ := (q.eval 1 + q.coeff a) / (2 * q.coeff a)
  have hbEq : b * (2 * q.coeff a) = q.eval 1 + q.coeff a := by
    dsimp only [b]
    field_simp
  have hb : 1 < b := by
    apply (lt_div_iff₀ (show 0 < 2 * q.coeff a by positivity)).mpr
    linarith
  have hbD : b < q.natDegree + 1 := by
    apply (div_lt_iff₀ (show 0 < 2 * q.coeff a by positivity)).mpr
    have hdpos : 0 < (q.natDegree : ℝ) * q.coeff a := by positivity
    nlinarith only [hsumle, hdpos]
  have hbM : b * q.coeff a ≤ q.eval 1 := by nlinarith only [hbEq, hsumgt]
  have hmaxall (i : ℕ) : q.coeff i ≤ q.coeff a := by
    by_cases hi : i ≤ q.natDegree
    · exact hmax i (Finset.mem_range.mpr (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
      exact hapos.le
  refine ⟨coefficientReflectionWitness q.natDegree b,
    coeffNonneg_mul_coefficientReflectionWitness hq
      (fun i => (mul_le_mul_of_nonneg_left (hmaxall i) (by linarith)).trans hbM),
    coefficientReflectionWitness_not_nonneg _ hb,
    fun y hy => coefficientReflectionWitness_eval_pos hD hbD hy, ?_⟩
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coefficientReflectionWitness_coeff, if_neg (by omega), if_neg (by omega)]
  ring

/-- Positive monomials are exactly the universally reversible coefficient-cone multipliers. -/
theorem universal_coefficient_reflector_iff (q : ℝ[X]) :
    (∀ p : ℝ[X], CoeffNonneg (p * q) ↔ CoeffNonneg p) ↔
      ∃ a : ℕ, ∃ c : ℝ, 0 < c ∧ q = C c * X ^ a := by
  constructor
  · intro h
    have hq : CoeffNonneg q := by
      have h1 : CoeffNonneg (1 : ℝ[X]) := by
        intro n
        simp only [coeff_one]
        split_ifs <;> norm_num
      simpa only [one_mul] using (h 1).mpr h1
    have hq0 : q ≠ 0 := by
      intro hzero
      have hz : CoeffNonneg ((-1 : ℝ[X]) * q) := by
        rw [hzero, mul_zero]
        intro n
        simp
      have hc := (h (-1)).mp hz 0
      norm_num at hc
    by_contra hmono
    obtain ⟨p, hpq, hp, _, _⟩ := exists_positive_reflection_counterexample hq hq0 hmono
    exact hp ((h p).mp (by simpa only [mul_comm] using hpq))
  · rintro ⟨a, c, hc, rfl⟩ p
    rw [mul_comm, coeffNonneg_positive_monomial_mul_iff _ _ hc]

/-- A sparse shell cannot hide a defect before twice its exponent span. Each coefficient is
visible either before the first shifted term or after the degree of the original polynomial. -/
theorem coeffNonneg_mul_one_add_X_pow_iff_of_degree_lt (p : ℝ[X]) (D : ℕ)
    (hdeg : p.natDegree < 2 * D) :
    CoeffNonneg (p * (1 + X ^ D)) ↔ CoeffNonneg p := by
  constructor
  · intro h k
    by_cases hk : k < D
    · have hc := h k
      rw [mul_add, mul_one, coeff_add, coeff_mul_X_pow', if_neg (by omega), add_zero] at hc
      exact hc
    · have hc := h (k + D)
      rw [mul_add, mul_one, coeff_add, coeff_mul_X_pow,
        coeff_eq_zero_of_natDegree_lt (by omega), zero_add] at hc
      exact hc
  · intro h k
    rw [mul_add, mul_one, coeff_add, coeff_mul_X_pow']
    split_ifs
    · exact add_nonneg (h _) (h _)
    · simpa only [add_zero] using h k

/-- An extremal defect for the shell `1 + X^D`. -/
def sparseReflectionWitness (D : ℕ) : ℝ[X] := X ^ (2 * D) - X ^ D + 1

theorem sparseReflectionWitness_mul (D : ℕ) :
    sparseReflectionWitness D * (1 + X ^ D) = (1 : ℝ[X]) + X ^ (3 * D) := by
  rw [sparseReflectionWitness, show 2 * D = D * 2 by omega,
    show 3 * D = D * 3 by omega, pow_mul, pow_mul]
  ring

theorem sparseReflectionWitness_eval_pos (D : ℕ) (y : ℝ) :
    0 < (sparseReflectionWitness D).eval y := by
  simp only [sparseReflectionWitness, eval_add, eval_sub, eval_pow, eval_X, eval_one]
  rw [show 2 * D = D * 2 by omega, pow_mul]
  nlinarith only [sq_nonneg (y ^ D - 1 / 2)]

theorem sparseReflectionWitness_not_nonneg {D : ℕ} (hD : 0 < D) :
    ¬ CoeffNonneg (sparseReflectionWitness D) := by
  intro h
  have hc := h D
  simp only [sparseReflectionWitness, coeff_add, coeff_sub, coeff_X_pow,
    if_neg (show D ≠ 2 * D by omega), if_pos rfl, coeff_one,
    if_neg (show D ≠ 0 by omega)] at hc
  norm_num at hc

theorem coeffNonneg_sparseReflectionWitness_mul (D : ℕ) :
    CoeffNonneg (sparseReflectionWitness D * (1 + X ^ D)) := by
  rw [sparseReflectionWitness_mul]
  intro k
  simp only [coeff_add, coeff_one, coeff_X_pow]
  split_ifs <;> norm_num

/-- The extremal witness attains the universal degree bound exactly. -/
theorem sparseReflectionWitness_natDegree {D : ℕ} (hD : 0 < D) :
    (sparseReflectionWitness D).natDegree = 2 * D := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp only [sparseReflectionWitness, coeff_add, coeff_sub, coeff_X_pow, coeff_one,
      if_neg (show k ≠ 2 * D by omega), if_neg (show k ≠ D by omega),
      if_neg (show k ≠ 0 by omega)]
    ring
  · by_contra hdeg
    exact sparseReflectionWitness_not_nonneg hD
      ((coeffNonneg_mul_one_add_X_pow_iff_of_degree_lt _ D (lt_of_not_ge hdeg)).mp
        (coeffNonneg_sparseReflectionWitness_mul D))

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
