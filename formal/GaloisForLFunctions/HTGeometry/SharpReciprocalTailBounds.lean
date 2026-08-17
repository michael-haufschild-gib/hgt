import GaloisForLFunctions.HTGeometry.PhaseTailMajorization

/-!
# Sharp elementary bounds for finite reciprocal tails

The half-step telescoping bounds here retain enough endpoint information to resolve phase tails
whose size differs from a circuit-capacity threshold by less than one part in ten thousand.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- Half-step telescoping majorant for a finite inverse-square tail. -/
theorem sum_inv_sq_Ioc_le_halfstep (K L : ℕ) (hK : 1 ≤ K) (hKL : K ≤ L) :
    ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 2 ≤
      2 / (2 * K + 1 : ℕ) - 2 / (2 * L + 1 : ℕ) := by
  induction L with
  | zero =>
      have : K = 0 := Nat.le_zero.mp hKL
      omega
  | succ L ih =>
      by_cases h : K ≤ L
      · rw [Finset.sum_Ioc_succ_top h]
        have hprev := ih h
        have hLpos : (0 : ℝ) < L := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hK.trans h)
        have hstep : (1 : ℝ) / ((L + 1 : ℕ) : ℝ) ^ 2 ≤
            2 / (2 * L + 1 : ℕ) - 2 / (2 * (L + 1) + 1 : ℕ) := by
          norm_num [div_eq_mul_inv]
          field_simp
          nlinarith [sq_nonneg (L : ℝ)]
        linarith
      · have hEq : K = L + 1 := by omega
        subst K
        simp

/-- Half-step telescoping majorant for a finite inverse-fourth tail. -/
theorem sum_inv_fourth_Ioc_le_halfstep (K L : ℕ) (hK : 1 ≤ K) (hKL : K ≤ L) :
    ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 4 ≤
      (8 / 3 : ℝ) *
        (1 / ((2 * K + 1 : ℕ) : ℝ) ^ 3 -
          1 / ((2 * L + 1 : ℕ) : ℝ) ^ 3) := by
  induction L with
  | zero =>
      have : K = 0 := Nat.le_zero.mp hKL
      omega
  | succ L ih =>
      by_cases h : K ≤ L
      · rw [Finset.sum_Ioc_succ_top h]
        have hprev := ih h
        have hLpos : (0 : ℝ) < L := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hK.trans h)
        have hstep : (1 : ℝ) / ((L + 1 : ℕ) : ℝ) ^ 4 ≤
            (8 / 3 : ℝ) *
              (1 / ((2 * L + 1 : ℕ) : ℝ) ^ 3 -
                1 / ((2 * (L + 1) + 1 : ℕ) : ℝ) ^ 3) := by
          norm_num [div_eq_mul_inv]
          field_simp
          nlinarith [sq_nonneg (L : ℝ), sq_nonneg ((L : ℝ) ^ 2)]
        linarith
      · have hEq : K = L + 1 := by omega
        subst K
        simp

/-- Two-term Euler--Maclaurin minorant for a finite inverse-square tail. -/
theorem sum_inv_sq_Ioc_ge_twoterm (K L : ℕ) (hKL : K ≤ L) :
    1 / ((K + 1 : ℕ) : ℝ) - 1 / ((L + 1 : ℕ) : ℝ) +
        (1 / 2 : ℝ) *
          (1 / ((K + 1 : ℕ) : ℝ) ^ 2 - 1 / ((L + 1 : ℕ) : ℝ) ^ 2) ≤
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 2 := by
  induction L with
  | zero =>
      have : K = 0 := Nat.le_zero.mp hKL
      subst K
      simp
  | succ L ih =>
      by_cases h : K ≤ L
      · rw [Finset.sum_Ioc_succ_top h]
        have hprev := ih h
        have hstep :
            1 / (((L + 1 : ℕ) : ℝ)) - 1 / (((L + 2 : ℕ) : ℝ)) +
                (1 / 2 : ℝ) *
                  (1 / (((L + 1 : ℕ) : ℝ)) ^ 2 -
                    1 / (((L + 2 : ℕ) : ℝ)) ^ 2) ≤
              1 / (((L + 1 : ℕ) : ℝ)) ^ 2 := by
          norm_num [div_eq_mul_inv]
          field_simp
          ring_nf
          norm_num
        linarith
      · have hEq : K = L + 1 := by omega
        subst K
        simp

/-- Two-term Euler--Maclaurin minorant for a finite inverse-fourth tail. -/
theorem sum_inv_fourth_Ioc_ge_twoterm (K L : ℕ) (hKL : K ≤ L) :
    (1 / 3 : ℝ) *
          (1 / ((K + 1 : ℕ) : ℝ) ^ 3 - 1 / ((L + 1 : ℕ) : ℝ) ^ 3) +
        (1 / 2 : ℝ) *
          (1 / ((K + 1 : ℕ) : ℝ) ^ 4 - 1 / ((L + 1 : ℕ) : ℝ) ^ 4) ≤
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 4 := by
  induction L with
  | zero =>
      have : K = 0 := Nat.le_zero.mp hKL
      subst K
      simp
  | succ L ih =>
      by_cases h : K ≤ L
      · rw [Finset.sum_Ioc_succ_top h]
        have hprev := ih h
        have hstep :
            (1 / 3 : ℝ) *
                  (1 / (((L + 1 : ℕ) : ℝ)) ^ 3 -
                    1 / (((L + 2 : ℕ) : ℝ)) ^ 3) +
                (1 / 2 : ℝ) *
                  (1 / (((L + 1 : ℕ) : ℝ)) ^ 4 -
                    1 / (((L + 2 : ℕ) : ℝ)) ^ 4) ≤
              1 / (((L + 1 : ℕ) : ℝ)) ^ 4 := by
          norm_num [div_eq_mul_inv]
          field_simp
          ring_nf
          have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
          nlinarith
        linarith
      · have hEq : K = L + 1 := by omega
        subst K
        simp

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
