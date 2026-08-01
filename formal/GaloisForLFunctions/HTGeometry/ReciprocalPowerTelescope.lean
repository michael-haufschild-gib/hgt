import GaloisForLFunctions.HTGeometry.PolygammaSeries

/-!
# The telescoping defect of reciprocal powers

For reciprocals `a = w⁻¹` and `b = (w+1)⁻¹` the relation `a − b = a·b` holds, and it makes the
telescoping difference `a^{m+1} − b^{m+1}` agree with `(m+1)·a^{m+2}` to one order more than either
term:

`‖(a^{m+1} − b^{m+1}) − (m+1)a^{m+2}‖ ≤ (m+1)(m+2)‖a‖^{m+3}`.

Each summand of the geometric factorization differs from `a^{m+2}` only by exchanging some factors
`a` for factors `b`, and every such exchange costs another factor `a·b`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- Two reciprocals with `a − b = a·b` have powers differing by at most `j‖a‖^{j+1}`. -/
theorem norm_pow_sub_pow_le_of_sub_eq_mul {a b : ℂ} (hab : a - b = a * b) (hba : ‖b‖ ≤ ‖a‖)
    (j : ℕ) : ‖a ^ j - b ^ j‖ ≤ j * ‖a‖ ^ (j + 1) := by
  have hgeom := geom_sum₂_mul a b j
  rw [← hgeom, hab, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range j, a ^ i * b ^ (j - 1 - i)‖ ≤ j * ‖a‖ ^ (j - 1) := by
    calc ‖∑ i ∈ Finset.range j, a ^ i * b ^ (j - 1 - i)‖
        ≤ ∑ i ∈ Finset.range j, ‖a ^ i * b ^ (j - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range j, ‖a‖ ^ (j - 1) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hi' : i ≤ j - 1 := by
            have := Finset.mem_range.mp hi
            omega
          rw [norm_mul, norm_pow, norm_pow]
          have hb : ‖b‖ ^ (j - 1 - i) ≤ ‖a‖ ^ (j - 1 - i) :=
            pow_le_pow_left₀ (norm_nonneg _) hba _
          have hstep : ‖a‖ ^ i * ‖b‖ ^ (j - 1 - i) ≤ ‖a‖ ^ i * ‖a‖ ^ (j - 1 - i) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
          have hexp : ‖a‖ ^ i * ‖a‖ ^ (j - 1 - i) = ‖a‖ ^ (j - 1) := by
            rw [← pow_add]
            congr 1
            omega
          rw [← hexp]
          exact hstep
      _ = j * ‖a‖ ^ (j - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hab' : ‖a * b‖ ≤ ‖a‖ ^ 2 := by
    rw [norm_mul, sq]
    exact mul_le_mul_of_nonneg_left hba (norm_nonneg _)
  have hnn : (0 : ℝ) ≤ ‖∑ i ∈ Finset.range j, a ^ i * b ^ (j - 1 - i)‖ := norm_nonneg _
  calc ‖∑ i ∈ Finset.range j, a ^ i * b ^ (j - 1 - i)‖ * ‖a * b‖
      ≤ (j * ‖a‖ ^ (j - 1)) * ‖a‖ ^ 2 := by
        refine mul_le_mul hsum hab' (norm_nonneg _) ?_
        positivity
    _ ≤ j * ‖a‖ ^ (j + 1) := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp
        · have hexp : ‖a‖ ^ (j - 1) * ‖a‖ ^ 2 = ‖a‖ ^ (j + 1) := by
            rw [← pow_add]
            congr 1
            omega
          rw [mul_assoc, hexp]

/-- The geometric factorization of the telescoping difference. -/
theorem pow_sub_pow_eq_sum_of_sub_eq_mul {a b : ℂ} (hab : a - b = a * b) (m : ℕ) :
    a ^ (m + 1) - b ^ (m + 1)
      = ∑ i ∈ Finset.range (m + 1), a ^ (i + 1) * b ^ (m - i + 1) := by
  have hgeom := geom_sum₂_mul a b (m + 1)
  rw [← hgeom, hab, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ m := by
    have := Finset.mem_range.mp hi
    omega
  have hexp : m + 1 - 1 - i = m - i := by omega
  rw [hexp]
  ring

/-- **The telescoping defect.**  The difference of consecutive reciprocal powers agrees with
`(m+1)a^{m+2}` up to `(m+1)(m+2)‖a‖^{m+3}`. -/
theorem norm_telescope_defect_le {a b : ℂ} (hab : a - b = a * b) (hba : ‖b‖ ≤ ‖a‖) (m : ℕ) :
    ‖(a ^ (m + 1) - b ^ (m + 1)) - ((m : ℂ) + 1) * a ^ (m + 2)‖
      ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) * ‖a‖ ^ (m + 3) := by
  have hconst : ((m : ℂ) + 1) * a ^ (m + 2)
      = ∑ i ∈ Finset.range (m + 1), a ^ (i + 1) * a ^ (m - i + 1) := by
    have hterm : ∀ i ∈ Finset.range (m + 1), a ^ (i + 1) * a ^ (m - i + 1) = a ^ (m + 2) := by
      intro i hi
      have hi' : i ≤ m := by
        have := Finset.mem_range.mp hi
        omega
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [pow_sub_pow_eq_sum_of_sub_eq_mul hab m, hconst, ← Finset.sum_sub_distrib]
  calc ‖∑ i ∈ Finset.range (m + 1), (a ^ (i + 1) * b ^ (m - i + 1) - a ^ (i + 1) * a ^ (m - i + 1))‖
      ≤ ∑ i ∈ Finset.range (m + 1), ‖a ^ (i + 1) * b ^ (m - i + 1) - a ^ (i + 1) * a ^ (m - i + 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), ((m : ℝ) + 2) * ‖a‖ ^ (m + 3) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hi' : i ≤ m := by
          have := Finset.mem_range.mp hi
          omega
        have hfac : a ^ (i + 1) * b ^ (m - i + 1) - a ^ (i + 1) * a ^ (m - i + 1)
            = a ^ (i + 1) * (b ^ (m - i + 1) - a ^ (m - i + 1)) := by ring
        rw [hfac, norm_mul, norm_pow]
        have hsub : ‖b ^ (m - i + 1) - a ^ (m - i + 1)‖ ≤ ((m - i : ℕ) + 1 : ℝ) * ‖a‖ ^ (m - i + 2) := by
          have h := norm_pow_sub_pow_le_of_sub_eq_mul hab hba (m - i + 1)
          rw [norm_sub_rev]
          simpa using h
        have hstep : ‖a‖ ^ (i + 1) * ‖b ^ (m - i + 1) - a ^ (m - i + 1)‖
            ≤ ‖a‖ ^ (i + 1) * (((m - i : ℕ) + 1 : ℝ) * ‖a‖ ^ (m - i + 2)) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
        have hexp : ‖a‖ ^ (i + 1) * ‖a‖ ^ (m - i + 2) = ‖a‖ ^ (m + 3) := by
          rw [← pow_add]
          congr 1
          omega
        have hcount : ((m - i : ℕ) + 1 : ℝ) ≤ (m : ℝ) + 2 := by
          have : ((m - i : ℕ) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast Nat.sub_le m i
          linarith
        calc ‖a‖ ^ (i + 1) * ‖b ^ (m - i + 1) - a ^ (m - i + 1)‖
            ≤ ‖a‖ ^ (i + 1) * (((m - i : ℕ) + 1 : ℝ) * ‖a‖ ^ (m - i + 2)) := hstep
          _ = ((m - i : ℕ) + 1 : ℝ) * (‖a‖ ^ (i + 1) * ‖a‖ ^ (m - i + 2)) := by ring
          _ = ((m - i : ℕ) + 1 : ℝ) * ‖a‖ ^ (m + 3) := by rw [hexp]
          _ ≤ ((m : ℝ) + 2) * ‖a‖ ^ (m + 3) := by
              have hnn : (0 : ℝ) ≤ ‖a‖ ^ (m + 3) := by positivity
              exact mul_le_mul_of_nonneg_right hcount hnn
    _ = ((m : ℝ) + 1) * ((m : ℝ) + 2) * ‖a‖ ^ (m + 3) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end GaloisForLFunctions
