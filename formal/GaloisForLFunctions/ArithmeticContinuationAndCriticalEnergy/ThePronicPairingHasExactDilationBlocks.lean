import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure

/-!
# Exact dilation blocks for the pronic pairing

The complete integer fibres of division by p have pronic mass 1/(p*n*(n+1)).
Summing fibrewise scales every mixed pairing by exactly 1/p.
-/

section

noncomputable section
set_option autoImplicit false
open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

/-- Complete dilation blocks preserve the entire pronic pairing with factor `1/p`. -/
theorem pronicPairing_rowDilate_complete_blocks {p : ℕ} (hp : 1 ≤ p)
    (N : ℕ) (u v : ℕ → ℝ) (hu0 : u 0 = 0) :
    pronicPairing (p * (N + 1) - 1) (rowDilate p u) (rowDilate p v) =
      (1 / (p : ℝ)) * pronicPairing N u v := by
  have hp0 : 0 < p := hp
  have hmaps : ∀ n ∈ Icc 1 (p * (N + 1) - 1), n / p ∈ range (N + 1) := by
    intro n hn
    rw [mem_range, Nat.div_lt_iff_lt_mul hp0]
    have h := (mem_Icc.mp hn).2
    have hpos : 0 < p * (N + 1) := Nat.mul_pos hp0 (Nat.succ_pos _)
    rw [Nat.mul_comm]
    omega
  unfold pronicPairing
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => rowDilate p u n * rowDilate p v n / ((n : ℝ) * ((n : ℝ) + 1)))]
  have hfiber (m : ℕ) (hm : m ∈ range (N + 1)) :
      (∑ n ∈ (Icc 1 (p * (N + 1) - 1)).filter (fun n => n / p = m),
        rowDilate p u n * rowDilate p v n / ((n : ℝ) * ((n : ℝ) + 1))) =
      (1 / (p : ℝ)) * (if m = 0 then 0 else
        u m * v m / ((m : ℝ) * ((m : ℝ) + 1))) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [if_pos rfl, mul_zero]
      apply sum_eq_zero
      intro n hn
      rw [mem_filter] at hn
      simp only [rowDilate, hn.2, hu0, zero_mul, zero_div]
    · have hmN : m ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hm
      have hfilter : (Icc 1 (p * (N + 1) - 1)).filter (fun n => n / p = m) =
          Icc (p * m) (p * m + p - 1) := by
        ext n
        constructor
        · intro hn
          rcases mem_filter.mp hn with ⟨hn, hdiv⟩
          have hlo : p * m ≤ n := by rw [← hdiv]; exact Nat.mul_div_le n p
          have hhi : n < (m + 1) * p := (Nat.div_lt_iff_lt_mul hp0).mp (by omega)
          have hid : (m + 1) * p = p * m + p := by ring
          rw [hid] at hhi
          exact mem_Icc.mpr ⟨hlo, by omega⟩
        · intro hn
          rcases mem_Icc.mp hn with ⟨hlo, hhi⟩
          have hpm : 1 ≤ p * m := Nat.mul_pos hp0 hm0
          have htop : p * m + p ≤ p * (N + 1) := by
            rw [show p * m + p = p * (m + 1) by ring]
            exact Nat.mul_le_mul_left p (Nat.succ_le_succ hmN)
          have hdivlo : m ≤ n / p :=
            (Nat.le_div_iff_mul_le hp0).mpr (by simpa only [Nat.mul_comm] using hlo)
          have hdivhi : n / p < m + 1 := (Nat.div_lt_iff_lt_mul hp0).mpr (by
            have hid : (m + 1) * p = p * m + p := by ring
            rw [hid]
            omega)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpm.trans hlo, by omega⟩, by omega⟩
      have hconst : ∀ n ∈ (Icc 1 (p * (N + 1) - 1)).filter (fun n => n / p = m),
          rowDilate p u n * rowDilate p v n / ((n : ℝ) * ((n : ℝ) + 1)) =
            (u m * v m) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        intro n hn
        rw [mem_filter] at hn
        rw [rowDilate, rowDilate, hn.2]
        ring
      rw [sum_congr rfl hconst, ← mul_sum, hfilter,
        sum_Icc_pronic_dilation_fibre hp hm0, if_neg hm0.ne']
      field_simp
  rw [sum_congr rfl hfiber, ← mul_sum]
  congr 1
  have hins : range (N + 1) = insert 0 (Icc 1 N) := by
    ext m
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hins, sum_insert (by simp), if_pos rfl, zero_add]
  exact sum_congr rfl fun m hm => by rw [if_neg (Nat.ne_of_gt (mem_Icc.mp hm).1)]

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

#print axioms GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.pronicPairing_rowDilate_complete_blocks
end
end
