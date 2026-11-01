import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights

/-!
# Complete-period normalization of the odd-pair stabilizer model

A finite odd-conductor packet has raw mean two on odd-coordinate periods.
Their density in the full integer rectangle is one quarter, so the scalar
needed for full mean one is two. This concerns the arithmetic weight before
introducing a signed aperture kernel.
-/

noncomputable section
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.SuccessorShellArithmetic

namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem complete_pair_lag {q M : ℕ} (hq : 0 < q) (hqM : q ∣ M) :
    (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) =
      if q = 1 then (M : ℝ) ^ 2 else 0 := by
  by_cases hq1 : q = 1
  · subst q
    simp only [ramanujanLagCoefficient_one, sum_const, card_range, nsmul_eq_mul, mul_one,
      ite_true]
    ring
  · have hs (n : ℕ) : (∑ i ∈ range M, ramanujanLagCoefficient q (n + i)) = 0 := by
      have h := sum_range_ramanujanLagCoefficient_shift_mul hq (by omega : 0 < (1 : ℕ))
        hqM (one_dvd M) n 0
      simpa only [ramanujanLagCoefficient_one, mul_one, if_neg hq1, Nat.add_comm n] using h
    have h := ramanujanAutocorrelationWeight_eq_period_squares hq (range M) (fun _ => 1)
    simp only [one_mul, hs, zero_pow (by decide : 2 ≠ 0), sum_const_zero, mul_zero,
      ramanujanAutocorrelationWeight] at h
    rw [if_neg hq1]
    have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    exact (div_eq_zero_iff.mp h).resolve_right hφ

private theorem odd_coordinate_dist (i j : ℕ) :
    Nat.dist (2 * i + 1) (2 * j + 1) = 2 * Nat.dist i j := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le (by omega), Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega), Nat.dist_eq_sub_of_le_right h]
    omega

/-- The literal parity stabilizer packet has complete odd-coordinate mass `2M²`. -/
theorem sum_odd_coordinate_parityStabilizerWeight {Q M : ℕ} (hQ : 1 ≤ Q)
    (hperiod : ∀ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), q ∣ M) :
    (∑ i ∈ range M, ∑ j ∈ range M,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) = 2 * (M : ℝ) ^ 2 := by
  let S := (Icc 1 Q).filter (fun q => q % 2 = 1)
  have hone : 1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hQ⟩, by norm_num⟩
  simp_rw [odd_coordinate_dist, parityStabilizerWeight_two_mul]
  unfold parityStabilizerWeight
  simp_rw [← mul_sum]
  congr 1
  calc
    _ = ∑ i ∈ range M, ∑ q ∈ S, ∑ j ∈ range M,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ramanujanLagCoefficient q (Nat.dist i j) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ q ∈ S, ∑ i ∈ range M, ∑ j ∈ range M,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ramanujanLagCoefficient q (Nat.dist i j) := by rw [sum_comm]
    _ = ∑ q ∈ S, (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) := by
      simp only [mul_sum]
    _ = ∑ q ∈ S, if q = 1 then (M : ℝ) ^ 2 else 0 := by
      apply sum_congr rfl
      intro q hqS
      have hq : 0 < q := (mem_Icc.mp (mem_filter.mp hqS).1).1
      rw [complete_pair_lag hq (hperiod q hqS)]
      by_cases hq1 : q = 1
      · subst q
        simp only [sqfreeTotientInv_one, Nat.totient_one, Nat.cast_one, div_one,
          one_mul]
      · rw [if_neg hq1, mul_zero]
    _ = _ := by rw [sum_ite_eq', if_pos hone]

/-- Raw mean in the full `2M × 2M` rectangle, with the even-coordinate weight zero. -/
def oddStabilizerRectangleMean (Q M : ℕ) (β : ℝ) : ℝ :=
  (∑ i ∈ range M, ∑ j ∈ range M,
    β * parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) / (2 * (M : ℝ)) ^ 2

/-- Complete-period mean is exactly half the scalar placed in front of the singular series. -/
theorem oddStabilizerRectangleMean_eq {Q M : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M)
    (hperiod : ∀ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), q ∣ M) (β : ℝ) :
    oddStabilizerRectangleMean Q M β = β / 2 := by
  unfold oddStabilizerRectangleMean
  simp_rw [← mul_sum]
  rw [sum_odd_coordinate_parityStabilizerWeight hQ hperiod]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hMR]

/-- Scalar two is the unique complete-period normalization with raw mean one. -/
theorem oddStabilizerRectangleMean_eq_one_iff {Q M : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M)
    (hperiod : ∀ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), q ∣ M) (β : ℝ) :
    oddStabilizerRectangleMean Q M β = 1 ↔ β = 2 := by
  rw [oddStabilizerRectangleMean_eq hQ hM hperiod]
  constructor <;> intro h <;> linarith only [h]

/-- The scalar in `stabilizerModelOddCoalSum` has raw complete-period mean one eighth. -/
theorem oddStabilizerRectangleMean_quarter {Q M : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M)
    (hperiod : ∀ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), q ∣ M) :
    oddStabilizerRectangleMean Q M (1 / 4) = 1 / 8 := by
  rw [oddStabilizerRectangleMean_eq hQ hM hperiod]
  norm_num

/-- With its canonical common period, every nonempty cutoff has raw mean one eighth. -/
theorem oddStabilizerRectangleMean_factorial_quarter (Q : ℕ) :
    oddStabilizerRectangleMean (Q + 1) (Q + 1).factorial (1 / 4) = 1 / 8 := by
  apply oddStabilizerRectangleMean_quarter (by omega) (Nat.factorial_pos _)
  intro q hq
  have hqI := mem_Icc.mp (mem_filter.mp hq).1
  exact Nat.dvd_factorial (by omega) hqI.2

/-- The corrected raw mean is exactly one at every nonempty cutoff. -/
theorem oddStabilizerRectangleMean_factorial_two (Q : ℕ) :
    oddStabilizerRectangleMean (Q + 1) (Q + 1).factorial 2 = 1 := by
  rw [oddStabilizerRectangleMean_eq (by omega) (Nat.factorial_pos _)]
  · norm_num
  · intro q hq
    have hqI := mem_Icc.mp (mem_filter.mp hq).1
    exact Nat.dvd_factorial (by omega) hqI.2

private theorem sum_period_stabilizer {Q M : ℕ} (hQ : 1 ≤ Q)
    (hperiod : ∀ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), q ∣ M) :
    (∑ i ∈ range M, parityStabilizerWeight Q i) = 2 * (M : ℝ) := by
  let S := (Icc 1 Q).filter (fun q => q % 2 = 1)
  have hone : 1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hQ⟩, by norm_num⟩
  have hmode (q : ℕ) (hqS : q ∈ S) :
      (∑ i ∈ range M, ramanujanLagCoefficient q i) = if q = 1 then (M : ℝ) else 0 := by
    have hq : 0 < q := (mem_Icc.mp (mem_filter.mp hqS).1).1
    have h := sum_range_ramanujanLagCoefficient_mul hq (by omega : 0 < (1 : ℕ))
      (hperiod q hqS) (one_dvd M)
    simpa only [ramanujanLagCoefficient_one, mul_one, Nat.totient_one, Nat.cast_one] using h
  unfold parityStabilizerWeight
  rw [← mul_sum]
  congr 1
  calc
    _ = ∑ q ∈ S, (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        (∑ i ∈ range M, ramanujanLagCoefficient q i) := by
      simp only [mul_sum]
      rw [sum_comm]
    _ = ∑ q ∈ S, if q = 1 then (M : ℝ) else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [hmode q hq]
      by_cases hq1 : q = 1
      · subst q
        simp only [sqfreeTotientInv_one, Nat.totient_one, Nat.cast_one, div_one,
          one_mul]
      · rw [if_neg hq1, mul_zero]
    _ = _ := by rw [sum_ite_eq', if_pos hone]

private theorem erased_rectangle_off_diagonal {M : ℕ} (hM : 0 < M)
    (f : ℕ → ℕ → ℝ) (r w : ℝ)
    (hrow : (∑ j ∈ range M, f 0 j) = r)
    (hcol : (∑ i ∈ range M, f i 0) = r) (hdiag : ∀ i, f i i = w) :
    (∑ i ∈ (range M).erase 0, ∑ j ∈ ((range M).erase 0).erase i, f i j) =
      (∑ i ∈ range M, ∑ j ∈ range M, f i j) - 2 * r - ((M : ℝ) - 2) * w := by
  let S := (range M).erase 0
  have hzero : 0 ∈ range M := mem_range.mpr hM
  have hfull := sum_erase_add (range M) (fun i => ∑ j ∈ range M, f i j) hzero
  rw [hrow] at hfull
  have hcol' := sum_erase_add (range M) (fun i => f i 0) hzero
  rw [hcol, hdiag] at hcol'
  have hrect : (∑ i ∈ S, ∑ j ∈ range M, f i j) =
      (∑ i ∈ S, ∑ j ∈ S, f i j) + ∑ i ∈ S, f i 0 := by
    calc
      _ = ∑ i ∈ S, ((∑ j ∈ S, f i j) + f i 0) := by
        apply sum_congr rfl
        intro i _
        exact (sum_erase_add (range M) (f i) hzero).symm
      _ = _ := by rw [sum_add_distrib]
  have hdiag' : (∑ i ∈ S, ∑ j ∈ S, f i j) =
      (∑ i ∈ S, ∑ j ∈ S.erase i, f i j) + (S.card : ℝ) * w := by
    calc
      _ = ∑ i ∈ S, ((∑ j ∈ S.erase i, f i j) + w) := by
        apply sum_congr rfl
        intro i hi
        simpa only [hdiag] using (sum_erase_add S (f i) hi).symm
      _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) = (M : ℝ) - 1 := by
    dsimp only [S]
    rw [card_erase_of_mem hzero, card_range, Nat.cast_sub (by omega : 1 ≤ M)]
    norm_num
  rw [hcard] at hdiag'
  change (∑ i ∈ S, ∑ j ∈ S.erase i, f i j) = _
  change (∑ i ∈ S, ∑ j ∈ range M, f i j) + r = _ at hfull
  change (∑ i ∈ S, f i 0) + w = r at hcol'
  linarith only [hfull, hcol', hrect, hdiag']

/-- Exact boundary correction for an arbitrary cutoff and interval length. -/
theorem sum_distinct_odd_stabilizer_eq (Q : ℕ) {M : ℕ} (hM : 0 < M) :
    (∑ i ∈ (range M).erase 0, ∑ j ∈ ((range M).erase 0).erase i,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) =
        (∑ i ∈ range M, ∑ j ∈ range M,
          parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) -
        2 * (∑ i ∈ range M, parityStabilizerWeight Q i) -
        ((M : ℝ) - 2) * parityStabilizerWeight Q 0 := by
  let f := fun i j => parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))
  apply erased_rectangle_off_diagonal hM f
  · simp only [f, odd_coordinate_dist, Nat.dist_zero_left, parityStabilizerWeight_two_mul]
  · simp only [f, odd_coordinate_dist, Nat.dist_zero_right, parityStabilizerWeight_two_mul]
  · intro i
    simp only [f, Nat.dist_self]

/-- Removing the integer one and the diagonal changes only linear complete-period terms. -/
theorem sum_distinct_odd_stabilizer_period {Q M : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M)
    (hperiod : ∀ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), q ∣ M) :
    (∑ i ∈ (range M).erase 0, ∑ j ∈ ((range M).erase 0).erase i,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) =
        2 * (M : ℝ) ^ 2 - 4 * M - ((M : ℝ) - 2) * parityStabilizerWeight Q 0 := by
  rw [sum_distinct_odd_stabilizer_eq Q hM,
    sum_odd_coordinate_parityStabilizerWeight hQ hperiod, sum_period_stabilizer hQ hperiod]
  ring

end GaloisForLFunctions.TransThresholdPairCorrelation
