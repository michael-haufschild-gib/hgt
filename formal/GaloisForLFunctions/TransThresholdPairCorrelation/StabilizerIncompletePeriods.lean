import GaloisForLFunctions.TransThresholdPairCorrelation.StabilizerPeriodNormalization
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations

/-!
# Odd-pair stabilizer normalization on incomplete periods

Every nonconstant Ramanujan mode has bounded prefix sums. Its exact
period-square representation gives a nonnegative rectangle error, uniformly
in interval length. The cutoff error is polynomial, with no common-period
requirement.
-/

noncomputable section
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.SuccessorShellArithmetic
open GaloisForLFunctions.RenormalizedBiarithmeticGeometry
open GaloisForLFunctions.BiScaleUncertainty.SieveMoments

namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem lag_prefix_bound {q : ℕ} (hq : 0 < q) (hq1 : q ≠ 1) (n M : ℕ) :
    |∑ i ∈ range M, ramanujanLagCoefficient q (n + i)| ≤
      (q : ℝ) * q.totient := by
  have hper (i : ℕ) : ramanujanLagCoefficient q (n + (i + q)) =
      ramanujanLagCoefficient q (n + i) := by
    rw [← Nat.add_assoc]
    unfold ramanujanLagCoefficient
    apply sum_congr rfl
    intro d hd
    simp only [Nat.dvd_add_left (Nat.dvd_of_mem_divisors hd)]
  have hz : (∑ i ∈ range q, ramanujanLagCoefficient q (n + i)) = 0 := by
    have h := sum_range_ramanujanLagCoefficient_shift_mul hq (by omega : 0 < (1 : ℕ))
      dvd_rfl (one_dvd q) n 0
    simpa only [ramanujanLagCoefficient_one, mul_one, if_neg hq1, Nat.add_comm n] using h
  calc
    _ ≤ ∑ i ∈ range q, |ramanujanLagCoefficient q (n + i)| :=
      abs_sum_range_le_of_periodic hq hper hz M
    _ ≤ ∑ _i ∈ range q, (q.totient : ℝ) :=
      sum_le_sum fun i _ => abs_ramanujanLagCoefficient_le_totient q (n + i)
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

private theorem lag_pair_bounds {q : ℕ} (hq : 0 < q) (hq1 : q ≠ 1) (M : ℕ) :
    0 ≤ (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) ∧
    (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) ≤
      (q : ℝ) ^ 2 * (q.totient : ℝ) ^ 2 := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have he := ramanujanAutocorrelationWeight_eq_period_squares hq (range M) (fun _ => 1)
  simp only [ramanujanAutocorrelationWeight, one_mul] at he
  have hnn := ramanujanAutocorrelationWeight_nonneg (range M) (fun _ => 1) q
  simp only [ramanujanAutocorrelationWeight, one_mul] at hnn
  constructor
  · simpa only [zero_mul] using (le_div_iff₀ hφ).mp hnn
  · have hb : (∑ i ∈ range M, ∑ j ∈ range M,
          ramanujanLagCoefficient q (Nat.dist i j)) / (q.totient : ℝ) ≤
        (q : ℝ) ^ 2 * (q.totient : ℝ) := by
      calc
        _ = _ := he
        _ ≤ (1 / ((q : ℝ) * q.totient)) *
            ∑ _n ∈ range q, ((q : ℝ) * q.totient) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum
          intro n _
          have hp := lag_prefix_bound hq hq1 n M
          have ht := mul_self_le_mul_self (abs_nonneg _) hp
          simpa only [← pow_two, sq_abs] using ht
        _ = _ := by
          rw [sum_const, card_range, nsmul_eq_mul]
          field_simp [hqr.ne', hφ.ne']
    have h := (div_le_iff₀ hφ).mp hb
    nlinarith only [h]

private theorem weighted_pair_bounds {q : ℕ} (hq : 0 < q) (hq1 : q ≠ 1) (M : ℕ) :
    0 ≤ (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
      (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) ∧
    (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
      (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) ≤
        (q : ℝ) ^ 2 := by
  have hp := lag_pair_bounds hq hq1 M
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hc : 0 ≤ RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ) :=
    div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) hφ.le
  refine ⟨mul_nonneg hc hp.1, ?_⟩
  calc
    _ ≤ (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        ((q : ℝ) ^ 2 * (q.totient : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hp.2 hc
    _ ≤ _ := by
      rw [RHTower.Sieve.sqfreeTotientInv_apply]
      split_ifs with hs
      · exact le_of_eq (by field_simp [hφ.ne'])
      · simp only [zero_div, zero_mul]
        positivity

private theorem weighted_prefix_bound {q : ℕ} (hq : 0 < q) (hq1 : q ≠ 1) (M : ℕ) :
    |(RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
      (∑ i ∈ range M, ramanujanLagCoefficient q i)| ≤ (q : ℝ) := by
  have hp := lag_prefix_bound hq hq1 0 M
  simp only [Nat.zero_add] at hp
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ1 : 1 ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hc : 0 ≤ RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ) :=
    div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) hφ.le
  rw [abs_mul, abs_of_nonneg hc]
  calc
    _ ≤ (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        ((q : ℝ) * q.totient) := mul_le_mul_of_nonneg_left hp hc
    _ ≤ _ := by
      rw [RHTower.Sieve.sqfreeTotientInv_apply]
      split_ifs with hs
      · have he : (1 / (q.totient : ℝ) / (q.totient : ℝ)) *
            ((q : ℝ) * q.totient) = (q : ℝ) / q.totient := by field_simp [hφ.ne']
        rw [he]
        exact (div_le_iff₀ hφ).mpr (by nlinarith only [mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hφ1)])
      · simp only [zero_div, zero_mul]
        positivity

private theorem packet_card_le {Q : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 Q) :
    (S.card : ℝ) ≤ (Q : ℝ) := by
  have h := card_le_card hS
  have hc : (Icc 1 Q).card = Q := by simp
  rw [hc] at h
  exact_mod_cast h

private theorem odd_dist (i j : ℕ) :
    Nat.dist (2 * i + 1) (2 * j + 1) = 2 * Nat.dist i j := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le (by omega), Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega), Nat.dist_eq_sub_of_le_right h]
    omega

private theorem rectangle_packet (Q M : ℕ) :
    (∑ i ∈ range M, ∑ j ∈ range M,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) =
        2 * ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j)) := by
  simp_rw [odd_dist, parityStabilizerWeight_two_mul, parityStabilizerWeight, ← mul_sum]
  congr 1
  calc
    _ = ∑ i ∈ range M, ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), ∑ j ∈ range M,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ramanujanLagCoefficient q (Nat.dist i j) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), ∑ i ∈ range M, ∑ j ∈ range M,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ramanujanLagCoefficient q (Nat.dist i j) := by rw [sum_comm]
    _ = _ := by simp only [mul_sum]

/-- Incomplete odd-coordinate rectangles have nonnegative packet error at most `2Q³`. -/
theorem odd_stabilizer_rectangle_error {Q : ℕ} (hQ : 1 ≤ Q) (M : ℕ) :
    0 ≤ (∑ i ∈ range M, ∑ j ∈ range M,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) - 2 * (M : ℝ) ^ 2 ∧
    (∑ i ∈ range M, ∑ j ∈ range M,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) - 2 * (M : ℝ) ^ 2 ≤
        2 * (Q : ℝ) ^ 3 := by
  let S := (Icc 1 Q).filter (fun q => q % 2 = 1)
  let F := fun q => (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
    (∑ i ∈ range M, ∑ j ∈ range M, ramanujanLagCoefficient q (Nat.dist i j))
  have hone : 1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hQ⟩, by norm_num⟩
  have hF1 : F 1 = (M : ℝ) ^ 2 := by
    simp only [F, sqfreeTotientInv_one, Nat.totient_one, Nat.cast_one, div_one,
      ramanujanLagCoefficient_one, sum_const, card_range, nsmul_eq_mul, mul_one, one_mul]
    ring
  have hsplit := sum_erase_add S F hone
  rw [hF1] at hsplit
  have hb (q : ℕ) (hq : q ∈ S.erase 1) : 0 ≤ F q ∧ F q ≤ (Q : ℝ) ^ 2 := by
    have hqs := mem_erase.mp hq
    have hqi := mem_Icc.mp (mem_filter.mp hqs.2).1
    have hp := weighted_pair_bounds (by omega : 0 < q) hqs.1 M
    have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast hqi.2
    refine ⟨hp.1, hp.2.trans ?_⟩
    nlinarith only [mul_nonneg (sub_nonneg.mpr hqQ)
      (add_nonneg (Nat.cast_nonneg Q) (Nat.cast_nonneg q))]
  have hnon : 0 ≤ ∑ q ∈ S.erase 1, F q := sum_nonneg fun q hq => (hb q hq).1
  have hcard : ((S.erase 1).card : ℝ) ≤ Q :=
    packet_card_le ((erase_subset _ _).trans (filter_subset _ _))
  have hup : (∑ q ∈ S.erase 1, F q) ≤ (Q : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ _q ∈ S.erase 1, (Q : ℝ) ^ 2 := sum_le_sum fun q hq => (hb q hq).2
      _ = ((S.erase 1).card : ℝ) * (Q : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * (Q : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = _ := by ring
  rw [rectangle_packet]
  change 0 ≤ 2 * (∑ q ∈ S, F q) - 2 * (M : ℝ) ^ 2 ∧
    2 * (∑ q ∈ S, F q) - 2 * (M : ℝ) ^ 2 ≤ 2 * (Q : ℝ) ^ 3
  constructor <;> linarith only [hsplit, hnon, hup]

/-- A stabilizer row has mean two with interval-length-independent error `2Q²`. -/
theorem odd_stabilizer_row_error {Q : ℕ} (hQ : 1 ≤ Q) (M : ℕ) :
    |(∑ i ∈ range M, parityStabilizerWeight Q i) - 2 * (M : ℝ)| ≤ 2 * (Q : ℝ) ^ 2 := by
  let S := (Icc 1 Q).filter (fun q => q % 2 = 1)
  let F := fun q => (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
    (∑ i ∈ range M, ramanujanLagCoefficient q i)
  have hone : 1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hQ⟩, by norm_num⟩
  have hF1 : F 1 = (M : ℝ) := by
    simp only [F, sqfreeTotientInv_one, Nat.totient_one, Nat.cast_one, div_one,
      ramanujanLagCoefficient_one, sum_const, card_range, nsmul_eq_mul, mul_one, one_mul]
  have hsplit := sum_erase_add S F hone
  rw [hF1] at hsplit
  have he : (∑ i ∈ range M, parityStabilizerWeight Q i) - 2 * (M : ℝ) =
      2 * ∑ q ∈ S.erase 1, F q := by
    have hsum : (∑ i ∈ range M, parityStabilizerWeight Q i) = 2 * ∑ q ∈ S, F q := by
      simp only [parityStabilizerWeight, ← mul_sum]
      congr 1
      simp only [F, mul_sum]
      rw [sum_comm]
    rw [hsum]
    linarith only [hsplit]
  have hb (q : ℕ) (hq : q ∈ S.erase 1) : |F q| ≤ (Q : ℝ) := by
    have hqs := mem_erase.mp hq
    have hqi := mem_Icc.mp (mem_filter.mp hqs.2).1
    exact (weighted_prefix_bound (by omega : 0 < q) hqs.1 M).trans (by exact_mod_cast hqi.2)
  have hcard : ((S.erase 1).card : ℝ) ≤ Q :=
    packet_card_le ((erase_subset _ _).trans (filter_subset _ _))
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ q ∈ S.erase 1, |F q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ S.erase 1, (Q : ℝ) := sum_le_sum hb
    _ = ((S.erase 1).card : ℝ) * (Q : ℝ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (Q : ℝ) := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The diagonal packet mass lies between zero and `2Q`. -/
theorem odd_stabilizer_diagonal_bounds (Q : ℕ) :
    0 ≤ parityStabilizerWeight Q 0 ∧ parityStabilizerWeight Q 0 ≤ 2 * (Q : ℝ) := by
  let S := (Icc 1 Q).filter (fun q => q % 2 = 1)
  have he : parityStabilizerWeight Q 0 = 2 * ∑ q ∈ S, RHTower.Sieve.sqfreeTotientInv q := by
    unfold parityStabilizerWeight
    congr 1
    apply sum_congr rfl
    intro q hq
    have hq1 := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq1).ne'
    rw [ramanujanLagCoefficient_of_dvd hq1 (dvd_zero q)]
    exact div_mul_cancel₀ _ hφ
  have hb (q : ℕ) (hq : q ∈ S) : RHTower.Sieve.sqfreeTotientInv q ≤ 1 := by
    have hq1 := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq1
    rw [RHTower.Sieve.sqfreeTotientInv_apply]
    split_ifs
    · exact (div_le_one (by linarith)).mpr hφ
    · norm_num
  rw [he]
  constructor
  · exact mul_nonneg (by norm_num) (sum_nonneg fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ _q ∈ S, (1 : ℝ) := sum_le_sum hb
      _ = (S.card : ℝ) := by simp only [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := packet_card_le (filter_subset _ _)

/-- Removing integer one and repeated pairs costs only explicit row and diagonal errors. -/
theorem distinct_odd_stabilizer_rectangle_error {Q M : ℕ} (hQ : 1 ≤ Q) (hM : 0 < M) :
    |(∑ i ∈ (range M).erase 0, ∑ j ∈ ((range M).erase 0).erase i,
      parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) - 2 * (M : ℝ) ^ 2| ≤
        2 * (Q : ℝ) ^ 3 + 4 * (Q : ℝ) ^ 2 + 4 * M + 2 * ((M : ℝ) + 2) * Q := by
  let A := ∑ i ∈ range M, ∑ j ∈ range M,
    parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))
  let R := ∑ i ∈ range M, parityStabilizerWeight Q i
  let W := parityStabilizerWeight Q 0
  have hA : |A - 2 * (M : ℝ) ^ 2| ≤ 2 * (Q : ℝ) ^ 3 := by
    rw [abs_of_nonneg (odd_stabilizer_rectangle_error hQ M).1]
    exact (odd_stabilizer_rectangle_error hQ M).2
  have hR : |R| ≤ 2 * (Q : ℝ) ^ 2 + 2 * M := by
    calc
      _ = |(R - 2 * M) + 2 * M| := by congr 1; ring
      _ ≤ |R - 2 * M| + |2 * (M : ℝ)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (M : ℝ))]
        have hr : |R - 2 * M| ≤ 2 * (Q : ℝ) ^ 2 := odd_stabilizer_row_error hQ M
        linarith only [hr]
  have hW : |((M : ℝ) - 2) * W| ≤ ((M : ℝ) + 2) * (2 * Q) := by
    rw [abs_mul, abs_of_nonneg (odd_stabilizer_diagonal_bounds Q).1]
    have hm : |(M : ℝ) - 2| ≤ (M : ℝ) + 2 := by
      exact abs_le.mpr ⟨by linarith only [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)], by linarith⟩
    exact mul_le_mul hm (odd_stabilizer_diagonal_bounds Q).2
      (odd_stabilizer_diagonal_bounds Q).1 (by positivity)
  rw [sum_distinct_odd_stabilizer_eq Q hM]
  change |A - 2 * R - ((M : ℝ) - 2) * W - 2 * (M : ℝ) ^ 2| ≤ _
  calc
    _ = |(A - 2 * (M : ℝ) ^ 2) - 2 * R - ((M : ℝ) - 2) * W| := by congr 1; ring
    _ ≤ |A - 2 * (M : ℝ) ^ 2| + |2 * R| + |((M : ℝ) - 2) * W| :=
      by
        have h1 := abs_add_le (A - 2 * (M : ℝ) ^ 2) (-(2 * R))
        have h2 := abs_add_le ((A - 2 * (M : ℝ) ^ 2) - 2 * R) (-((M : ℝ) - 2) * W)
        rw [neg_mul] at h2
        simp only [← sub_eq_add_neg, abs_neg] at h1 h2
        linarith only [h1, h2]
    _ ≤ _ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith only [hA, hR, hW]

/-- Raw full-rectangle mean of the packet on distinct odd integers at least three. -/
def distinctOddStabilizerRectangleMean (Q M : ℕ) (β : ℝ) : ℝ :=
  (β * ∑ i ∈ (range M).erase 0, ∑ j ∈ ((range M).erase 0).erase i,
    parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))) / (2 * (M : ℝ)) ^ 2

/-- A growing conductor cutoff has the same raw mean, with explicit square-scale error. -/
theorem distinctOddStabilizerRectangleMean_square_bound {Q : ℕ} (hQ : 1 ≤ Q) (β : ℝ) :
    |distinctOddStabilizerRectangleMean Q (Q ^ 2) β - β / 2| ≤ 4 * |β| / (Q : ℝ) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := lt_of_lt_of_le (by norm_num) hq
  have hM : 0 < Q ^ 2 := pow_pos (by omega) _
  let D := ∑ i ∈ (range (Q ^ 2)).erase 0, ∑ j ∈ ((range (Q ^ 2)).erase 0).erase i,
    parityStabilizerWeight Q (Nat.dist (2 * i + 1) (2 * j + 1))
  have he : |D - 2 * (Q : ℝ) ^ 4| ≤ 16 * (Q : ℝ) ^ 3 := by
    have h := distinct_odd_stabilizer_rectangle_error hQ hM
    simp only [Nat.cast_pow] at h
    change |D - 2 * ((Q : ℝ) ^ 2) ^ 2| ≤ _ at h
    rw [show ((Q : ℝ) ^ 2) ^ 2 = (Q : ℝ) ^ 4 by ring] at h
    have h1 : (Q : ℝ) ≤ (Q : ℝ) ^ 2 := by
      nlinarith only [mul_nonneg hq0.le (sub_nonneg.mpr hq)]
    have h2 : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg (Q : ℝ)) (sub_nonneg.mpr hq)]
    nlinarith only [h, h1, h2]
  have hid : distinctOddStabilizerRectangleMean Q (Q ^ 2) β - β / 2 =
      β * (D - 2 * (Q : ℝ) ^ 4) / (4 * (Q : ℝ) ^ 4) := by
    unfold distinctOddStabilizerRectangleMean
    simp only [Nat.cast_pow]
    change β * D / (2 * (Q : ℝ) ^ 2) ^ 2 - β / 2 = _
    field_simp [hq0.ne']; ring
  rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 4 * (Q : ℝ) ^ 4)]
  calc
    _ ≤ (|β| * (16 * (Q : ℝ) ^ 3)) / (4 * (Q : ℝ) ^ 4) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (abs_nonneg β)) (by positivity)
    _ = _ := by field_simp [hq0.ne']; ring

open Filter Topology in
/-- The raw mean remains half the scalar while both conductor cutoff and interval grow. -/
theorem distinctOddStabilizerRectangleMean_square_tendsto (β : ℝ) :
    Tendsto (fun n : ℕ => distinctOddStabilizerRectangleMean (n + 1) ((n + 1) ^ 2) β)
      atTop (𝓝 (β / 2)) := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    exact tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
  have hinv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hshift
  have he : Tendsto (fun n : ℕ => 4 * |β| / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 4 * |β|)).mul hinv
    rw [mul_zero] at h
    convert h using 1
    ext n
    ring
  have hlo := (tendsto_const_nhds (x := β / 2)).sub he
  have hhi := (tendsto_const_nhds (x := β / 2)).add he
  rw [sub_zero] at hlo
  rw [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact Eventually.of_forall fun n => by
      have h := (abs_le.mp (distinctOddStabilizerRectangleMean_square_bound (by omega : 1 ≤ n + 1) β)).1
      linarith only [h]
  · exact Eventually.of_forall fun n => by
      have h := (abs_le.mp (distinctOddStabilizerRectangleMean_square_bound (by omega : 1 ≤ n + 1) β)).2
      linarith only [h]

end GaloisForLFunctions.TransThresholdPairCorrelation
