import GaloisForLFunctions.BezoutValuationIncidence.AsymmetricAdjacentDivisorTruncation
import GaloisForLFunctions.HTGeometry.ShiftPartialSummation

/-!
# Uniform adjacent-divisor compensated remainder

Independent divisor cutoffs turn the existing adjacent mean limit into a positive
power rate for every pair of positive damping parameters. The existing Abel bound
then gives a horizon-independent bound with the actual compensated kernel
`1 / (n + 1) - 1 / (T + 1)`, including its terminal correction.

This controls the adjacent correlations entering the predecessor-peak bracket.
It does not supply strict contraction of the interior martingale.
-/

open Finset RHTower Filter Topology
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem ceil_power_cutoff_bounds {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ ⌈(N : ℝ) ^ s⌉₊ ∧
      (N : ℝ) ^ s ≤ (⌈(N : ℝ) ^ s⌉₊ : ℝ) ∧
      (⌈(N : ℝ) ^ s⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ s := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := Real.one_le_rpow hN1 hs
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), Nat.le_ceil _, ?_⟩
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) s)
  linarith

/-- Positive damping gives a positive power rate for the existing adjacent mean. -/
theorem exists_pm_adjacent_divisor_mean_power_rate
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ n ∈ Icc 1 N,
          pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n) /
            (N : ℝ) - pmAdjacentDivisorDensity ε η| ≤ C * (N : ℝ) ^ (-δ) := by
  let α : ℝ := ε / (8 * (1 + ε))
  let δ : ℝ := min (α * η / 2) (min (ε / 8) (1 / 4))
  let K : ℝ → ℝ := fun e => ∑' d : ℕ, |pmPowerDampedRealWeight (e / 2) d| / (d : ℝ)
  have hK (e : ℝ) : 0 ≤ K e := tsum_nonneg fun d => div_nonneg (abs_nonneg _) (Nat.cast_nonneg d)
  have hKε := hK ε
  have hKη := hK η
  have hα : 0 < α := div_pos hε (by positivity)
  have hαε : α ≤ ε / 8 := by
    dsimp only [α]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hα4 : α ≤ 1 / 4 := by
    dsimp only [α]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hδη : δ ≤ α * η / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, by linarith, 2 * K η + 8 * K ε + 4, by positivity, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let D : ℕ := ⌈(N : ℝ) ^ α⌉₊
  let A : ℕ := ⌈(N : ℝ) ^ (1 / 2 : ℝ)⌉₊
  obtain ⟨hD1, hDlo, hDhi⟩ := ceil_power_cutoff_bounds hN hα.le
  obtain ⟨hA1, hAlo, hAhi⟩ := ceil_power_cutoff_bounds hN (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hDtail : pmPowerDampedReciprocalTail η D ≤ K η * (N : ℝ) ^ (-δ) := by
    calc
      _ ≤ (D : ℝ) ^ (-η / 2) * K η :=
        pmPowerDampedReciprocalTail_le_half_exponent_moment hη hD1
      _ ≤ ((N : ℝ) ^ α) ^ (-η / 2) * K η :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNR α) hDlo (by linarith))
          (hK η)
      _ = K η * (N : ℝ) ^ (-(α * η / 2)) := by
        rw [← Real.rpow_mul hNR.le]
        have he : α * (-η / 2) = -(α * η / 2) := by ring
        rw [he, mul_comm]
      _ ≤ K η * (N : ℝ) ^ (-δ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (hK η)
  have hAtail : pmPowerDampedReciprocalTail ε A ≤ K ε * (N : ℝ) ^ (-ε / 4) := by
    calc
      _ ≤ (A : ℝ) ^ (-ε / 2) * K ε :=
        pmPowerDampedReciprocalTail_le_half_exponent_moment hε hA1
      _ ≤ ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (-ε / 2) * K ε :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNR (1 / 2)) hAlo (by linarith))
          (hK ε)
      _ = _ := by
        rw [← Real.rpow_mul hNR.le]
        have he : (1 / 2 : ℝ) * (-ε / 2) = -ε / 4 := by ring
        rw [he, mul_comm]
  have hmiddle : 4 * (D : ℝ) * pmPowerDampedReciprocalTail ε A ≤
      8 * K ε * (N : ℝ) ^ (-δ) := by
    calc
      _ ≤ 4 * (D : ℝ) * (K ε * (N : ℝ) ^ (-ε / 4)) :=
        mul_le_mul_of_nonneg_left hAtail (by positivity)
      _ ≤ 4 * (2 * (N : ℝ) ^ α) * (K ε * (N : ℝ) ^ (-ε / 4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDhi (by norm_num)) (by positivity)
      _ = 8 * K ε * ((N : ℝ) ^ α * (N : ℝ) ^ (-ε / 4)) := by ring
      _ = 8 * K ε * (N : ℝ) ^ (α - ε / 4) := by
        rw [← Real.rpow_add hNR]
        have he : α + (-ε / 4) = α - ε / 4 := by ring
        rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity)
  have hhead : ((D : ℝ) * A) / (N : ℝ) ≤ 4 * (N : ℝ) ^ (-δ) := by
    calc
      _ ≤ ((2 * (N : ℝ) ^ α) * (2 * (N : ℝ) ^ (1 / 2 : ℝ))) / (N : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hDhi hAhi (Nat.cast_nonneg A) (by positivity)) hNR.le
      _ = 4 * ((N : ℝ) ^ α * (N : ℝ) ^ (1 / 2 : ℝ)) / (N : ℝ) := by ring
      _ = 4 * ((N : ℝ) ^ (α + 1 / 2) / N) := by rw [← Real.rpow_add hNR]; ring
      _ = 4 * (N : ℝ) ^ (α - 1 / 2) := by
        rw [← Real.rpow_sub_one hNR.ne']
        have he : (α + 1 / 2) - 1 = α - 1 / 2 := by ring
        rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num)
  calc
    _ ≤ 2 * pmPowerDampedReciprocalTail η D +
        4 * (D : ℝ) * pmPowerDampedReciprocalTail ε A + ((D : ℝ) * A) / (N : ℝ) :=
      abs_pm_adjacent_divisor_mean_sub_density_le_cutoff_sizes hε hη D A hN
    _ ≤ 2 * (K η * (N : ℝ) ^ (-δ)) +
        8 * K ε * (N : ℝ) ^ (-δ) + 4 * (N : ℝ) ^ (-δ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hDtail (by norm_num)) hmiddle) hhead
    _ = _ := by ring

private theorem exists_adjacent_centered_sum_power_bound
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |∑ n ∈ Icc 1 N,
        (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n -
          pmAdjacentDivisorDensity ε η)| ≤ B * (N : ℝ) ^ a := by
  obtain ⟨δ, hδ, hδ1, C, hC, hbound⟩ := exists_pm_adjacent_divisor_mean_power_rate hε hη
  refine ⟨1 - δ, by linarith, by linarith, C, hC, fun N => ?_⟩
  by_cases hN : N = 0
  · subst N
    simpa using mul_nonneg hC (Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) (1 - δ))
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsum :
      (∑ n ∈ Icc 1 N,
        (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n -
          pmAdjacentDivisorDensity ε η)) =
      (∑ n ∈ Icc 1 N,
        pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n) -
          (N : ℝ) * pmAdjacentDivisorDensity ε η := by
    rw [sum_sub_distrib]
    simp
  have he :
      (∑ n ∈ Icc 1 N,
        pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n) /
          (N : ℝ) - pmAdjacentDivisorDensity ε η =
      (∑ n ∈ Icc 1 N,
        (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n -
          pmAdjacentDivisorDensity ε η)) / (N : ℝ) := by
    rw [hsum]
    field_simp
  have hm := hbound N hN1
  have hNabs : |(N : ℝ)| = N := abs_of_pos hNR
  rw [he, abs_div, hNabs] at hm
  calc
    _ ≤ (C * (N : ℝ) ^ (-δ)) * N := (div_le_iff₀ hNR).mp hm
    _ = C * ((N : ℝ) ^ (-δ) * (N : ℝ) ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = C * (N : ℝ) ^ (-δ + 1) := by rw [← Real.rpow_add hNR]
    _ = _ := by
      have he : -δ + 1 = 1 - δ := by ring
      rw [he]

private theorem power_boundary_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (T : ℕ) :
    (T : ℝ) ^ a / ((T : ℝ) + 1) ≤ 1 := by
  have hpow : (T : ℝ) ^ a ≤ (T : ℝ) + 1 := by
    by_cases hT : T = 0
    · subst T
      simp [Real.zero_rpow ha0.ne']
    · have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
      have hh : (T : ℝ) ^ a ≤ T := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1 ha1.le
      linarith
  exact (div_le_iff₀ (by positivity)).mpr (by simpa using hpow)

private theorem exists_compensated_range_bound_of_partial_power
    {f : ℕ → ℝ} {B a : ℝ} (hB : 0 ≤ B) (ha0 : 0 < a) (ha1 : a < 1)
    (hS : ∀ T : ℕ, |HTGeometry.partialSum f T| ≤ B * (T : ℝ) ^ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |∑ n ∈ range T, f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))| ≤ C := by
  let inc : ℕ → ℝ := fun j =>
    ((j : ℝ) + 1) ^ a * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
  let I : ℝ := ∑' j : ℕ, inc j
  have hi0 (j : ℕ) : 0 ≤ inc j := by dsimp only [inc]; positivity
  have hI : 0 ≤ I := tsum_nonneg hi0
  have hs : Summable inc := HTGeometry.summable_increment ha1
  refine ⟨B * (2 + I), mul_nonneg hB (by linarith), fun T => ?_⟩
  have hboundary : B * (T : ℝ) ^ a * (1 / ((T : ℝ) + 1)) ≤ B := by
    calc
      _ = B * ((T : ℝ) ^ a / ((T : ℝ) + 1)) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left (power_boundary_le ha0 ha1 T) hB
      _ = _ := mul_one _
  have hsum :
      (∑ j ∈ range T, B * ((j : ℝ) + 1) ^ a *
        (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) ≤ B * I := by
    calc
      _ = ∑ j ∈ range T, B * inc j := by
        apply sum_congr rfl
        intro j _
        dsimp only [inc]
        ring
      _ ≤ ∑' j : ℕ, B * inc j :=
        sum_le_hasSum (range T) (fun j _ => mul_nonneg hB (hi0 j)) (hs.mul_left B).hasSum
      _ = _ := by rw [tsum_mul_left]
  have hH : |∑ n ∈ range T, f n * (1 / ((n : ℝ) + 1))| ≤ B + B * I :=
    (HTGeometry.abel_bound_of_partialSum_le hS T).trans (add_le_add hboundary hsum)
  have hterminal : |HTGeometry.partialSum f T * (1 / ((T : ℝ) + 1))| ≤ B := by
    have hw : |1 / ((T : ℝ) + 1)| = 1 / ((T : ℝ) + 1) := abs_of_pos (by positivity)
    rw [abs_mul, hw]
    exact (mul_le_mul_of_nonneg_right (hS T) (by positivity)).trans hboundary
  have he :
      (∑ n ∈ range T, f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
        (∑ n ∈ range T, f n * (1 / ((n : ℝ) + 1))) -
          HTGeometry.partialSum f T * (1 / ((T : ℝ) + 1)) := by
    simp only [HTGeometry.partialSum, mul_sub, sum_sub_distrib, sum_mul]
  rw [he]
  calc
    _ ≤ |∑ n ∈ range T, f n * (1 / ((n : ℝ) + 1))| +
        |HTGeometry.partialSum f T * (1 / ((T : ℝ) + 1))| := abs_sub _ _
    _ ≤ (B + B * I) + B := add_le_add hH hterminal
    _ = _ := by ring

private theorem sum_range_eq_sum_Icc_pred_of_zero {f : ℕ → ℝ}
    (hf0 : f 0 = 0) (T : ℕ) :
    (∑ n ∈ range T, f n) = ∑ n ∈ Icc 1 (T - 1), f n := by
  by_cases hT : T = 0
  · subst T
    simp
  have hset : range T = insert 0 (Icc 1 (T - 1)) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp), hf0, zero_add]

/-- The centered adjacent field has a uniform compensated harmonic bound
for every pair of positive damping parameters. -/
theorem exists_pm_adjacent_divisor_compensated_bound
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |∑ n ∈ Icc 1 (T - 1),
        (pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n -
          pmAdjacentDivisorDensity ε η) *
            (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))| ≤ C := by
  obtain ⟨a, ha0, ha1, B, hB, hprefix⟩ := exists_adjacent_centered_sum_power_bound hε hη
  let q : ℕ → ℝ := fun n =>
    pmPowerDampedDivisorCoeff ε (n + 1) * pmPowerDampedDivisorCoeff η n -
      pmAdjacentDivisorDensity ε η
  let f : ℕ → ℝ := fun n => if n = 0 then 0 else q n
  have hf0 : f 0 = 0 := by simp only [f, if_pos rfl]
  have hIcc (T : ℕ) : (∑ n ∈ Icc 1 (T - 1), f n) = ∑ n ∈ Icc 1 (T - 1), q n := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp only [f, if_neg hn0]
  have hS (T : ℕ) : |HTGeometry.partialSum f T| ≤ B * (T : ℝ) ^ a := by
    rw [HTGeometry.partialSum, sum_range_eq_sum_Icc_pred_of_zero hf0, hIcc]
    exact (hprefix (T - 1)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.sub_le T 1) ha0.le) hB)
  obtain ⟨C, hC, hbound⟩ := exists_compensated_range_bound_of_partial_power hB ha0 ha1 hS
  refine ⟨C, hC, fun T => ?_⟩
  have hz : f 0 * (1 / ((0 : ℝ) + 1) - 1 / ((T : ℝ) + 1)) = 0 := by
    rw [hf0, zero_mul]
  have hh := hbound T
  rw [sum_range_eq_sum_Icc_pred_of_zero
    (f := fun n : ℕ => f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)))
    (by simpa only [Nat.cast_zero] using hz)] at hh
  have he :
      (∑ n ∈ Icc 1 (T - 1), f n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1))) =
        ∑ n ∈ Icc 1 (T - 1), q n * (1 / ((n : ℝ) + 1) - 1 / ((T : ℝ) + 1)) := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp only [f, if_neg hn0]
  rw [he] at hh
  exact hh

end GaloisForLFunctions.BezoutValuationIncidence
