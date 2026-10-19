import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDyadicRampAndQuadraticTraceLoss
import GaloisForLFunctions.TransHorizonIncidenceMechanics.NonnegativeWeightEndpointOrderAndCalibratedDefect
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Nonnegative dyadic ramps

Deleting the negative endpoint of the signed coefficient ramp preserves its
cubic sieve energy. The resulting coefficients are explicitly nonnegative.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem column_telescope (K : ℕ) (f e : ℕ → ℝ) :
    (∑ k ∈ Finset.range (K + 1), (f k * e (k + 1) - f k * e (k + 2))) +
        f K * e (K + 2) =
      f 0 * e 1 + ∑ k ∈ Finset.range K, (f (k + 1) - f k) * e (k + 2) := by
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_succ' (fun k => f k * e (k + 1)) K,
    Finset.sum_range_succ (fun k => f k * e (k + 2)) K]
  have hsum : (∑ k ∈ Finset.range K, (f (k + 1) - f k) * e (k + 2)) =
      (∑ k ∈ Finset.range K, f (k + 1) * e (k + 2)) -
        ∑ k ∈ Finset.range K, f k * e (k + 2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  simp only [show ∀ k : ℕ, k + 1 + 1 = k + 2 by intro k; omega, Nat.zero_add]
  ring

/-- The signed ramp with its final negative endpoint removed, in manifestly nonnegative form. -/
def fermiNonnegativeDyadicRampWeight (K d : ℕ) : ℝ :=
  (if d = 2 then 2 * ((K : ℝ) + 1) else 0) +
    ∑ k ∈ Finset.range K,
      if d = 2 ^ (k + 2) then (2 : ℝ) ^ (k + 1) * ((K : ℝ) - k - 1) else 0

/-- Every coefficient of the modified ramp is nonnegative. -/
theorem fermiNonnegativeDyadicRampWeight_nonneg (K d : ℕ) :
    0 ≤ fermiNonnegativeDyadicRampWeight K d := by
  unfold fermiNonnegativeDyadicRampWeight
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro k hk
    have hkn : k + 1 ≤ K := by have h := Finset.mem_range.mp hk; omega
    have hkR : (k : ℝ) + 1 ≤ K := by exact_mod_cast hkn
    split_ifs
    · exact mul_nonneg (by positivity) (by linarith)
    · exact le_refl 0

private theorem positive_ramp_eq (K d : ℕ) :
    fermiNonnegativeDyadicRampWeight K d = fermiDyadicRampWeight (K + 1) d +
      if d = 2 ^ (K + 2) then (2 : ℝ) ^ (K + 1) else 0 := by
  let f (k : ℕ) : ℝ := 2 ^ (k + 1) * (((K + 1 : ℕ) : ℝ) - k)
  let e (j : ℕ) : ℝ := if d = 2 ^ j then 1 else 0
  have hf0 : f 0 = 2 * ((K : ℝ) + 1) := by simp [f]
  have hfK : f K = 2 ^ (K + 1) := by simp [f]
  have hdiff (k : ℕ) : f (k + 1) - f k =
      (2 : ℝ) ^ (k + 1) * ((K : ℝ) - k - 1) := by
    dsimp [f]
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have hcol : fermiDyadicRampWeight (K + 1) d =
      ∑ k ∈ Finset.range (K + 1), (f k * e (k + 1) - f k * e (k + 2)) := by
    change (∑ k ∈ Finset.range (K + 1),
      ((if d = 2 ^ (k + 1) then f k else 0) -
        (if d = 2 ^ (k + 2) then f k else 0))) = _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [e]
    split_ifs <;> ring
  have hhead : f 0 * e 1 = if d = 2 then 2 * ((K : ℝ) + 1) else 0 := by
    rw [hf0]
    dsimp [e]
    split_ifs <;> ring
  have hlast : f K * e (K + 2) =
      if d = 2 ^ (K + 2) then (2 : ℝ) ^ (K + 1) else 0 := by
    rw [hfK]
    dsimp [e]
    split_ifs <;> ring
  have htail : (∑ k ∈ Finset.range K, (f (k + 1) - f k) * e (k + 2)) =
      ∑ k ∈ Finset.range K,
        if d = 2 ^ (k + 2) then (2 : ℝ) ^ (k + 1) * ((K : ℝ) - k - 1) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hdiff]
    dsimp [e]
    split_ifs <;> ring
  have h := column_telescope K f e
  rw [← hcol, hhead, hlast, htail] at h
  exact h.symm

private theorem positive_sieve_eq (K n : ℕ) :
    sieveSeq (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) n =
      sieveSeq (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) n +
        if 2 ^ (K + 2) ∣ n then (2 : ℝ) ^ (K + 1) else 0 := by
  unfold sieveSeq
  simp_rw [positive_ramp_eq]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hp : 0 < (2 : ℕ) ^ (K + 2) := by positivity
  simp only [Finset.mem_filter, Finset.mem_Icc, le_refl,
    show 1 ≤ 2 ^ (K + 2) by omega, true_and]

private theorem signed_ramp_zero_on_endpoint_multiples {K n : ℕ} (hn : 2 ^ (K + 2) ∣ n) :
    sieveSeq (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) n = 0 := by
  unfold sieveSeq fermiDyadicRampWeight
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hkK := Finset.mem_range.mp hk
  have hp1 : 0 < (2 : ℕ) ^ (k + 1) := by positivity
  have hp2 : 0 < (2 : ℕ) ^ (k + 2) := by positivity
  have hb1 : (2 : ℕ) ^ (k + 1) ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hb2 : (2 : ℕ) ^ (k + 2) ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hd1 : (2 : ℕ) ^ (k + 1) ∣ n := dvd_trans (pow_dvd_pow 2 (by omega)) hn
  have hd2 : (2 : ℕ) ^ (k + 2) ∣ n := dvd_trans (pow_dvd_pow 2 (by omega)) hn
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc,
    show 1 ≤ 2 ^ (k + 1) by omega, show 1 ≤ 2 ^ (k + 2) by omega, hb1, hb2,
    hd1, hd2, true_and, if_true, sub_self]

private theorem positive_sieve_energy_ge (K : ℕ) :
    sieveTotalPronicEnergy (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) ≤
      sieveTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) := by
  have hsq (n : ℕ) : sieveSeq (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) n ^ 2 ≤
      sieveSeq (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) n ^ 2 := by
    by_cases hn : 2 ^ (K + 2) ∣ n
    · rw [signed_ramp_zero_on_endpoint_multiples hn, zero_pow (by omega : 2 ≠ 0)]
      exact sq_nonneg _
    · rw [positive_sieve_eq, if_neg hn, add_zero]
  have hcell (m : ℕ) :
      sievePairedPronicEnergy (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) {m} ≤
        sievePairedPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) {m} := by
    simp only [sievePairedPronicEnergy, Finset.sum_singleton]
    exact add_le_add (div_le_div_of_nonneg_right (hsq (2 * m + 1)) (by positivity))
      (div_le_div_of_nonneg_right (hsq (2 * m + 2)) (by positivity))
  exact Summable.tsum_le_tsum hcell
    (sieve_fermi_pronic_summable (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1))).1
    (sieve_fermi_pronic_summable (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K)).1

/-- Nonnegative coefficients retain the signed ramp's cubic lower sieve energy. -/
theorem fermiNonnegativeDyadicRamp_pronic_lower (K : ℕ) :
    ((K : ℝ) + 1) * (K + 2) * (2 * K + 3) / 12 ≤
      sieveTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) := by
  have h := (fermiDyadicRamp_pronic_bounds (K + 1)).1.trans (positive_sieve_energy_ge K)
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  nlinarith

private def endpointCorrection (K m : ℕ) : ℝ :=
  2 * (if 2 ^ (K + 2) ∣ 2 * m + 2 then (2 : ℝ) ^ (K + 1) else 0) -
    (if 2 ^ (K + 2) ∣ 4 * m + 4 then (2 : ℝ) ^ (K + 1) else 0)

private theorem endpointCorrection_sq (K m : ℕ) :
    endpointCorrection K m ^ 2 =
      if 2 ^ K ∣ m + 1 then ((2 : ℝ) ^ (K + 1)) ^ 2 else 0 := by
  have h1 : 2 ^ (K + 2) ∣ 2 * m + 2 ↔ 2 ^ (K + 1) ∣ m + 1 := by
    rw [show 2 ^ (K + 2) = 2 * (2 : ℕ) ^ (K + 1) by simp only [pow_succ'],
      show 2 * m + 2 = 2 * (m + 1) by omega,
      Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)]
  have h2 : 2 ^ (K + 2) ∣ 4 * m + 4 ↔ 2 ^ K ∣ m + 1 := by
    rw [show 2 ^ (K + 2) = 4 * (2 : ℕ) ^ K by simp only [pow_succ]; ring,
      show 4 * m + 4 = 4 * (m + 1) by omega,
      Nat.mul_dvd_mul_iff_left (by omega : 0 < 4)]
  unfold endpointCorrection
  simp only [h1, h2]
  by_cases h : 2 ^ K ∣ m + 1
  · by_cases hh : 2 ^ (K + 1) ∣ m + 1
    · simp only [if_pos h, if_pos hh]
      ring
    · simp only [if_pos h, if_neg hh]
      ring
  · have hh : ¬ 2 ^ (K + 1) ∣ m + 1 :=
      fun hd => h (dvd_trans (pow_dvd_pow 2 (by omega)) hd)
    simp only [if_neg h, if_neg hh]
    ring

private theorem endpoint_weight_eq (K m : ℕ) :
    endpointCorrection K m ^ 2 / (pronicSeq (4 * m + 4) : ℝ) =
      if 2 ^ K ∣ m + 1 then ((2 : ℝ) ^ (K + 1)) ^ 2 /
        (pronicSeq (4 * (m + 1)) : ℝ) else 0 := by
  rw [endpointCorrection_sq]
  by_cases h : 2 ^ K ∣ m + 1
  · simp only [if_pos h, show 4 * m + 4 = 4 * (m + 1) by omega]
  · simp only [if_neg h, zero_div]

private theorem endpoint_scaled_weight_le (K t : ℕ) (ht : 1 ≤ t) :
    ((2 : ℝ) ^ (K + 1)) ^ 2 / (pronicSeq (4 * (2 ^ K * t)) : ℝ) ≤
      (1 / 4 : ℝ) * (1 / (t : ℝ) ^ 2) := by
  let B : ℝ := 2 ^ (K + 1)
  have hB : 0 < B := by positivity
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hden : (pronicSeq (4 * (2 ^ K * t)) : ℝ) =
      (2 * B * t) * (2 * B * t + 1) := by
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_pow, Nat.cast_ofNat, B, pow_succ]
    ring
  rw [hden]
  calc
    _ ≤ 1 / (4 * (t : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hB.le ht0.le]
    _ = _ := by ring

private theorem endpoint_partial_energy_le (K M : ℕ) :
    (∑ m ∈ Finset.range M, endpointCorrection K m ^ 2 /
      (pronicSeq (4 * m + 4) : ℝ)) ≤ 1 / 2 := by
  simp_rw [endpoint_weight_eq]
  rw [← sum_Icc_eq_sum_range_succ (fun j : ℕ =>
    if 2 ^ K ∣ j then ((2 : ℝ) ^ (K + 1)) ^ 2 / (pronicSeq (4 * j) : ℝ) else 0) M]
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_eq_sum_Icc_div (by positivity)]
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 (M / 2 ^ K), (1 / 4 : ℝ) * (1 / (t : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun t ht => endpoint_scaled_weight_le K t (Finset.mem_Icc.mp ht).1)
    _ = (1 / 4 : ℝ) * ∑ t ∈ Finset.Icc 1 (M / 2 ^ K), 1 / (t : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 4 : ℝ) * 2 := mul_le_mul_of_nonneg_left
      (RHTower.Sieve.sum_inv_sq_le_two (M / 2 ^ K)) (by norm_num)
    _ = 1 / 2 := by norm_num

private theorem positive_odd_jump (K m : ℕ) :
    fermiBoundaryJump (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) (2 * m + 1) =
      fermiBoundaryJump (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) (2 * m + 1) := by
  have hn : ¬ 2 ^ (K + 2) ∣ 2 * m + 1 := by
    intro h
    have hp : (2 : ℕ) ^ 1 ∣ 2 ^ (K + 2) := pow_dvd_pow 2 (by omega)
    have hh := dvd_trans hp h
    norm_num only [pow_one] at hh
    omega
  rw [fermiBoundaryJump_odd, fermiBoundaryJump_odd, positive_sieve_eq, if_neg hn, add_zero]

private theorem positive_even_jump (K m : ℕ) :
    fermiBoundaryJump (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) (4 * m + 4) =
      fermiBoundaryJump (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) (4 * m + 4) +
        endpointCorrection K m := by
  have hp := fermiBoundaryJump_even (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) (2 * m + 1)
  have hs := fermiBoundaryJump_even (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) (2 * m + 1)
  rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 by omega,
    show 2 * m + 1 + 1 = 2 * m + 2 by omega] at hp hs
  rw [hp, hs, positive_sieve_eq, positive_sieve_eq]
  unfold endpointCorrection
  ring

private theorem positive_selected_cell_le (K m : ℕ) :
    fermiSelectedPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) {m} ≤
      2 * fermiSelectedPronicEnergy (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) {m} +
        2 * (endpointCorrection K m ^ 2 / (pronicSeq (4 * m + 4) : ℝ)) := by
  simp only [fermiSelectedPronicEnergy, Finset.sum_singleton, positive_odd_jump, positive_even_jump]
  let a := fermiBoundaryJump (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) (2 * m + 1)
  let b := fermiBoundaryJump (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) (4 * m + 4)
  let d := endpointCorrection K m
  let w1 : ℝ := pronicSeq (2 * m + 1)
  let w2 : ℝ := pronicSeq (4 * m + 4)
  change a ^ 2 / w1 + (b + d) ^ 2 / w2 ≤
    2 * (a ^ 2 / w1 + b ^ 2 / w2) + 2 * (d ^ 2 / w2)
  have hw2 : 0 ≤ w2 := by dsimp [w2]; positivity
  have ho : 0 ≤ a ^ 2 / w1 := by dsimp [w1]; positivity
  have hd : (b + d) ^ 2 / w2 ≤ 2 * (b ^ 2 / w2) + 2 * (d ^ 2 / w2) := by
    calc
      _ ≤ (2 * b ^ 2 + 2 * d ^ 2) / w2 :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (b - d)]) hw2
      _ = _ := by ring
  nlinarith

private theorem positive_selected_total_le (K : ℕ) :
    fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) ≤
      2 * fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) + 1 := by
  change (∑' m : ℕ, fermiSelectedPronicEnergy (2 ^ (K + 2))
    (fermiNonnegativeDyadicRampWeight K) {m}) ≤ _
  apply Real.tsum_le_of_sum_range_le
    (fun m => by simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]; positivity)
  intro M
  have hp := Finset.sum_le_sum (s := Finset.range M) (fun m _ => positive_selected_cell_le K m)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  have hs := Summable.sum_le_tsum (Finset.range M)
    (fun m _ => by simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]; positivity)
    (sieve_fermi_pronic_summable (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1))).2
  change (∑ m ∈ Finset.range M, fermiSelectedPronicEnergy (2 ^ (K + 2))
    (fermiDyadicRampWeight (K + 1)) {m}) ≤
      fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) at hs
  have he := endpoint_partial_energy_le K M
  nlinarith

/-- The nonnegative ramp's complete selected energy grows at most linearly. -/
theorem fermiNonnegativeDyadicRamp_selected_upper (K : ℕ) :
    fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) ≤
      4 * (K : ℝ) + 5 := by
  have h := positive_selected_total_le K
  have hq := (fermiDyadicRamp_pronic_bounds (K + 1)).2
  norm_num only [Nat.cast_add, Nat.cast_one] at hq
  change fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiDyadicRampWeight (K + 1)) ≤
    2 * ((K : ℝ) + 1) at hq
  nlinarith

/-- The quadratic lower loss remains nonvacuous inside the nonnegative coefficient cone. -/
theorem fermiNonnegativeDyadicRamp_selected_pos (K : ℕ) :
    0 < fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) := by
  let D := Nat.log 2 (2 ^ (K + 2)) + 1
  have hp : 0 < sieveTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) :=
    lt_of_lt_of_le (by positivity) (fermiNonnegativeDyadicRamp_pronic_lower K)
  have hu := sieveTotalPronicEnergy_le_depth_selected (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K)
  change sieveTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) ≤
    (((D : ℝ) + 4) * ((D : ℝ) + 1)) *
      fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) at hu
  by_contra hq
  have hD : 0 ≤ ((D : ℝ) + 4) * ((D : ℝ) + 1) := by positivity
  have hneg : 0 ≤ -fermiSelectedTotalPronicEnergy (2 ^ (K + 2))
      (fermiNonnegativeDyadicRampWeight K) := by linarith
  nlinarith [mul_nonneg hD hneg]

/-- Nonnegative coefficients already force quadratic physical inverse loss. -/
theorem fermiNonnegativeDyadicRamp_quadratic_loss (K : ℕ) :
    (((K : ℝ) + 2) * (2 * K + 3) / 60) *
        fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) ≤
      sieveTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) := by
  have hQ : fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) ≤
      5 * ((K : ℝ) + 1) := by
    nlinarith [fermiNonnegativeDyadicRamp_selected_upper K, show (0 : ℝ) ≤ K by positivity]
  calc
    _ ≤ (((K : ℝ) + 2) * (2 * K + 3) / 60) * (5 * (K + 1)) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = ((K : ℝ) + 1) * (K + 2) * (2 * K + 3) / 12 := by ring
    _ ≤ _ := fermiNonnegativeDyadicRamp_pronic_lower K

/-- Even nonnegative divisor coefficients admit no horizon-independent physical inverse bound. -/
theorem fermiSelectedTotal_no_uniform_nonnegative_inverse :
    ¬ ∃ C : ℝ, ∀ (N : ℕ) (c : ℕ → ℝ), (∀ d, 0 ≤ c d) →
      sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    by_contra hc
    have hl := fermiNonnegativeDyadicRamp_pronic_lower 0
    norm_num only [Nat.cast_zero] at hl
    have hb := hC 4 (fermiNonnegativeDyadicRampWeight 0)
      (fun d => fermiNonnegativeDyadicRampWeight_nonneg 0 d)
    have hp : 0 < fermiSelectedTotalPronicEnergy 4 (fermiNonnegativeDyadicRampWeight 0) :=
      fermiNonnegativeDyadicRamp_selected_pos 0
    nlinarith [mul_nonneg (show 0 ≤ -C by linarith) hp.le]
  obtain ⟨K, hK⟩ := exists_nat_gt (60 * C + 1)
  have hQ : fermiSelectedTotalPronicEnergy (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K) ≤
      5 * ((K : ℝ) + 1) := by
    nlinarith [fermiNonnegativeDyadicRamp_selected_upper K, show (0 : ℝ) ≤ K by positivity]
  have hu := (hC (2 ^ (K + 2)) (fermiNonnegativeDyadicRampWeight K)
    (fun d => fermiNonnegativeDyadicRampWeight_nonneg K d)).trans (mul_le_mul_of_nonneg_left hQ hC0)
  have hl := fermiNonnegativeDyadicRamp_pronic_lower K
  have hgap : 0 < ((K : ℝ) + 2) * (2 * K + 3) - 60 * C := by
    nlinarith [sq_nonneg (K : ℝ)]
  nlinarith [mul_pos (show (0 : ℝ) < K + 1 by positivity) hgap]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
