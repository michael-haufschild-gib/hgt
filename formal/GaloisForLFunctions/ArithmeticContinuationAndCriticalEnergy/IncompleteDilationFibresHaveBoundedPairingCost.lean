import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePronicPairingHasExactDilationBlocks
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheMaxKernelFormOfTheDampingAutocorrelation

/-!
# Incomplete dilation fibres have bounded pairing cost

The mixed pronic pairing differs from its contracted-horizon value by one
explicit terminal fibre. Linear row bounds C and D bound its cost by C*D/p,
uniformly in the observation horizon, including a zero quotient.
-/

noncomputable section
set_option autoImplicit false
open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

/-- The only discrepancy from a complete dilation block is its final constant fibre. -/
theorem pronicPairing_rowDilate_horizon_remainder {p : ℕ} (hp : 1 ≤ p)
    (T : ℕ) (u v : ℕ → ℝ) (hu0 : u 0 = 0) :
    (1 / (p : ℝ)) * pronicPairing (T / p) u v -
      pronicPairing T (rowDilate p u) (rowDilate p v) =
      u (T / p) * v (T / p) *
        ∑ n ∈ Icc (T + 1) (p * (T / p + 1) - 1),
          1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  let N := T / p
  let U := p * (N + 1) - 1
  have htop : T ≤ U := by
    have hlt : T < (N + 1) * p :=
      (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self N)
    rw [Nat.mul_comm] at hlt
    dsimp only [U]
    omega
  have hdiv (n : ℕ) (hn : n ∈ Icc (T + 1) U) : n / p = N := by
    have hnlo := (mem_Icc.mp hn).1
    have hnhi := (mem_Icc.mp hn).2
    have hlo : N ≤ n / p := Nat.div_le_div_right (by omega : T ≤ n)
    have hhi : n / p < N + 1 := (Nat.div_lt_iff_lt_mul hp).mpr (by
      have hpos : 0 < p * (N + 1) := Nat.mul_pos hp (Nat.succ_pos _)
      dsimp only [U] at hnhi
      rw [Nat.mul_comm]
      omega)
    omega
  rw [← pronicPairing_rowDilate_complete_blocks hp (T / p) u v hu0]
  change pronicPairing U (rowDilate p u) (rowDilate p v) -
    pronicPairing T (rowDilate p u) (rowDilate p v) = _
  rw [pronicPairing, pronicPairing, ← sum_sdiff (Icc_subset_Icc_right htop)]
  have hset : Icc 1 U \ Icc 1 T = Icc (T + 1) U := by
    ext n
    simp only [mem_sdiff, mem_Icc]
    omega
  rw [hset, add_sub_cancel_right, mul_sum]
  exact sum_congr rfl fun n hn => by
    simp only [rowDilate, hdiv n hn]
    ring

/-- Exact mixed dilation pairing, including the incomplete terminal fibre and zero quotient. -/
theorem pronicPairing_rowDilate_eq_horizon_correction {p : ℕ} (hp : 1 ≤ p)
    (T : ℕ) (u v : ℕ → ℝ) (hu0 : u 0 = 0) :
    pronicPairing T (rowDilate p u) (rowDilate p v) =
      (1 / (p : ℝ)) * pronicPairing (T / p) u v -
        u (T / p) * v (T / p) *
          (1 / ((T : ℝ) + 1) -
            1 / ((p : ℝ) * (((T / p : ℕ) : ℝ) + 1))) := by
  have h := pronicPairing_rowDilate_horizon_remainder hp T u v hu0
  have hpos : 0 < p * (T / p + 1) := Nat.mul_pos hp (Nat.succ_pos _)
  have htop : T + 1 ≤ p * (T / p + 1) := by
    have hlt : T < (T / p + 1) * p :=
      (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (T / p))
    exact Nat.succ_le_of_lt (by simpa only [Nat.mul_comm] using hlt)
  have hend : p * (T / p + 1) - 1 + 1 = p * (T / p + 1) :=
    Nat.sub_add_cancel hpos
  have hcast : ((p * (T / p + 1) - 1 : ℕ) : ℝ) + 1 =
      (p : ℝ) * (((T / p : ℕ) : ℝ) + 1) := by exact_mod_cast hend
  have hmass := sum_Icc_pronic_tail_mass (N := T + 1)
    (T := p * (T / p + 1) - 1) (Nat.succ_pos T) (by omega)
  rw [Nat.cast_add, Nat.cast_one, hcast] at hmass
  rw [hmass] at h
  linarith only [h]

/-- The incomplete terminal fibre has a horizon-independent cost for linearly bounded rows. -/
theorem abs_pronicPairing_rowDilate_horizon_error_of_bounds {p : ℕ} (hp : 1 ≤ p)
    (T : ℕ) (u v : ℕ → ℝ) (hu0 : u 0 = 0)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∀ n, |u n| ≤ C * (n : ℝ)) (hv : ∀ n, |v n| ≤ D * (n : ℝ)) :
    |pronicPairing T (rowDilate p u) (rowDilate p v) -
      (1 / (p : ℝ)) * pronicPairing (T / p) u v| ≤ C * D / (p : ℝ) := by
  let N := T / p
  let U := p * (N + 1) - 1
  let S := Icc (T + 1) U
  rw [abs_sub_comm, pronicPairing_rowDilate_horizon_remainder hp T u v hu0]
  change |u N * v N * (∑ n ∈ S, 1 / ((n : ℝ) * ((n : ℝ) + 1)))| ≤ _
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [hN, hu0, zero_mul, zero_mul, abs_zero]
    positivity
  · have hSN : S ⊆ Icc (p * N) (p * N + p - 1) := by
      intro n hn
      have hnlo := (mem_Icc.mp hn).1
      have hlo : p * N ≤ n := (Nat.mul_div_le T p).trans (by omega : T ≤ n)
      have hnU := (mem_Icc.mp hn).2
      have hid : U = p * N + p - 1 := by dsimp only [U]; rw [Nat.mul_add, Nat.mul_one]
      rw [hid] at hnU
      exact mem_Icc.mpr ⟨hlo, hnU⟩
    have hmass0 : 0 ≤ ∑ n ∈ S, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_nonneg
      intro n _
      positivity
    have hmass : (∑ n ∈ S, 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        1 / ((p : ℝ) * ((N : ℝ) * ((N : ℝ) + 1))) := by
      rw [← sum_Icc_pronic_dilation_fibre hp hN]
      exact sum_le_sum_of_subset_of_nonneg hSN (fun _ _ _ => by positivity)
    have hprod : |u N * v N| ≤ (C * D) * (N : ℝ) ^ 2 := by
      rw [abs_mul]
      calc
        _ ≤ (C * (N : ℝ)) * (D * (N : ℝ)) :=
          mul_le_mul (hu N) (hv N) (abs_nonneg _) (mul_nonneg hC (Nat.cast_nonneg _))
        _ = _ := by ring
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hpreal : (0 : ℝ) < p := by exact_mod_cast hp
    rw [abs_mul, abs_of_nonneg hmass0]
    calc
      _ ≤ ((C * D) * (N : ℝ) ^ 2) *
          (1 / ((p : ℝ) * ((N : ℝ) * ((N : ℝ) + 1)))) :=
        mul_le_mul hprod hmass hmass0 (mul_nonneg (mul_nonneg hC hD) (sq_nonneg _))
      _ ≤ ((C * D) * ((N : ℝ) * ((N : ℝ) + 1))) *
          (1 / ((p : ℝ) * ((N : ℝ) * ((N : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by nlinarith only [hNreal.le]) (mul_nonneg hC hD))
          (by positivity)
      _ = C * D / (p : ℝ) := by field_simp

/-- Unit linear row bounds make the incomplete-fibre cost at most `1/p`. -/
theorem abs_pronicPairing_rowDilate_horizon_error {p : ℕ} (hp : 1 ≤ p)
    (T : ℕ) (u v : ℕ → ℝ) (hu0 : u 0 = 0)
    (hu : ∀ n, |u n| ≤ (n : ℝ)) (hv : ∀ n, |v n| ≤ (n : ℝ)) :
    |pronicPairing T (rowDilate p u) (rowDilate p v) -
      (1 / (p : ℝ)) * pronicPairing (T / p) u v| ≤ 1 / (p : ℝ) := by
  simpa only [one_mul] using
    abs_pronicPairing_rowDilate_horizon_error_of_bounds hp T u v hu0
      (C := 1) (D := 1) zero_le_one zero_le_one
      (fun n => by simpa only [one_mul] using hu n)
      (fun n => by simpa only [one_mul] using hv n)

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

#print axioms GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.pronicPairing_rowDilate_eq_horizon_correction
#print axioms GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.abs_pronicPairing_rowDilate_horizon_error
end
