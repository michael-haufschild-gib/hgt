import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualWeightConductor
import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareTail

noncomputable section

namespace RHTower

open Complex Set

theorem exists_norm_smoothAFEZetaSquareDualWeight_frozen_low_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N m : ℕ}, 4 ≤ N → 1 ≤ m → m ≤ N →
      ‖smoothAFEZetaSquareDualWeight (N : ℝ)
        ((m : ℝ) * (N : ℝ))‖ ≤ 1 + C := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_sub_one_le_conductor
  refine ⟨C, hC, ?_⟩
  intro N m hN hm hmN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hYpos : 0 < (m : ℝ) * (N : ℝ) := mul_pos hmpos hNpos
  have hraw := hweight (N : ℝ) hYpos
  have hmax : max 1 |(N : ℝ)| = (N : ℝ) := by
    rw [abs_of_pos hNpos, max_eq_right]
    exact_mod_cast (show 1 ≤ N by omega)
  rw [hmax] at hraw
  have hYle : (m : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    nlinarith
  have hquarter : ((m : ℝ) * (N : ℝ)) ^ (1 / 4 : ℝ) ≤
      ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    calc
      ((m : ℝ) * (N : ℝ)) ^ (1 / 4 : ℝ)
          ≤ ((N : ℝ) ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hYpos.le hYle (by norm_num)
      _ = ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
        calc
          ((N : ℝ) ^ 2) ^ (1 / 4 : ℝ) =
              (N : ℝ) ^ ((2 : ℝ) * (1 / 4 : ℝ)) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hNpos.le]
            norm_num
          _ = (N : ℝ) ^ ((1 / 4 : ℝ) * 2) := by ring_nf
          _ = ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
            rw [Real.rpow_mul hNpos.le]
            exact Real.rpow_natCast _ 2
  have hden : 0 < ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by positivity
  have herr :
      ‖smoothAFEZetaSquareDualWeight (N : ℝ) ((m : ℝ) * (N : ℝ)) - 1‖ ≤ C := by
    calc
      ‖smoothAFEZetaSquareDualWeight (N : ℝ) ((m : ℝ) * (N : ℝ)) - 1‖
          ≤ C * ((m : ℝ) * (N : ℝ)) ^ (1 / 4 : ℝ) /
              ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := hraw
      _ ≤ C * ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 /
              ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hquarter hC) hden.le
      _ = C := by field_simp [hden.ne']
  calc
    ‖smoothAFEZetaSquareDualWeight (N : ℝ) ((m : ℝ) * (N : ℝ))‖ =
        ‖(smoothAFEZetaSquareDualWeight (N : ℝ) ((m : ℝ) * (N : ℝ)) - 1) + 1‖ := by ring_nf
    _ ≤ ‖smoothAFEZetaSquareDualWeight (N : ℝ) ((m : ℝ) * (N : ℝ)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + C := by norm_num; linarith

theorem exists_norm_smoothAFEZetaSquareDualWeight_frozen_high_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N m : ℕ}, 4 ≤ N → 1 ≤ m →
      ‖smoothAFEZetaSquareDualWeight (N : ℝ)
        ((m : ℝ) * (N : ℝ))‖ ≤ 4 * K * (N : ℝ) / (m : ℝ) := by
  obtain ⟨K, hK, hweight⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_le_invScale
  refine ⟨K, hK, ?_⟩
  intro N m hN hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hYpos : 0 < (m : ℝ) * (N : ℝ) := mul_pos hmpos hNpos
  have hraw := hweight (N : ℝ) hYpos
  have hlin : 1 + (N : ℝ) ≤ 2 * (N : ℝ) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hsq : (1 + (N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
  rw [abs_of_pos hNpos] at hraw
  calc
    ‖smoothAFEZetaSquareDualWeight (N : ℝ) ((m : ℝ) * (N : ℝ))‖
        ≤ K * (1 + (N : ℝ)) ^ 2 / ((m : ℝ) * (N : ℝ)) := hraw
    _ ≤ K * (4 * (N : ℝ) ^ 2) / ((m : ℝ) * (N : ℝ)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq hK) hYpos.le
    _ = 4 * K * (N : ℝ) / (m : ℝ) := by
      field_simp [hNpos.ne', hmpos.ne']

/-- Weighted square mass of frozen inner dual AFE coefficients. -/
def smoothAFEZetaSquareDualFrozenWeightedMass (N k : ℕ) : ℝ :=
  (((k + 1).divisors.card : ℝ) ^ 2) *
    ‖smoothAFEZetaSquareDualWeight (N : ℝ)
      (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2

/-- Plain square mass after the critical half-power normalization. -/
def smoothAFEZetaSquareDualFrozenPlainMass (N k : ℕ) : ℝ :=
  smoothAFEZetaSquareDualFrozenWeightedMass N k / ((k + 1 : ℕ) : ℝ)

private theorem sum_range_divisorSquare_succ_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, (((k + 1).divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hmoment := RHTower.Sieve.sum_card_divisors_pow_le_polylog 2 N hN
  have heq :
      ∑ k ∈ Finset.range N, (((k + 1).divisors.card : ℝ) ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext m; simp]
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [heq]
  simpa using hmoment

private theorem sum_range_divisorSquare_div_succ_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N,
        (((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ) ≤
      (1 + Real.log (N : ℝ)) ^ 4 := by
  have hmoment := RHTower.Sieve.sum_card_divisors_sq_div_le_polylog N hN
  have heq :
      ∑ k ∈ Finset.range N,
          (((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ) =
        ∑ n ∈ Finset.Icc 1 N,
          ((n.divisors.card : ℝ) ^ 2) / (n : ℝ) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext m; simp]
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [heq]
  exact hmoment

/-- Frozen dual inner source has the exact two affine square masses needed for mean square. -/
theorem exists_tsum_smoothAFEZetaSquareDualFrozenMasses_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∑' k : ℕ, smoothAFEZetaSquareDualFrozenWeightedMass N k) ≤
          B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 ∧
      (∑' k : ℕ, smoothAFEZetaSquareDualFrozenPlainMass N k) ≤
          B * (1 + Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hlow⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_frozen_low_le
  obtain ⟨K, hK, hhigh⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_frozen_high_le
  let B : ℝ := (1 + C) ^ 2 + 512 * K ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbaseSq : Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) /
        ((k + 1 : ℕ) : ℝ) ^ 2) := by
    apply (RHTower.Sieve.summable_divisorSquare_div_sq.comp_injective
      Nat.succ_injective).congr
    intro k
    norm_cast
  have hbaseCube : Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) /
        ((k + 1 : ℕ) : ℝ) ^ 3) := by
    apply (RHTower.Sieve.summable_divisorSquare_div_cube.comp_injective
      Nat.succ_injective).congr
    intro k
    norm_cast
  have hsumW : Summable (smoothAFEZetaSquareDualFrozenWeightedMass N) := by
    let Q : ℕ → ℝ := fun k =>
      (16 * K ^ 2 * (N : ℝ) ^ 2) *
        ((((k + 1).divisors.card : ℝ) ^ 2) /
          ((k + 1 : ℕ) : ℝ) ^ 2)
    have hQ : Summable Q := hbaseSq.mul_left (16 * K ^ 2 * (N : ℝ) ^ 2)
    refine Summable.of_nonneg_of_le
      (fun k => by unfold smoothAFEZetaSquareDualFrozenWeightedMass; positivity)
      (fun k => ?_) hQ
    have hw := hhigh hN (show 1 ≤ k + 1 by omega)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    unfold smoothAFEZetaSquareDualFrozenWeightedMass Q
    calc
      (((k + 1).divisors.card : ℝ) ^ 2) *
          ‖smoothAFEZetaSquareDualWeight (N : ℝ)
            (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 ≤
        (((k + 1).divisors.card : ℝ) ^ 2) *
          (4 * K * (N : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ((((k + 1).divisors.card : ℝ) ^ 2) /
            ((k + 1 : ℕ) : ℝ) ^ 2) := by ring
  have hsumP : Summable (smoothAFEZetaSquareDualFrozenPlainMass N) := by
    let Q : ℕ → ℝ := fun k =>
      (16 * K ^ 2 * (N : ℝ) ^ 2) *
        ((((k + 1).divisors.card : ℝ) ^ 2) /
          ((k + 1 : ℕ) : ℝ) ^ 3)
    have hQ : Summable Q := hbaseCube.mul_left (16 * K ^ 2 * (N : ℝ) ^ 2)
    refine Summable.of_nonneg_of_le
      (fun k => by
        unfold smoothAFEZetaSquareDualFrozenPlainMass smoothAFEZetaSquareDualFrozenWeightedMass
        positivity)
      (fun k => ?_) hQ
    have hw := hhigh hN (show 1 ≤ k + 1 by omega)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    unfold smoothAFEZetaSquareDualFrozenPlainMass
      smoothAFEZetaSquareDualFrozenWeightedMass Q
    calc
      ((((k + 1).divisors.card : ℝ) ^ 2) *
          ‖smoothAFEZetaSquareDualWeight (N : ℝ)
            (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2) /
          ((k + 1 : ℕ) : ℝ) ≤
        ((((k + 1).divisors.card : ℝ) ^ 2) *
          (4 * K * (N : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2) /
          ((k + 1 : ℕ) : ℝ) := by gcongr
      _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ((((k + 1).divisors.card : ℝ) ^ 2) /
            ((k + 1 : ℕ) : ℝ) ^ 3) := by ring
  have hheadW :
      ∑ k ∈ Finset.range N, smoothAFEZetaSquareDualFrozenWeightedMass N k ≤
        (1 + C) ^ 2 * ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) := by
    have hpoint : ∀ k ∈ Finset.range N,
        smoothAFEZetaSquareDualFrozenWeightedMass N k ≤
          (1 + C) ^ 2 * (((k + 1).divisors.card : ℝ) ^ 2) := by
      intro k hk
      have hw := hlow hN (show 1 ≤ k + 1 by omega)
        (by simpa using Finset.mem_range.mp hk)
      unfold smoothAFEZetaSquareDualFrozenWeightedMass
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
      nlinarith [mul_le_mul_of_nonneg_left hsq
        (sq_nonneg (((k + 1).divisors.card : ℝ)))]
    calc
      ∑ k ∈ Finset.range N, smoothAFEZetaSquareDualFrozenWeightedMass N k ≤
          ∑ k ∈ Finset.range N,
            (1 + C) ^ 2 * (((k + 1).divisors.card : ℝ) ^ 2) :=
        Finset.sum_le_sum hpoint
      _ = (1 + C) ^ 2 *
          ∑ k ∈ Finset.range N, (((k + 1).divisors.card : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ (1 + C) ^ 2 *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left (sum_range_divisorSquare_succ_le N hN1) (sq_nonneg _)
  have hheadP :
      ∑ k ∈ Finset.range N, smoothAFEZetaSquareDualFrozenPlainMass N k ≤
        (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 := by
    have hpoint : ∀ k ∈ Finset.range N,
        smoothAFEZetaSquareDualFrozenPlainMass N k ≤
          (1 + C) ^ 2 *
            ((((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ)) := by
      intro k hk
      have hw := hlow hN (show 1 ≤ k + 1 by omega)
        (by simpa using Finset.mem_range.mp hk)
      unfold smoothAFEZetaSquareDualFrozenPlainMass
        smoothAFEZetaSquareDualFrozenWeightedMass
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
      have hmul := mul_le_mul_of_nonneg_left hsq
        (sq_nonneg (((k + 1).divisors.card : ℝ)))
      calc
        (((k + 1).divisors.card : ℝ) ^ 2 *
              ‖smoothAFEZetaSquareDualWeight (N : ℝ)
                (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2) /
            ((k + 1 : ℕ) : ℝ) ≤
          (((k + 1).divisors.card : ℝ) ^ 2 * (1 + C) ^ 2) /
            ((k + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hmul (by positivity)
        _ = (1 + C) ^ 2 *
            (((k + 1).divisors.card : ℝ) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
          ring
    calc
      ∑ k ∈ Finset.range N, smoothAFEZetaSquareDualFrozenPlainMass N k ≤
          ∑ k ∈ Finset.range N, (1 + C) ^ 2 *
            ((((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = (1 + C) ^ 2 * ∑ k ∈ Finset.range N,
          (((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left
          (sum_range_divisorSquare_div_succ_le N hN1) (sq_nonneg _)
  have htailW :
      ∑' k : ℕ, smoothAFEZetaSquareDualFrozenWeightedMass N (k + N) ≤
        512 * K ^ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
    let Q : ℕ → ℝ := fun k =>
      (16 * K ^ 2 * (N : ℝ) ^ 2) *
        ((((N + 1 + k).divisors.card : ℝ) ^ 2) /
          ((N + 1 + k : ℕ) : ℝ) ^ 2)
    have hshift : Summable (fun k : ℕ =>
        smoothAFEZetaSquareDualFrozenWeightedMass N (k + N)) :=
      hsumW.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hQ : Summable Q := by
      have hinj : Function.Injective (fun k : ℕ => N + 1 + k) := by
        intro a b h
        exact Nat.add_left_cancel h
      have hb := RHTower.Sieve.summable_divisorSquare_div_sq.comp_injective hinj
      exact (hb.congr (fun k => by norm_cast)).mul_left _
    have hpoint : ∀ k : ℕ,
        smoothAFEZetaSquareDualFrozenWeightedMass N (k + N) ≤ Q k := by
      intro k
      have hw := hhigh hN (show 1 ≤ (k + N) + 1 by omega)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
      unfold smoothAFEZetaSquareDualFrozenWeightedMass Q
      calc
        ((((k + N) + 1).divisors.card : ℝ) ^ 2) *
            ‖smoothAFEZetaSquareDualWeight (N : ℝ)
              (((((k + N) + 1 : ℕ) : ℝ)) * (N : ℝ))‖ ^ 2 ≤
          ((((k + N) + 1).divisors.card : ℝ) ^ 2) *
            (4 * K * (N : ℝ) / ((((k + N) + 1 : ℕ) : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ((((N + 1 + k).divisors.card : ℝ) ^ 2) /
              ((N + 1 + k : ℕ) : ℝ) ^ 2) := by
          rw [show (k + N) + 1 = N + 1 + k by omega]
          ring
    have hc := hshift.tsum_le_tsum hpoint hQ
    rw [show (∑' k : ℕ, Q k) =
        (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) /
            ((N + 1 + k : ℕ) : ℝ) ^ 2 by
      dsimp only [Q]
      rw [tsum_mul_left]] at hc
    have ht := RHTower.Sieve.tsum_shift_divisorSquare_div_sq_le N hN1
    calc
      ∑' k : ℕ, smoothAFEZetaSquareDualFrozenWeightedMass N (k + N) ≤
          (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) /
              ((N + 1 + k : ℕ) : ℝ) ^ 2 := hc
      _ ≤ (16 * K ^ 2 * (N : ℝ) ^ 2) *
          (32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) := by gcongr
      _ = 512 * K ^ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
        field_simp [hNpos.ne']
        ring
  have htailP :
      ∑' k : ℕ, smoothAFEZetaSquareDualFrozenPlainMass N (k + N) ≤
        512 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 := by
    let Q : ℕ → ℝ := fun k =>
      (16 * K ^ 2 * (N : ℝ) ^ 2) *
        ((((N + 1 + k).divisors.card : ℝ) ^ 2) /
          ((N + 1 + k : ℕ) : ℝ) ^ 3)
    have hshift : Summable (fun k : ℕ =>
        smoothAFEZetaSquareDualFrozenPlainMass N (k + N)) :=
      hsumP.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hQ : Summable Q := by
      have hinj : Function.Injective (fun k : ℕ => N + 1 + k) := by
        intro a b h
        exact Nat.add_left_cancel h
      have hb := RHTower.Sieve.summable_divisorSquare_div_cube.comp_injective hinj
      exact (hb.congr (fun k => by norm_cast)).mul_left _
    have hpoint : ∀ k : ℕ,
        smoothAFEZetaSquareDualFrozenPlainMass N (k + N) ≤ Q k := by
      intro k
      have hw := hhigh hN (show 1 ≤ (k + N) + 1 by omega)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
      unfold smoothAFEZetaSquareDualFrozenPlainMass
        smoothAFEZetaSquareDualFrozenWeightedMass Q
      calc
        (((((k + N) + 1).divisors.card : ℝ) ^ 2) *
            ‖smoothAFEZetaSquareDualWeight (N : ℝ)
              (((((k + N) + 1 : ℕ) : ℝ)) * (N : ℝ))‖ ^ 2) /
              ((((k + N) + 1 : ℕ) : ℝ)) ≤
          (((((k + N) + 1).divisors.card : ℝ) ^ 2) *
            (4 * K * (N : ℝ) / ((((k + N) + 1 : ℕ) : ℝ))) ^ 2) /
              ((((k + N) + 1 : ℕ) : ℝ)) := by gcongr
        _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ((((N + 1 + k).divisors.card : ℝ) ^ 2) /
              ((N + 1 + k : ℕ) : ℝ) ^ 3) := by
          rw [show (k + N) + 1 = N + 1 + k by omega]
          ring
    have hc := hshift.tsum_le_tsum hpoint hQ
    rw [show (∑' k : ℕ, Q k) =
        (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) /
            ((N + 1 + k : ℕ) : ℝ) ^ 3 by
      dsimp only [Q]
      rw [tsum_mul_left]] at hc
    have ht := RHTower.Sieve.tsum_shift_divisorSquare_div_cube_le N hN1
    calc
      ∑' k : ℕ, smoothAFEZetaSquareDualFrozenPlainMass N (k + N) ≤
          (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) /
              ((N + 1 + k : ℕ) : ℝ) ^ 3 := hc
      _ ≤ (16 * K ^ 2 * (N : ℝ) ^ 2) *
          (32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) ^ 2) := by gcongr
      _ = 512 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 := by
        field_simp [hNpos.ne']
        ring
  constructor
  · rw [← hsumW.sum_add_tsum_nat_add N]
    calc
      ∑ k ∈ Finset.range N, smoothAFEZetaSquareDualFrozenWeightedMass N k +
            ∑' k : ℕ, smoothAFEZetaSquareDualFrozenWeightedMass N (k + N) ≤
          (1 + C) ^ 2 * ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) +
            512 * K ^ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 :=
        add_le_add hheadW htailW
      _ = B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
        dsimp only [B]
        ring
  · rw [← hsumP.sum_add_tsum_nat_add N]
    have hlog0 : 0 ≤ 1 + Real.log (N : ℝ) := by
      have := Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N)
      linarith
    have hcubefour : (1 + Real.log (N : ℝ)) ^ 3 ≤
        (1 + Real.log (N : ℝ)) ^ 4 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hlog0 3) (by
        have := Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N)
        linarith)
    calc
      ∑ k ∈ Finset.range N, smoothAFEZetaSquareDualFrozenPlainMass N k +
            ∑' k : ℕ, smoothAFEZetaSquareDualFrozenPlainMass N (k + N) ≤
          (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 +
            512 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 :=
        add_le_add hheadP htailP
      _ ≤ (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 +
            512 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 4 := by gcongr
      _ = B * (1 + Real.log (N : ℝ)) ^ 4 := by
        dsimp only [B]
        ring

end RHTower
