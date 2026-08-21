import GaloisForLFunctions.RHTower.SmoothAFEZetaSquarePrimalHeightDerivative
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareLogTail

noncomputable section

namespace RHTower

open Complex Set

/-- Plain square mass of the differentiated primal square-AFE source. -/
def smoothAFEZetaSquarePrimalHeightDerivativePlainMass (N k : ℕ) : ℝ :=
  ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N 0 k‖ ^ 2

/-- Affine-weighted square mass of the differentiated primal square-AFE source. -/
def smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass (N k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) *
    smoothAFEZetaSquarePrimalHeightDerivativePlainMass N k

private theorem norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_zero_sq_formula
    {N : ℕ} (hN : 4 ≤ N) (k : ℕ) :
    ‖smoothAFEZetaSquarePrimalHeightDerivativeTerm N 0 k‖ ^ 2 =
      (((k + 1).divisors.card : ℝ) ^ 2) *
        Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
        ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
          (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 /
        ((k + 1 : ℕ) : ℝ) := by
  have hm1 : 1 ≤ k + 1 := by omega
  have hm0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hlog0 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm1)
  have hcast : (k : ℂ) + 1 = ((((k : ℝ) + 1 : ℝ)) : ℂ) := by norm_cast
  have hnormlog : ‖Complex.log (k + 1 : ℂ)‖ =
      Real.log ((k + 1 : ℕ) : ℝ) := by
    rw [hcast, ← Complex.ofReal_log (by positivity), Complex.norm_real,
      Real.norm_eq_abs]
    push_cast at hlog0 ⊢
    exact abs_of_nonneg hlog0
  have hmk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpow : (((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) ^ 2 =
      1 / ((k : ℝ) + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmk0.le]
    norm_num [Real.rpow_neg_one]
  simp only [smoothAFEZetaSquarePrimalHeightDerivativeTerm,
    norm_mul, Complex.norm_natCast, norm_natSucc_cpow_neg_linePt,
    norm_neg, norm_I, mul_one]
  rw [hnormlog, ← smoothAFEZetaSquarePrimalCutoff_mul_conductor hN0]
  rw [mul_pow, mul_pow, mul_pow, hpow]
  push_cast
  ring

private theorem derivativePlainMass_formula
    {N : ℕ} (hN : 4 ≤ N) (k : ℕ) :
    smoothAFEZetaSquarePrimalHeightDerivativePlainMass N k =
      (((k + 1).divisors.card : ℝ) ^ 2) *
        Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
        ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
          (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 /
        ((k + 1 : ℕ) : ℝ) := by
  exact norm_smoothAFEZetaSquarePrimalHeightDerivativeTerm_zero_sq_formula hN k

private theorem derivativeWeightedMass_formula
    {N : ℕ} (hN : 4 ≤ N) (k : ℕ) :
    smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N k =
      (((k + 1).divisors.card : ℝ) ^ 2) *
        Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
        ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
          (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 := by
  rw [smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass,
    derivativePlainMass_formula hN]
  have hm0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  field_simp [hm0.ne']

private theorem summable_shift_divisorSquare_log_sq_div_sq :
    Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) *
        Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
        ((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hbase := RHTower.summable_divisor_sq_log_rpow
    (σ := (1 : ℝ)) (by norm_num)
  apply (hbase.comp_injective Nat.succ_injective).congr
  intro k
  simp only [Function.comp_apply]
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [show (-2 * (1 : ℝ)) = (-2 : ℝ) by norm_num,
    Real.rpow_neg hk.le]
  norm_num [one_div]
  ring

private theorem summable_shift_divisorSquare_log_sq_div_cube :
    Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) *
        Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
        ((k + 1 : ℕ) : ℝ) ^ 3) := by
  have hbase := RHTower.summable_divisor_sq_log_rpow
    (σ := (3 / 2 : ℝ)) (by norm_num)
  apply (hbase.comp_injective Nat.succ_injective).congr
  intro k
  simp only [Function.comp_apply]
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [show (-2 * (3 / 2 : ℝ)) = (-3 : ℝ) by norm_num,
    Real.rpow_neg hk.le]
  norm_num [one_div]
  ring

theorem summable_smoothAFEZetaSquarePrimalHeightDerivativeMasses
    {N : ℕ} (hN : 4 ≤ N) :
    Summable (smoothAFEZetaSquarePrimalHeightDerivativePlainMass N) ∧
      Summable (smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N) := by
  obtain ⟨K, hK, hhigh⟩ :=
    exists_norm_smoothAFEZetaSquarePrimalCutoff_high_le
  have hW : Summable
      (smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N) := by
    refine Summable.of_nonneg_of_le
      (fun k => by
        unfold smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass
          smoothAFEZetaSquarePrimalHeightDerivativePlainMass
        positivity)
      (fun k => ?_)
      (summable_shift_divisorSquare_log_sq_div_sq.mul_left
        (16 * K ^ 2 * (N : ℝ) ^ 2))
    have hw := hhigh hN (show 1 ≤ k + 1 by omega)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [derivativeWeightedMass_formula hN]
    calc
      (((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
            ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
              (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2
          ≤ (((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
            (4 * K * (N : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2 := by gcongr
      _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ((((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
            ((k + 1 : ℕ) : ℝ) ^ 2) := by ring
  have hP : Summable
      (smoothAFEZetaSquarePrimalHeightDerivativePlainMass N) := by
    refine Summable.of_nonneg_of_le
      (fun k => by
        unfold smoothAFEZetaSquarePrimalHeightDerivativePlainMass
        positivity)
      (fun k => ?_)
      (summable_shift_divisorSquare_log_sq_div_cube.mul_left
        (16 * K ^ 2 * (N : ℝ) ^ 2))
    have hw := hhigh hN (show 1 ≤ k + 1 by omega)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [derivativePlainMass_formula hN]
    calc
      ((((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
            ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
              (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2) /
            ((k + 1 : ℕ) : ℝ)
          ≤ ((((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
            (4 * K * (N : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2) /
            ((k + 1 : ℕ) : ℝ) := by gcongr
      _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ((((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
            ((k + 1 : ℕ) : ℝ) ^ 3) := by ring
  exact ⟨hP, hW⟩

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

private theorem log_natSucc_le_one_add_log_of_lt
    {N k : ℕ} (hN : 1 ≤ N) (hk : k < N) :
    Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  have hm1 : 1 ≤ k + 1 := by omega
  have hmN : k + 1 ≤ N := by omega
  have hmono : Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (((k + 1 : ℕ) : ℝ)) ∈ Set.Ioi 0 by
        change (0 : ℝ) < ((k + 1 : ℕ) : ℝ)
        exact_mod_cast (show 0 < k + 1 by omega))
      (show (N : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < N
        exact_mod_cast (show 0 < N by omega))
      (by exact_mod_cast hmN)
  linarith

private theorem sum_range_divisorSquare_log_sq_succ_le
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N,
        (((k + 1).divisors.card : ℝ) ^ 2) *
          Real.log ((k + 1 : ℕ) : ℝ) ^ 2 ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 := by
  have hbase : 0 ≤ 1 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)]
  calc
    ∑ k ∈ Finset.range N,
          (((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2
        ≤ ∑ k ∈ Finset.range N,
          (1 + Real.log (N : ℝ)) ^ 2 *
            (((k + 1).divisors.card : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hlog0 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 1 by omega))
      have hlog := log_natSucc_le_one_add_log_of_lt hN (Finset.mem_range.mp hk)
      have hsq := pow_le_pow_left₀ hlog0 hlog 2
      nlinarith [sq_nonneg (((k + 1).divisors.card : ℝ))]
    _ = (1 + Real.log (N : ℝ)) ^ 2 *
          ∑ k ∈ Finset.range N,
            (((k + 1).divisors.card : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) :=
      mul_le_mul_of_nonneg_left (sum_range_divisorSquare_succ_le N hN)
        (pow_nonneg hbase 2)
    _ = (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 := by ring

private theorem sum_range_divisorSquare_log_sq_div_succ_le
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N,
        (((k + 1).divisors.card : ℝ) ^ 2) *
          Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
          ((k + 1 : ℕ) : ℝ) ≤
      (1 + Real.log (N : ℝ)) ^ 6 := by
  have hbase : 0 ≤ 1 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)]
  calc
    ∑ k ∈ Finset.range N,
          (((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
            ((k + 1 : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.range N,
          (1 + Real.log (N : ℝ)) ^ 2 *
            ((((k + 1).divisors.card : ℝ) ^ 2) /
              ((k + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hlog0 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 1 by omega))
      have hlog := log_natSucc_le_one_add_log_of_lt hN (Finset.mem_range.mp hk)
      have hsq := pow_le_pow_left₀ hlog0 hlog 2
      have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      calc
        (((k + 1).divisors.card : ℝ) ^ 2) *
              Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
              ((k + 1 : ℕ) : ℝ)
            ≤ ((1 + Real.log (N : ℝ)) ^ 2 *
                (((k + 1).divisors.card : ℝ) ^ 2)) /
              ((k + 1 : ℕ) : ℝ) :=
          (div_le_div_iff_of_pos_right hden).2 (by
            nlinarith [sq_nonneg (((k + 1).divisors.card : ℝ))])
        _ = (1 + Real.log (N : ℝ)) ^ 2 *
            ((((k + 1).divisors.card : ℝ) ^ 2) /
              ((k + 1 : ℕ) : ℝ)) := by ring
    _ = (1 + Real.log (N : ℝ)) ^ 2 *
          ∑ k ∈ Finset.range N,
            (((k + 1).divisors.card : ℝ) ^ 2) /
              ((k + 1 : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 *
          (1 + Real.log (N : ℝ)) ^ 4 :=
      mul_le_mul_of_nonneg_left (sum_range_divisorSquare_div_succ_le N hN)
        (pow_nonneg hbase 2)
    _ = (1 + Real.log (N : ℝ)) ^ 6 := by ring

/-- The differentiated primal square-AFE source has sharp affine masses
`O(N log⁵ N)` and `O(log⁶ N)`. -/
theorem exists_tsum_smoothAFEZetaSquarePrimalHeightDerivativeMasses_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∑' k : ℕ,
        smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N k) ≤
          B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 ∧
      (∑' k : ℕ,
        smoothAFEZetaSquarePrimalHeightDerivativePlainMass N k) ≤
          B * (1 + Real.log (N : ℝ)) ^ 6 := by
  obtain ⟨C, hC, hlow⟩ :=
    exists_norm_smoothAFEZetaSquarePrimalCutoff_low_le
  obtain ⟨K, hK, hhigh⟩ :=
    exists_norm_smoothAFEZetaSquarePrimalCutoff_high_le
  let B : ℝ := (1 + C) ^ 2 + 10432 * K ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N)]
  obtain ⟨hsumP, hsumW⟩ :=
    summable_smoothAFEZetaSquarePrimalHeightDerivativeMasses hN
  have hheadW :
      ∑ k ∈ Finset.range N,
          smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N k ≤
        (1 + C) ^ 2 *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5) := by
    calc
      ∑ k ∈ Finset.range N,
            smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N k
          ≤ ∑ k ∈ Finset.range N,
            (1 + C) ^ 2 *
              ((((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hw := hlow hN (show 1 ≤ k + 1 by omega)
          (by simpa using Finset.mem_range.mp hk)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
        rw [derivativeWeightedMass_formula hN]
        have hcoeff : 0 ≤ (((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
        calc
          (((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
                ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
                  (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2
              ≤ (((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2 * (1 + C) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq hcoeff
          _ = (1 + C) ^ 2 *
              ((((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2) := by ring
      _ = (1 + C) ^ 2 *
          ∑ k ∈ Finset.range N,
            (((k + 1).divisors.card : ℝ) ^ 2) *
              Real.log ((k + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ (1 + C) ^ 2 *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5) :=
        mul_le_mul_of_nonneg_left
          (sum_range_divisorSquare_log_sq_succ_le N hN1) (sq_nonneg _)
  have hheadP :
      ∑ k ∈ Finset.range N,
          smoothAFEZetaSquarePrimalHeightDerivativePlainMass N k ≤
        (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 6 := by
    calc
      ∑ k ∈ Finset.range N,
            smoothAFEZetaSquarePrimalHeightDerivativePlainMass N k
          ≤ ∑ k ∈ Finset.range N,
            (1 + C) ^ 2 *
              ((((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
                ((k + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hw := hlow hN (show 1 ≤ k + 1 by omega)
          (by simpa using Finset.mem_range.mp hk)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
        rw [derivativePlainMass_formula hN]
        have hcoeff : 0 ≤ (((k + 1).divisors.card : ℝ) ^ 2) *
            Real.log ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
        have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        calc
          ((((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2 *
                ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
                  (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2) /
                ((k + 1 : ℕ) : ℝ)
              ≤ ((((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2 * (1 + C) ^ 2) /
                ((k + 1 : ℕ) : ℝ) :=
            (div_le_div_iff_of_pos_right hden).2
              (mul_le_mul_of_nonneg_left hsq hcoeff)
          _ = (1 + C) ^ 2 *
              ((((k + 1).divisors.card : ℝ) ^ 2) *
                Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
                ((k + 1 : ℕ) : ℝ)) := by ring
      _ = (1 + C) ^ 2 *
          ∑ k ∈ Finset.range N,
            (((k + 1).divisors.card : ℝ) ^ 2) *
              Real.log ((k + 1 : ℕ) : ℝ) ^ 2 /
              ((k + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 6 :=
        mul_le_mul_of_nonneg_left
          (sum_range_divisorSquare_log_sq_div_succ_le N hN1) (sq_nonneg _)
  have htailW :
      ∑' k : ℕ,
          smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N (k + N) ≤
        10432 * K ^ 2 * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 5 := by
    let Q : ℕ → ℝ := fun k =>
      (16 * K ^ 2 * (N : ℝ) ^ 2) *
        ((((N + 1 + k).divisors.card : ℝ) ^ 2) *
          Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 2)
    have hshift : Summable (fun k : ℕ =>
        smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N (k + N)) :=
      hsumW.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hQ : Summable Q := by
      have hb := summable_shift_divisorSquare_log_sq_div_sq.comp_injective
        (fun a b h => Nat.add_right_cancel h : Function.Injective (fun k : ℕ => k + N))
      apply (hb.congr (fun k => ?_)).mul_left _
      dsimp only [Function.comp_apply]
      rw [show (k + N) + 1 = N + 1 + k by omega]
    have hpoint : ∀ k : ℕ,
        smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N (k + N) ≤ Q k := by
      intro k
      have hw := hhigh hN (show 1 ≤ (k + N) + 1 by omega)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
      rw [derivativeWeightedMass_formula hN]
      dsimp only [Q]
      rw [show (k + N) + 1 = N + 1 + k by omega]
      have hsq' :
          ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
            (((N + 1 + k : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 ≤
            (4 * K * (N : ℝ) / ((N + 1 + k : ℕ) : ℝ)) ^ 2 := by
        simpa [show (k + N) + 1 = N + 1 + k by omega] using hsq
      calc
        (((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 *
              ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
                (((N + 1 + k : ℕ) : ℝ) * (N : ℝ))‖ ^ 2
            ≤ (((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 *
              (4 * K * (N : ℝ) / ((N + 1 + k : ℕ) : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq' (by positivity)
        _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ((((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
              ((N + 1 + k : ℕ) : ℝ) ^ 2) := by ring
    have hc := hshift.tsum_le_tsum hpoint hQ
    rw [show (∑' k : ℕ, Q k) =
        (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) *
            Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
            ((N + 1 + k : ℕ) : ℝ) ^ 2 by
      dsimp only [Q]
      rw [tsum_mul_left]] at hc
    have ht := RHTower.Sieve.tsum_shift_divisorSquare_log_sq_div_sq_le N hN1
    calc
      ∑' k : ℕ,
            smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N (k + N)
          ≤ (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
              ((N + 1 + k : ℕ) : ℝ) ^ 2 := hc
      _ ≤ (16 * K ^ 2 * (N : ℝ) ^ 2) *
          (652 * (1 + Real.log (N : ℝ)) ^ 5 / (N : ℝ)) := by gcongr
      _ = 10432 * K ^ 2 * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ 5 := by
        field_simp [hNpos.ne']
        ring
  have htailP :
      ∑' k : ℕ,
          smoothAFEZetaSquarePrimalHeightDerivativePlainMass N (k + N) ≤
        10432 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 5 := by
    let Q : ℕ → ℝ := fun k =>
      (16 * K ^ 2 * (N : ℝ) ^ 2) *
        ((((N + 1 + k).divisors.card : ℝ) ^ 2) *
          Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 3)
    have hshift : Summable (fun k : ℕ =>
        smoothAFEZetaSquarePrimalHeightDerivativePlainMass N (k + N)) :=
      hsumP.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hQ : Summable Q := by
      have hb := summable_shift_divisorSquare_log_sq_div_cube.comp_injective
        (fun a b h => Nat.add_right_cancel h : Function.Injective (fun k : ℕ => k + N))
      apply (hb.congr (fun k => ?_)).mul_left _
      dsimp only [Function.comp_apply]
      rw [show (k + N) + 1 = N + 1 + k by omega]
    have hpoint : ∀ k : ℕ,
        smoothAFEZetaSquarePrimalHeightDerivativePlainMass N (k + N) ≤ Q k := by
      intro k
      have hw := hhigh hN (show 1 ≤ (k + N) + 1 by omega)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
      rw [derivativePlainMass_formula hN]
      dsimp only [Q]
      rw [show (k + N) + 1 = N + 1 + k by omega]
      have hsq' :
          ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
            (((N + 1 + k : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 ≤
            (4 * K * (N : ℝ) / ((N + 1 + k : ℕ) : ℝ)) ^ 2 := by
        simpa [show (k + N) + 1 = N + 1 + k by omega] using hsq
      calc
        ((((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 *
              ‖smoothAFEZetaSquarePrimalCutoff (N : ℝ)
                (((N + 1 + k : ℕ) : ℝ) * (N : ℝ))‖ ^ 2) /
              ((N + 1 + k : ℕ) : ℝ)
            ≤ ((((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 *
              (4 * K * (N : ℝ) / ((N + 1 + k : ℕ) : ℝ)) ^ 2) /
              ((N + 1 + k : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq' (by positivity)) (by positivity)
        _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ((((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
              ((N + 1 + k : ℕ) : ℝ) ^ 3) := by ring
    have hc := hshift.tsum_le_tsum hpoint hQ
    rw [show (∑' k : ℕ, Q k) =
        (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) *
            Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
            ((N + 1 + k : ℕ) : ℝ) ^ 3 by
      dsimp only [Q]
      rw [tsum_mul_left]] at hc
    have ht := RHTower.Sieve.tsum_shift_divisorSquare_log_sq_div_cube_le N hN1
    calc
      ∑' k : ℕ,
            smoothAFEZetaSquarePrimalHeightDerivativePlainMass N (k + N)
          ≤ (16 * K ^ 2 * (N : ℝ) ^ 2) *
            ∑' k : ℕ, (((N + 1 + k).divisors.card : ℝ) ^ 2) *
              Real.log ((N + 1 + k : ℕ) : ℝ) ^ 2 /
              ((N + 1 + k : ℕ) : ℝ) ^ 3 := hc
      _ ≤ (16 * K ^ 2 * (N : ℝ) ^ 2) *
          (652 * (1 + Real.log (N : ℝ)) ^ 5 / (N : ℝ) ^ 2) := by gcongr
      _ = 10432 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 5 := by
        field_simp [hNpos.ne']
        ring
  constructor
  · rw [← hsumW.sum_add_tsum_nat_add N]
    calc
      ∑ k ∈ Finset.range N,
            smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N k +
          ∑' k : ℕ,
            smoothAFEZetaSquarePrimalHeightDerivativeWeightedMass N (k + N)
          ≤ (1 + C) ^ 2 *
              ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5) +
            10432 * K ^ 2 * (N : ℝ) *
              (1 + Real.log (N : ℝ)) ^ 5 := add_le_add hheadW htailW
      _ = B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 := by
        dsimp only [B]
        ring
  · rw [← hsumP.sum_add_tsum_nat_add N]
    have hpow : (1 + Real.log (N : ℝ)) ^ 5 ≤
        (1 + Real.log (N : ℝ)) ^ 6 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hlog0 5)
        (by linarith [Real.log_nonneg (by exact_mod_cast hN1 : (1 : ℝ) ≤ N)])
    calc
      ∑ k ∈ Finset.range N,
            smoothAFEZetaSquarePrimalHeightDerivativePlainMass N k +
          ∑' k : ℕ,
            smoothAFEZetaSquarePrimalHeightDerivativePlainMass N (k + N)
          ≤ (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 6 +
            10432 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 5 :=
        add_le_add hheadP htailP
      _ ≤ (1 + C) ^ 2 * (1 + Real.log (N : ℝ)) ^ 6 +
            10432 * K ^ 2 * (1 + Real.log (N : ℝ)) ^ 6 := by gcongr
      _ = B * (1 + Real.log (N : ℝ)) ^ 6 := by
        dsimp only [B]
        ring

end RHTower
