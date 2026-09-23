import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogLocal
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Higher logarithmic jets of the local Selberg correction

For every positive derivative order `k`, the local correction factor has numerator

`(log p)^k / p^(2 : ℕ) * XY * (X + Y - 2^k XY)`.

The same geometric tails used for the first derivative therefore give an `ell^(1 : ℕ)` mass bounded by
`(8 + 4 * 2^k) * (log p)^k / p^(2 : ℕ)`.  In particular the square and cube jets required by the
origin-based Barban--Vehov energy are absolutely summable over primes.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Coefficient of `X^alpha Y^beta` in the `k`-th logarithmic derivative of the local correction
factor.  The intended range is `0 < k`. -/
def selbergCorrectionLogPowerLocal (k p alpha beta : ℕ) : ℝ :=
  (Real.log (p : ℝ) ^ k / (p : ℝ) ^ (2 + alpha + beta)) *
    ((if 2 ≤ alpha ∧ 1 ≤ beta then (p : ℝ) ^ 3 else 0) +
      (if 1 ≤ alpha ∧ 2 ≤ beta then (p : ℝ) ^ 3 else 0) -
      (if 2 ≤ alpha ∧ 2 ≤ beta then (2 : ℝ) ^ k * (p : ℝ) ^ 4 else 0))

theorem selbergCorrectionLogPowerLocal_one (p alpha beta : ℕ) :
    selbergCorrectionLogPowerLocal 1 p alpha beta =
      selbergCorrectionLogLocal p alpha beta := by
  rw [selbergCorrectionLogPowerLocal, selbergCorrectionLogLocal]
  norm_num

/-- Product form exposing the three summable geometric tails. -/
theorem selbergCorrectionLogPowerLocal_eq_geomTails
    (k : ℕ) {p : ℕ} (hp : 0 < p) (alpha beta : ℕ) :
    selbergCorrectionLogPowerLocal k p alpha beta =
      Real.log (p : ℝ) ^ k *
        ((1 / (p : ℝ) ^ 2) * (geomTailTwo p alpha * geomTailOne p beta) +
          (1 / (p : ℝ) ^ 2) * (geomTailOne p alpha * geomTailTwo p beta) -
          (1 / (p : ℝ) ^ 2) *
            ((2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta))) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hA :
      (if 2 ≤ alpha ∧ 1 ≤ beta then (p : ℝ) ^ 3 else 0) /
          (p : ℝ) ^ (2 + alpha + beta) =
        (1 / (p : ℝ) ^ 2) * (geomTailTwo p alpha * geomTailOne p beta) := by
    rw [geomTailTwo, geomTailOne]
    by_cases hab : 2 ≤ alpha ∧ 1 ≤ beta
    · rw [if_pos hab, if_pos hab.1, if_pos hab.2]
      field_simp
      ring
    · rw [if_neg hab]
      rcases not_and_or.mp hab with h | h
      · rw [if_neg h]
        simp
      · rw [if_neg h]
        simp
  have hB :
      (if 1 ≤ alpha ∧ 2 ≤ beta then (p : ℝ) ^ 3 else 0) /
          (p : ℝ) ^ (2 + alpha + beta) =
        (1 / (p : ℝ) ^ 2) * (geomTailOne p alpha * geomTailTwo p beta) := by
    rw [geomTailTwo, geomTailOne]
    by_cases hab : 1 ≤ alpha ∧ 2 ≤ beta
    · rw [if_pos hab, if_pos hab.1, if_pos hab.2]
      field_simp
      ring
    · rw [if_neg hab]
      rcases not_and_or.mp hab with h | h
      · rw [if_neg h]
        simp
      · rw [if_neg h]
        simp
  have hC :
      (if 2 ≤ alpha ∧ 2 ≤ beta then (2 : ℝ) ^ k * (p : ℝ) ^ 4 else 0) /
          (p : ℝ) ^ (2 + alpha + beta) =
        (1 / (p : ℝ) ^ 2) *
          ((2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta)) := by
    simp only [geomTailTwo]
    by_cases hab : 2 ≤ alpha ∧ 2 ≤ beta
    · rw [if_pos hab, if_pos hab.1, if_pos hab.2]
      field_simp
      ring
    · rw [if_neg hab]
      rcases not_and_or.mp hab with h | h
      · rw [if_neg h]
        simp
      · rw [if_neg h]
        simp
  rw [selbergCorrectionLogPowerLocal, ← hA, ← hB, ← hC]
  field_simp

/-- Nonnegative local majorant. -/
def selbergCorrectionLogPowerMajorant (k p alpha beta : ℕ) : ℝ :=
  (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) *
    (geomTailTwo p alpha * geomTailOne p beta +
      geomTailOne p alpha * geomTailTwo p beta +
      (2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta))

theorem selbergCorrectionLogPowerMajorant_nonneg
    (k : ℕ) {p : ℕ} (hp : 2 ≤ p) (alpha beta : ℕ) :
    0 ≤ selbergCorrectionLogPowerMajorant k p alpha beta := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith)
  rw [selbergCorrectionLogPowerMajorant]
  have hfac : 0 ≤ Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2 := by positivity
  have h1 := mul_nonneg (geomTailTwo_nonneg p alpha) (geomTailOne_nonneg p beta)
  have h2 := mul_nonneg (geomTailOne_nonneg p alpha) (geomTailTwo_nonneg p beta)
  have h3 := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
    (mul_nonneg (geomTailTwo_nonneg p alpha) (geomTailTwo_nonneg p beta))
  exact mul_nonneg hfac (by linarith)

/-- Termwise domination of every higher local jet. -/
theorem abs_selbergCorrectionLogPowerLocal_le
    (k : ℕ) {p : ℕ} (hp : 2 ≤ p) (alpha beta : ℕ) :
    |selbergCorrectionLogPowerLocal k p alpha beta| ≤
      selbergCorrectionLogPowerMajorant k p alpha beta := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hp)
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith)
  rw [selbergCorrectionLogPowerLocal_eq_geomTails k (by omega) alpha beta,
    selbergCorrectionLogPowerMajorant, abs_mul,
    abs_of_nonneg (pow_nonneg hlogp k)]
  have h1 : 0 ≤ geomTailTwo p alpha * geomTailOne p beta :=
    mul_nonneg (geomTailTwo_nonneg p alpha) (geomTailOne_nonneg p beta)
  have h2 : 0 ≤ geomTailOne p alpha * geomTailTwo p beta :=
    mul_nonneg (geomTailOne_nonneg p alpha) (geomTailTwo_nonneg p beta)
  have h3 : 0 ≤ (2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta) :=
    mul_nonneg (pow_nonneg (by norm_num) k)
      (mul_nonneg (geomTailTwo_nonneg p alpha) (geomTailTwo_nonneg p beta))
  have hinv : (0 : ℝ) < 1 / (p : ℝ) ^ 2 := by positivity
  have hbound :
      |(1 / (p : ℝ) ^ 2) * (geomTailTwo p alpha * geomTailOne p beta) +
          (1 / (p : ℝ) ^ 2) * (geomTailOne p alpha * geomTailTwo p beta) -
          (1 / (p : ℝ) ^ 2) *
            ((2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta))| ≤
        (1 / (p : ℝ) ^ 2) *
          (geomTailTwo p alpha * geomTailOne p beta +
            geomTailOne p alpha * geomTailTwo p beta +
            (2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta)) := by
    rw [abs_le]
    constructor <;> nlinarith
  calc
    Real.log (p : ℝ) ^ k *
          |(1 / (p : ℝ) ^ 2) * (geomTailTwo p alpha * geomTailOne p beta) +
              (1 / (p : ℝ) ^ 2) * (geomTailOne p alpha * geomTailTwo p beta) -
              (1 / (p : ℝ) ^ 2) *
                ((2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta))| ≤
        Real.log (p : ℝ) ^ k *
          ((1 / (p : ℝ) ^ 2) *
            (geomTailTwo p alpha * geomTailOne p beta +
              geomTailOne p alpha * geomTailTwo p beta +
              (2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta))) :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg hlogp k)
    _ = (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) *
        (geomTailTwo p alpha * geomTailOne p beta +
          geomTailOne p alpha * geomTailTwo p beta +
          (2 : ℝ) ^ k * (geomTailTwo p alpha * geomTailTwo p beta)) := by ring

private theorem summable_pair_two_one {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => geomTailTwo p ab.1 * geomTailOne p ab.2) :=
  (summable_geomTailTwo hp).mul_of_nonneg (summable_geomTailOne hp)
    (geomTailTwo_nonneg p) (geomTailOne_nonneg p)

private theorem summable_pair_one_two {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => geomTailOne p ab.1 * geomTailTwo p ab.2) :=
  (summable_geomTailOne hp).mul_of_nonneg (summable_geomTailTwo hp)
    (geomTailOne_nonneg p) (geomTailTwo_nonneg p)

private theorem summable_pair_two_two {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ => geomTailTwo p ab.1 * geomTailTwo p ab.2) :=
  (summable_geomTailTwo hp).mul_of_nonneg (summable_geomTailTwo hp)
    (geomTailTwo_nonneg p) (geomTailTwo_nonneg p)

theorem summable_selbergCorrectionLogPowerMajorant
    (k : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ =>
      selbergCorrectionLogPowerMajorant k p ab.1 ab.2) := by
  have h := (((summable_pair_two_one hp).add (summable_pair_one_two hp)).add
    ((summable_pair_two_two hp).mul_left ((2 : ℝ) ^ k))).mul_left
      (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2)
  exact h.congr (fun ab => by rw [selbergCorrectionLogPowerMajorant])

/-- The `ell^(1 : ℕ)` mass of the `k`-th local jet. -/
theorem tsum_selbergCorrectionLogPowerMajorant_le
    (k : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (∑' ab : ℕ × ℕ, selbergCorrectionLogPowerMajorant k p ab.1 ab.2) ≤
      (8 + 4 * (2 : ℝ) ^ k) * Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2 := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith)
  have hTO : (∑' ab : ℕ × ℕ,
      geomTailTwo p ab.1 * geomTailOne p ab.2) ≤ 4 := by
    rw [← (summable_geomTailTwo hp).tsum_mul_tsum (summable_geomTailOne hp)
      (summable_pair_two_one hp)]
    have h1 := tsum_geomTailTwo_le hp
    have h2 := tsum_geomTailOne_le hp
    have hn1 : 0 ≤ ∑' alpha : ℕ, geomTailTwo p alpha :=
      tsum_nonneg (geomTailTwo_nonneg p)
    have hn2 : 0 ≤ ∑' beta : ℕ, geomTailOne p beta :=
      tsum_nonneg (geomTailOne_nonneg p)
    nlinarith
  have hOT : (∑' ab : ℕ × ℕ,
      geomTailOne p ab.1 * geomTailTwo p ab.2) ≤ 4 := by
    rw [← (summable_geomTailOne hp).tsum_mul_tsum (summable_geomTailTwo hp)
      (summable_pair_one_two hp)]
    have h1 := tsum_geomTailOne_le hp
    have h2 := tsum_geomTailTwo_le hp
    have hn1 : 0 ≤ ∑' alpha : ℕ, geomTailOne p alpha :=
      tsum_nonneg (geomTailOne_nonneg p)
    have hn2 : 0 ≤ ∑' beta : ℕ, geomTailTwo p beta :=
      tsum_nonneg (geomTailTwo_nonneg p)
    nlinarith
  have hTT : (∑' ab : ℕ × ℕ,
      geomTailTwo p ab.1 * geomTailTwo p ab.2) ≤ 4 := by
    rw [← (summable_geomTailTwo hp).tsum_mul_tsum (summable_geomTailTwo hp)
      (summable_pair_two_two hp)]
    have h1 := tsum_geomTailTwo_le hp
    have hn : 0 ≤ ∑' alpha : ℕ, geomTailTwo p alpha :=
      tsum_nonneg (geomTailTwo_nonneg p)
    nlinarith
  have hexpand :
      (∑' ab : ℕ × ℕ, selbergCorrectionLogPowerMajorant k p ab.1 ab.2) =
        (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) *
          ((∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) +
            (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) +
            (2 : ℝ) ^ k *
              (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2)) := by
    calc
      (∑' ab : ℕ × ℕ, selbergCorrectionLogPowerMajorant k p ab.1 ab.2) =
          ∑' ab : ℕ × ℕ, (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) *
            (geomTailTwo p ab.1 * geomTailOne p ab.2 +
              geomTailOne p ab.1 * geomTailTwo p ab.2 +
              (2 : ℝ) ^ k * (geomTailTwo p ab.1 * geomTailTwo p ab.2)) :=
        tsum_congr (fun ab => by rw [selbergCorrectionLogPowerMajorant])
      _ = _ := by
        rw [tsum_mul_left,
          ((summable_pair_two_one hp).add (summable_pair_one_two hp)).tsum_add
            ((summable_pair_two_two hp).mul_left ((2 : ℝ) ^ k)),
          (summable_pair_two_one hp).tsum_add (summable_pair_one_two hp),
          tsum_mul_left]
  rw [hexpand]
  have hsum :
      (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) +
          (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) +
          (2 : ℝ) ^ k *
            (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2) ≤
        8 + 4 * (2 : ℝ) ^ k := by
    have hk : 0 ≤ (2 : ℝ) ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hTT hk]
  have hfac : 0 ≤ Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2 := by positivity
  calc
    (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) *
        ((∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailOne p ab.2) +
          (∑' ab : ℕ × ℕ, geomTailOne p ab.1 * geomTailTwo p ab.2) +
          (2 : ℝ) ^ k *
            (∑' ab : ℕ × ℕ, geomTailTwo p ab.1 * geomTailTwo p ab.2))
        ≤ (Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) *
            (8 + 4 * (2 : ℝ) ^ k) := mul_le_mul_of_nonneg_left hsum hfac
    _ = (8 + 4 * (2 : ℝ) ^ k) * Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2 := by ring

theorem summable_abs_selbergCorrectionLogPowerLocal
    (k : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun ab : ℕ × ℕ =>
      |selbergCorrectionLogPowerLocal k p ab.1 ab.2|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun ab => abs_selbergCorrectionLogPowerLocal_le k hp ab.1 ab.2)
    (summable_selbergCorrectionLogPowerMajorant k hp)

theorem tsum_abs_selbergCorrectionLogPowerLocal_le
    (k : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (∑' ab : ℕ × ℕ, |selbergCorrectionLogPowerLocal k p ab.1 ab.2|) ≤
      (8 + 4 * (2 : ℝ) ^ k) * Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2 := by
  refine le_trans ?_ (tsum_selbergCorrectionLogPowerMajorant_le k hp)
  exact Summable.tsum_le_tsum
    (fun ab => abs_selbergCorrectionLogPowerLocal_le k hp ab.1 ab.2)
    (summable_abs_selbergCorrectionLogPowerLocal k hp)
    (summable_selbergCorrectionLogPowerMajorant k hp)

/-- Prime masses of every fixed local jet are summable. -/
theorem summable_selbergCorrectionLogPowerPrimeBound (k : ℕ) :
    Summable (fun p : ℕ =>
      (8 + 4 * (2 : ℝ) ^ k) * Real.log (p : ℝ) ^ k / (p : ℝ) ^ 2) := by
  have hbase := RHTower.summable_abs_log_natCast_pow_mul_rpow_neg k 2 (by norm_num)
  have hnonneg : ∀ p : ℕ, 0 ≤ Real.log (p : ℝ) := by
    intro p
    rcases p with _ | p
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le p))
  refine (hbase.mul_left (8 + 4 * (2 : ℝ) ^ k)).congr ?_
  intro p
  rw [Real.rpow_neg (Nat.cast_nonneg p)]
  rw [Real.rpow_two]
  rw [abs_of_nonneg (hnonneg p)]
  simp only [div_eq_mul_inv]
  ring

end

end RHTower.Sieve
