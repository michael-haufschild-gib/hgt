import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Gamma jump multiplier and its elementary growth bound

The polar-Gamma jump operator has the real Fourier multiplier

`r(η) = 2 Σ_{n ≥ 1} η² / (n(n² + η²))`.

Every term is nonnegative and dominated by `|η|/(2n²)`, because `n² + η² ≥ 2n|η|`.  Summing gives the
elementary linear bound

`0 ≤ r(η) ≤ S|η|`,   `S = Σ_{n ≥ 1} n^{-2}`,

which is all that is needed to place the jump operator in the class `H¹(ℝ;X) → L²(ℝ;X)`: the
logarithmic sharpening `r(η) = O(log(2+|η|))` is stronger, but the linear bound already dominates it
and is what the domain statement consumes.
-/

open Filter

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The `n`-th term of the Gamma jump multiplier series, indexed from zero. -/
def gammaJumpTerm (η : ℝ) (n : ℕ) : ℝ :=
  η ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ)))

/-- The Gamma jump multiplier `r(η) = 2 Σ_{n≥1} η²/(n(n²+η²))`. -/
def gammaJumpMultiplier (η : ℝ) : ℝ := 2 * ∑' n : ℕ, gammaJumpTerm η n

theorem gammaJumpTerm_nonneg (η : ℝ) (n : ℕ) : 0 ≤ gammaJumpTerm η n := by
  rw [gammaJumpTerm]
  positivity

/-- **The termwise arithmetic–geometric bound.**  `n² + η² ≥ 2n|η|` makes every term at most
`|η|/(2n²)`. -/
theorem gammaJumpTerm_le (η : ℝ) (n : ℕ) :
    gammaJumpTerm η n ≤ |η| / (2 * (((n : ℝ) + 1) ^ (2 : ℕ))) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden : (0 : ℝ) < ((n : ℝ) + 1) * ((((n : ℝ) + 1)) ^ (2 : ℕ) + η ^ (2 : ℕ)) := by positivity
  have hden2 : (0 : ℝ) < 2 * (((n : ℝ) + 1) ^ (2 : ℕ)) := by positivity
  have habs : |η| ^ (2 : ℕ) = η ^ (2 : ℕ) := sq_abs η
  have hamgm : 2 * ((n : ℝ) + 1) * |η| ≤ (((n : ℝ) + 1)) ^ (2 : ℕ) + η ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (((n : ℝ) + 1) - |η|), habs]
  have key : |η| * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) * |η|)
      ≤ |η| * ((n : ℝ) + 1) * ((((n : ℝ) + 1)) ^ (2 : ℕ) + η ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hamgm (by positivity)
  rw [gammaJumpTerm, div_le_div_iff₀ hden hden2]
  nlinarith [key, habs]

theorem summable_inv_succ_sq : Summable (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ))) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (2 : ℕ))) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr fun n => ?_
  push_cast
  ring

theorem summable_gammaJumpMajorant (η : ℝ) :
    Summable (fun n : ℕ => |η| / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))) := by
  have h := summable_inv_succ_sq.mul_left (|η| / 2)
  refine h.congr fun n => ?_
  rw [mul_one_div, div_div]

theorem summable_gammaJumpTerm (η : ℝ) : Summable (gammaJumpTerm η) :=
  Summable.of_nonneg_of_le (gammaJumpTerm_nonneg η) (gammaJumpTerm_le η)
    (summable_gammaJumpMajorant η)

theorem gammaJumpMultiplier_nonneg (η : ℝ) : 0 ≤ gammaJumpMultiplier η := by
  have h : (0 : ℝ) ≤ ∑' n : ℕ, gammaJumpTerm η n := tsum_nonneg (gammaJumpTerm_nonneg η)
  rw [gammaJumpMultiplier]
  linarith

/-- **The elementary linear bound.**  The Gamma jump multiplier grows at most linearly, with the
explicit constant `Σ n^{-2}`. -/
theorem gammaJumpMultiplier_le (η : ℝ) :
    gammaJumpMultiplier η ≤ (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ))) * |η| := by
  have hle : ∑' n : ℕ, gammaJumpTerm η n
      ≤ ∑' n : ℕ, |η| / (2 * (((n : ℝ) + 1) ^ (2 : ℕ))) :=
    Summable.tsum_mono (summable_gammaJumpTerm η) (summable_gammaJumpMajorant η)
      (gammaJumpTerm_le η)
  have hval : ∑' n : ℕ, |η| / (2 * (((n : ℝ) + 1) ^ (2 : ℕ)))
      = (|η| / 2) * ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [mul_one_div, div_div]
  rw [hval] at hle
  calc gammaJumpMultiplier η = 2 * ∑' n : ℕ, gammaJumpTerm η n := rfl
    _ ≤ 2 * ((|η| / 2) * ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ))) := by linarith
    _ = (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ))) * |η| := by ring

/-- The affine form of the growth bound, matching the `H¹ → L²` domain statement. -/
theorem abs_gammaJumpMultiplier_le (η : ℝ) :
    |gammaJumpMultiplier η|
      ≤ (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ))) * (1 + |η|) := by
  have hS : 0 ≤ ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ (2 : ℕ)) :=
    tsum_nonneg fun n => by positivity
  rw [abs_of_nonneg (gammaJumpMultiplier_nonneg η)]
  refine le_trans (gammaJumpMultiplier_le η) ?_
  nlinarith [hS, abs_nonneg η]

end GaloisForLFunctions.RHTower
