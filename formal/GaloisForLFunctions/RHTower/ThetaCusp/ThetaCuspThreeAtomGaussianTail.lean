import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomFourthNumerator
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform Gaussian tail beyond the first three theta atoms

For `q ≥ π` and every natural power through twelve, the sum beginning
at `n = 4` is at most twice its first term. The proof retains the exact
leading decay `exp(-15q)` and bounds the remaining terms geometrically.
These are the powers needed for the first four source derivatives.
-/

open scoped BigOperators

namespace RHTower.ThetaCuspThreeAtomFourth

/-- Gaussian moment summand with the first three positive atoms removed. -/
noncomputable def gaussianTailWeight (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ)+4)^m * Real.exp (-((((k : ℝ)+4)^2-1)*q))

theorem gaussianTailWeight_nonneg (m : ℕ) (q : ℝ) (k : ℕ) :
    0 ≤ gaussianTailWeight m q k := by unfold gaussianTailWeight; positivity

theorem add_four_le_geometric (k : ℕ) : (k : ℝ)+4 ≤ 4*(2:ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast
    rw [pow_succ]
    linarith

theorem gaussianTailWeight_le_geometric {m : ℕ} (hm : m ≤ 12)
    {q : ℝ} (hq : Real.pi ≤ q) (k : ℕ) :
    gaussianTailWeight m q k ≤ 4^m * Real.exp (-15*q) * (1/2:ℝ)^k := by
  have hq0 : 0 ≤ q := Real.pi_pos.le.trans hq
  have hp : ((k : ℝ)+4)^m ≤ 4^m * ((2:ℝ)^m)^k := by
    calc
      _ ≤ (4*(2:ℝ)^k)^m := pow_le_pow_left₀ (by positivity) (add_four_le_geometric k) m
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k m]
  have he : Real.exp (-((((k:ℝ)+4)^2-1)*q)) ≤
      Real.exp (-15*q) * Real.exp (-8*q)^k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg (k:ℝ)) hq0]
  have hr : (2:ℝ)^m * Real.exp (-8*q) ≤ 1/2 := by
    have hp12 : (2:ℝ)^m ≤ 4096 := by
      calc
        _ ≤ (2:ℝ)^12 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm
        _ = 4096 := by norm_num
    have he8 := expDecay_le 8 hq
    norm_num at he8
    calc
      _ ≤ 4096 * (1 / 78310985281 : ℝ) := by
        gcongr
        simpa only [neg_mul] using he8
      _ ≤ 1/2 := by norm_num
  unfold gaussianTailWeight
  calc
    _ ≤ (4^m * ((2:ℝ)^m)^k) * (Real.exp (-15*q) * Real.exp (-8*q)^k) := by gcongr
    _ = 4^m * Real.exp (-15*q) * ((2:ℝ)^m * Real.exp (-8*q))^k := by
      rw [mul_pow]
      ring
    _ ≤ _ := by gcongr

theorem summable_gaussianTailWeight {m : ℕ} (hm : m ≤ 12)
    {q : ℝ} (hq : Real.pi ≤ q) : Summable (gaussianTailWeight m q) := by
  apply Summable.of_nonneg_of_le (gaussianTailWeight_nonneg m q)
    (gaussianTailWeight_le_geometric hm hq)
  exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _

/-- The complete infinite Gaussian tail is bounded by twice its first summand. -/
theorem tsum_gaussianTailWeight_le {m : ℕ} (hm : m ≤ 12)
    {q : ℝ} (hq : Real.pi ≤ q) :
    (∑' k : ℕ, gaussianTailWeight m q k) ≤ 2*4^m * Real.exp (-15*q) := by
  have hg : Summable (fun k : ℕ => 4^m * Real.exp (-15*q) * (1/2:ℝ)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  calc
    _ ≤ ∑' k : ℕ, 4^m * Real.exp (-15*q) * (1/2:ℝ)^k :=
      (summable_gaussianTailWeight hm hq).tsum_le_tsum
        (gaussianTailWeight_le_geometric hm hq) hg
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

/-- Gaussian moments of the first three positive atoms. -/
noncomputable def headGaussianWeight (m : ℕ) (q : ℝ) : ℝ :=
  1+(2:ℝ)^m*Real.exp (-3*q)+(3:ℝ)^m*Real.exp (-8*q)

theorem headGaussianWeight_add_tail_lt_two {m : ℕ} (hm : m ≤ 12)
    {q : ℝ} (hq : Real.pi ≤ q) :
    headGaussianWeight m q + (∑' k : ℕ, gaussianTailWeight m q k) < 2 := by
  have hp2 : (2:ℝ)^m ≤ 4096 := by
    calc _ ≤ (2:ℝ)^12 := pow_le_pow_right₀ (by norm_num) hm
         _ = _ := by norm_num
  have hp3 : (3:ℝ)^m ≤ 531441 := by
    calc _ ≤ (3:ℝ)^12 := pow_le_pow_right₀ (by norm_num) hm
         _ = _ := by norm_num
  have hp4 : (4:ℝ)^m ≤ 16777216 := by
    calc _ ≤ (4:ℝ)^12 := pow_le_pow_right₀ (by norm_num) hm
         _ = _ := by norm_num
  have he3 : Real.exp (-3*q) ≤ 1/(23:ℝ)^3 := expDecay_le 3 hq
  have he8 : Real.exp (-8*q) ≤ 1/(23:ℝ)^8 := expDecay_le 8 hq
  have he15 : Real.exp (-15*q) ≤ 1/(23:ℝ)^15 := expDecay_le 15 hq
  have h2 := mul_le_mul hp2 he3 (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 4096)
  have h3 := mul_le_mul hp3 he8 (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 531441)
  have ht : (∑' k : ℕ, gaussianTailWeight m q k) ≤
      2*16777216*(1/(23:ℝ)^15) := by
    apply (tsum_gaussianTailWeight_le hm hq).trans
    gcongr
  have hsum : headGaussianWeight m q + (∑' k : ℕ, gaussianTailWeight m q k) ≤
      1+4096*(1/(23:ℝ)^3)+531441*(1/(23:ℝ)^8)+2*16777216*(1/(23:ℝ)^15) := by
    unfold headGaussianWeight
    linarith
  exact hsum.trans_lt (by norm_num)

theorem headGaussianWeight_lt_two {m : ℕ} (hm : m ≤ 12)
    {q : ℝ} (hq : Real.pi ≤ q) : headGaussianWeight m q < 2 := by
  have ht : 0 ≤ ∑' k : ℕ, gaussianTailWeight m q k :=
    tsum_nonneg (gaussianTailWeight_nonneg m q)
  linarith [headGaussianWeight_add_tail_lt_two hm hq]

end RHTower.ThetaCuspThreeAtomFourth
