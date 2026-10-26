import GaloisForLFunctions.BiScaleUncertainty.FiniteHorizonPositiveCoercivity
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The exact dyadic mantissa tent on integer windows

On each dyadic level the signal is the normalized triangle. Adjacent levels
join at zero, and doubling preserves the signal exactly.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- The specified integer mantissa triangle, extended by zero at the unused index zero. -/
def dyadicMantissaTent (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    min ((n : ℝ) - (2 : ℝ) ^ Nat.log 2 n)
      (2 * (2 : ℝ) ^ Nat.log 2 n - (n : ℝ)) / (2 : ℝ) ^ Nat.log 2 n

theorem dyadicMantissaTent_zero : dyadicMantissaTent 0 = 0 := by
  simp [dyadicMantissaTent]

/-- Both ends of every dyadic level have value zero. -/
theorem dyadicMantissaTent_pow (k : ℕ) : dyadicMantissaTent (2 ^ k) = 0 := by
  have hn : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero k (by decide)
  rw [dyadicMantissaTent, if_neg hn, Nat.log_pow (by decide : 1 < (2 : ℕ))]
  simp only [Nat.cast_pow, Nat.cast_ofNat, sub_self]
  have hp : 0 ≤ (2 : ℝ) ^ k := by positivity
  have hmin : 0 ≤ 2 * (2 : ℝ) ^ k - (2 : ℝ) ^ k := by linarith only [hp]
  rw [min_eq_left hmin, zero_div]

/-- The triangle formula holds on the entire closed level, including its shared right endpoint. -/
theorem dyadicMantissaTent_eq_level (k n : ℕ) (hlo : 2 ^ k ≤ n) (hhi : n ≤ 2 ^ (k + 1)) :
    dyadicMantissaTent n =
      min ((n : ℝ) - (2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1) - (n : ℝ)) / (2 : ℝ) ^ k := by
  rcases eq_or_lt_of_le hhi with h | h
  · subst n
    rw [dyadicMantissaTent_pow]
    simp only [Nat.cast_pow, Nat.cast_ofNat, sub_self]
    rw [min_eq_right (by
      rw [pow_succ']
      have hp : 0 ≤ (2 : ℝ) ^ k := by positivity
      linarith only [hp]), zero_div]
  · have hn : n ≠ 0 := (lt_of_lt_of_le (by positivity : 0 < (2 : ℕ) ^ k) hlo).ne'
    rw [dyadicMantissaTent, if_neg hn, Nat.log_eq_of_pow_le_of_lt_pow hlo h, pow_succ']

/-- The original mantissa-coordinate formula, with its exact denominator. -/
theorem dyadicMantissaTent_pow_add (k j : ℕ) (hj : j ≤ 2 ^ k) :
    dyadicMantissaTent (2 ^ k + j) =
      min (j : ℝ) ((2 : ℝ) ^ k - (j : ℝ)) / (2 : ℝ) ^ k := by
  have hhi : 2 ^ k + j ≤ 2 ^ (k + 1) := by
    rw [pow_succ']
    omega
  rw [dyadicMantissaTent_eq_level k (2 ^ k + j) (Nat.le_add_right _ _) hhi]
  push_cast
  rw [pow_succ']
  congr 1
  congr 1 <;> ring

/-- The exact signal stays in the interval `[0,1/2]`. -/
theorem dyadicMantissaTent_bounds (n : ℕ) : 0 ≤ dyadicMantissaTent n ∧ dyadicMantissaTent n ≤ 1 / 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [dyadicMantissaTent_zero]
    constructor <;> norm_num
  · let k := Nat.log 2 n
    have hlo : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn
    have hhi : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
    have hloR : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hlo
    have hhiR : (n : ℝ) ≤ 2 * (2 : ℝ) ^ k := by
      have hh : (n : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hhi
      rw [pow_succ'] at hh
      exact hh.le
    have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [dyadicMantissaTent, if_neg hn]
    change 0 ≤ min ((n : ℝ) - (2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k - n) / (2 : ℝ) ^ k ∧ _
    constructor
    · exact div_nonneg (le_min (sub_nonneg.mpr hloR) (sub_nonneg.mpr hhiR)) hq.le
    · apply (div_le_iff₀ hq).mpr
      have h₁ := min_le_left ((n : ℝ) - (2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k - n)
      have h₂ := min_le_right ((n : ℝ) - (2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k - n)
      linarith only [h₁, h₂]

/-- Doubling preserves the exact normalized mantissa, hence the tent. -/
theorem dyadicMantissaTent_two_mul (n : ℕ) : dyadicMantissaTent (2 * n) = dyadicMantissaTent n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [mul_zero]
  · rw [Nat.mul_comm 2 n, dyadicMantissaTent, if_neg (Nat.mul_ne_zero hn (by decide)),
      dyadicMantissaTent, if_neg hn, Nat.log_mul_base (by decide : 1 < (2 : ℕ)) hn]
    simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ']
    let q : ℝ := (2 : ℝ) ^ Nat.log 2 n
    have hq : q ≠ 0 := by dsimp [q]; positivity
    change min ((n : ℝ) * 2 - 2 * q) (2 * (2 * q) - (n : ℝ) * 2) / (2 * q) =
      min ((n : ℝ) - q) (2 * q - n) / q
    by_cases h : (n : ℝ) - q ≤ 2 * q - n
    · rw [min_eq_left h, min_eq_left (by linarith only [h] :
        (n : ℝ) * 2 - 2 * q ≤ 2 * (2 * q) - (n : ℝ) * 2)]
      field_simp [hq]
    · have h' : 2 * q - (n : ℝ) ≤ n - q := (lt_of_not_ge h).le
      rw [min_eq_right h', min_eq_right (by linarith only [h'] :
        2 * (2 * q) - (n : ℝ) * 2 ≤ (n : ℝ) * 2 - 2 * q)]
      field_simp [hq]

/-- The adjacent increment is bounded by the reciprocal width of its dyadic level. -/
theorem abs_dyadicMantissaTent_succ_sub_le {n : ℕ} (hn : 1 ≤ n) :
    |dyadicMantissaTent (n + 1) - dyadicMantissaTent n| ≤ 1 / (2 : ℝ) ^ Nat.log 2 n := by
  let k := Nat.log 2 n
  have hn0 : n ≠ 0 := by omega
  have hlo : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn0
  have hhi : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [dyadicMantissaTent_eq_level k (n + 1) (hlo.trans (Nat.le_succ n)) (by omega),
    dyadicMantissaTent_eq_level k n hlo hhi.le, ← sub_div, abs_div, abs_of_pos hq]
  apply div_le_div_of_nonneg_right _ hq.le
  have hb := abs_min_sub_min_le_max
    (((n + 1 : ℕ) : ℝ) - (2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1) - ((n + 1 : ℕ) : ℝ))
    ((n : ℝ) - (2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1) - (n : ℝ))
  have h₁ : (((n + 1 : ℕ) : ℝ) - (2 : ℝ) ^ k) - ((n : ℝ) - (2 : ℝ) ^ k) = 1 := by
    push_cast
    ring
  have h₂ : ((2 : ℝ) ^ (k + 1) - ((n + 1 : ℕ) : ℝ)) -
      ((2 : ℝ) ^ (k + 1) - (n : ℝ)) = -1 := by
    push_cast
    ring
  rw [h₁, h₂] at hb
  norm_num at hb
  simpa only [Nat.cast_add, Nat.cast_one] using hb

/-- Each adjacent square is controlled by a telescoping reciprocal difference. -/
theorem dyadicMantissaTent_succ_sub_sq_le {n : ℕ} (hn : 1 ≤ n) :
    (dyadicMantissaTent (n + 1) - dyadicMantissaTent n) ^ 2 ≤
      4 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  let q : ℝ := (2 : ℝ) ^ Nat.log 2 n
  have hq : 0 < q := by dsimp [q]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hhi : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  have hhiR : (n : ℝ) + 1 ≤ 2 * q := by
    have hh : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast hhi
    simpa only [Nat.cast_add, Nat.cast_one, pow_succ'] using hh
  have hnq : (n : ℝ) ≤ 2 * q := by linarith only [hhiR]
  have hprod := mul_le_mul hnq hhiR (by positivity : 0 ≤ (n : ℝ) + 1) (by positivity : 0 ≤ 2 * q)
  have hrecip : (1 / q) ^ 2 ≤ 4 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [div_pow, one_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) (mul_pos hnR (by positivity))).mpr
    nlinarith only [hprod]
  have hb := abs_dyadicMantissaTent_succ_sub_le hn
  change |dyadicMantissaTent (n + 1) - dyadicMantissaTent n| ≤ 1 / q at hb
  have hs : (dyadicMantissaTent (n + 1) - dyadicMantissaTent n) ^ 2 ≤ (1 / q) ^ 2 := by
    have hp : 0 ≤ 1 / q := by positivity
    nlinarith only [hb, hp, abs_nonneg (dyadicMantissaTent (n + 1) - dyadicMantissaTent n),
      sq_abs (dyadicMantissaTent (n + 1) - dyadicMantissaTent n)]
  exact hs.trans hrecip


/-- The native doubling energy vanishes identically for the actual tent. -/
theorem multiplicativeScaleEnergy_dyadicMantissaTent (N : ℕ) :
    multiplicativeScaleEnergy 2 N dyadicMantissaTent = 0 := by
  simp only [multiplicativeScaleEnergy, Finset.Icc_self, Finset.sum_singleton,
    dyadicMantissaTent_two_mul, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]

/-- Adjacent energy is bounded by an explicit telescoping expression. -/
theorem additiveStepEnergy_dyadicMantissaTent_le {N : ℕ} (hN : 2 ≤ N) :
    additiveStepEnergy N dyadicMantissaTent ≤ 2 - 4 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h₁ : dyadicMantissaTent 1 = 0 := by simpa only [pow_zero] using dyadicMantissaTent_pow 0
    have h₂ : dyadicMantissaTent 2 = 0 := by simpa only [pow_one] using dyadicMantissaTent_pow 1
    norm_num [additiveStepEnergy, h₁, h₂]
  | succ N hN ih =>
    have hn : 1 ≤ N := by omega
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hstep := dyadicMantissaTent_succ_sub_sq_le hn
    have hsum : additiveStepEnergy (N + 1) dyadicMantissaTent =
        additiveStepEnergy N dyadicMantissaTent +
          (dyadicMantissaTent (N + 1) - dyadicMantissaTent N) ^ 2 := by
      exact Finset.sum_Ico_succ_top hn _
    rw [hsum]
    calc
      _ ≤ (2 - 4 / (N : ℝ)) + 4 / ((N : ℝ) * ((N : ℝ) + 1)) := add_le_add ih hstep
      _ = 2 - 4 / ((N + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp [hNR.ne', (by positivity : (N : ℝ) + 1 ≠ 0)]
        ring

/-- The specified tent has strictly less than two units of adjacent energy. -/
theorem additiveStepEnergy_dyadicMantissaTent_lt_two {N : ℕ} (hN : 2 ≤ N) :
    additiveStepEnergy N dyadicMantissaTent < 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < 4 / (N : ℝ) := div_pos (by norm_num) hNR
  exact (additiveStepEnergy_dyadicMantissaTent_le hN).trans_lt (by linarith only [hp])

/-- Every adjacent edge of a non-root full level has exactly the reciprocal level width. -/
theorem abs_dyadicMantissaTent_level_increment (k j : ℕ) (hj : j < 2 ^ (k + 1)) :
    |dyadicMantissaTent (2 ^ (k + 1) + j + 1) -
      dyadicMantissaTent (2 ^ (k + 1) + j)| = 1 / (2 : ℝ) ^ (k + 1) := by
  rw [Nat.add_assoc, dyadicMantissaTent_pow_add (k + 1) (j + 1) (by omega),
    dyadicMantissaTent_pow_add (k + 1) j hj.le]
  have hq : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hqeq : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := pow_succ' _ _
  by_cases hhalf : j < 2 ^ k
  · have hh : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      exact_mod_cast (show j + 1 ≤ 2 ^ k by omega)
    have h₁ : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) - ((j + 1 : ℕ) : ℝ) := by
      push_cast
      linarith only [hh, hqeq]
    have h₀ : (j : ℝ) ≤ (2 : ℝ) ^ (k + 1) - (j : ℝ) := by
      linarith only [hh, hqeq]
    rw [min_eq_left h₁, min_eq_left h₀, ← sub_div, abs_div, abs_of_pos hq]
    have he : ((j + 1 : ℕ) : ℝ) - (j : ℝ) = 1 := by push_cast; ring
    rw [he, abs_one]
  · have hh : (2 : ℝ) ^ k ≤ (j : ℝ) := by exact_mod_cast (le_of_not_gt hhalf)
    have h₁ : (2 : ℝ) ^ (k + 1) - ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      push_cast
      linarith only [hh, hqeq]
    have h₀ : (2 : ℝ) ^ (k + 1) - (j : ℝ) ≤ (j : ℝ) := by
      linarith only [hh, hqeq]
    rw [min_eq_right h₁, min_eq_right h₀, ← sub_div, abs_div, abs_of_pos hq]
    have he : ((2 : ℝ) ^ (k + 1) - ((j + 1 : ℕ) : ℝ)) -
        ((2 : ℝ) ^ (k + 1) - (j : ℝ)) = -1 := by push_cast; ring
    rw [he, abs_neg, abs_one]

/-- Including the transition to the next level, each non-root full level has exact energy. -/
theorem dyadicMantissaTent_full_level_energy (k : ℕ) :
    (∑ j ∈ Finset.range (2 ^ (k + 1)),
      (dyadicMantissaTent (2 ^ (k + 1) + j + 1) -
        dyadicMantissaTent (2 ^ (k + 1) + j)) ^ 2) = 1 / (2 : ℝ) ^ (k + 1) := by
  have he (j : ℕ) (hj : j ∈ Finset.range (2 ^ (k + 1))) :
      (dyadicMantissaTent (2 ^ (k + 1) + j + 1) -
        dyadicMantissaTent (2 ^ (k + 1) + j)) ^ 2 = (1 / (2 : ℝ) ^ (k + 1)) ^ 2 := by
    rw [← sq_abs, abs_dyadicMantissaTent_level_increment k j (Finset.mem_range.mp hj)]
  rw [Finset.sum_congr rfl he, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp


end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
