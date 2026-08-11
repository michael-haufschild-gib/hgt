import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockProfile
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Euler--Green anomaly of the source-horizontal prime-clock profile

Prime-clock normalization does more than select an odd universal profile.  Its logarithmic-depth
moments apply the inverse Euler operator to `sinh`: the coefficient of degree `2k+1` is divided by
`2k+1`.  Consequently the retained profile is the exact defect `(D⁻¹ - 1) sinh`, where
`D = u d/du`.  The neutral linear mode lies in the kernel, while every higher odd mode survives.

This identifies a sharp source obstruction.  Reflection only reverses the defect and neutral-jet
transport only kills its degree-one mode.  Any producer which annihilates the full profile must
supply an Euler--Green mean-value law before bounded scalarization.
-/

open Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Inverse-Euler Green average of the odd exponential carrier.  Coefficientwise this is
`D⁻¹ sinh`, with `D = u d/du`. -/
def sourceHorizontalWoldEulerGreenProfile (u : ℝ) : ℝ :=
  ∑' k : ℕ,
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (1 / (2 * k + 1 : ℕ) : ℝ)

private theorem summable_sourceHorizontalWoldEulerGreenProfile (u : ℝ) :
    Summable (fun k : ℕ =>
      u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (1 / (2 * k + 1 : ℕ) : ℝ)) := by
  refine Summable.of_norm_bounded (Real.hasSum_sinh |u|).summable ?_
  intro k
  have hden : (1 : ℝ) ≤ (2 * k + 1 : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : 2 * k + 1 ≠ 0))
  have hden0 : (0 : ℝ) < (2 * k + 1 : ℕ) := by positivity
  have hinv0 : 0 ≤ (1 / (2 * k + 1 : ℕ) : ℝ) := by positivity
  have hinv_le : (1 / (2 * k + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden0).2 hden
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
  simp only [Nat.cast_nonneg, abs_of_nonneg]
  rw [abs_of_nonneg hinv0]
  exact mul_le_of_le_one_right (by positivity) hinv_le

/-- Exact coefficient-faithful identification of the universal profile as the inverse-Euler Green
defect `(D⁻¹ - 1) sinh`. -/
theorem sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh (u : ℝ) :
    sourceHorizontalWoldPrimeClockUniversalProfile u =
      sourceHorizontalWoldEulerGreenProfile u - Real.sinh u := by
  unfold sourceHorizontalWoldPrimeClockUniversalProfile
  rw [sourceHorizontalWoldEulerGreenProfile]
  calc
    (∑' k : ℕ, u ^ (2 * k + 1) / (2 * k + 1).factorial *
        ((1 / (2 * k + 1 : ℕ) : ℝ) - 1)) =
        ∑' k : ℕ,
          (u ^ (2 * k + 1) / (2 * k + 1).factorial *
            (1 / (2 * k + 1 : ℕ) : ℝ) -
          u ^ (2 * k + 1) / (2 * k + 1).factorial) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k : ℕ,
          u ^ (2 * k + 1) / (2 * k + 1).factorial *
            (1 / (2 * k + 1 : ℕ) : ℝ)) -
        ∑' k : ℕ, u ^ (2 * k + 1) / (2 * k + 1).factorial :=
      (summable_sourceHorizontalWoldEulerGreenProfile u).tsum_sub
        (Real.hasSum_sinh u).summable
    _ = (∑' k : ℕ,
          u ^ (2 * k + 1) / (2 * k + 1).factorial *
            (1 / (2 * k + 1 : ℕ) : ℝ)) - Real.sinh u := by
      rw [(Real.hasSum_sinh u).tsum_eq]

/-- Euler multiplier carried by odd degree `2k+1`. -/
def sourceHorizontalWoldEulerAnomalyMultiplier (k : ℕ) : ℝ :=
  (1 / (2 * k + 1 : ℕ) : ℝ) - 1

/-- Neutral transport kills exactly the linear Euler mode. -/
@[simp] theorem sourceHorizontalWoldEulerAnomalyMultiplier_zero :
    sourceHorizontalWoldEulerAnomalyMultiplier 0 = 0 := by
  simp [sourceHorizontalWoldEulerAnomalyMultiplier]

/-- Every multiplier is the exact relative Euler-degree defect `-2k/(2k+1)`. -/
theorem sourceHorizontalWoldEulerAnomalyMultiplier_eq (k : ℕ) :
    sourceHorizontalWoldEulerAnomalyMultiplier k =
      -(2 * k : ℝ) / (2 * k + 1 : ℕ) := by
  rw [sourceHorizontalWoldEulerAnomalyMultiplier]
  have hden : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Every higher odd Euler mode survives, with the same orientation. -/
theorem sourceHorizontalWoldEulerAnomalyMultiplier_neg
    {k : ℕ} (hk : 0 < k) :
    sourceHorizontalWoldEulerAnomalyMultiplier k < 0 := by
  rw [sourceHorizontalWoldEulerAnomalyMultiplier_eq]
  have hnum : 0 < (2 * k : ℝ) := by positivity
  have hden : 0 < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  exact neg_lt_zero.mpr (div_pos hnum hden)

/-- Degree one is the unique odd Euler mode erased by prime-clock centering. -/
theorem sourceHorizontalWoldEulerAnomalyMultiplier_eq_zero_iff (k : ℕ) :
    sourceHorizontalWoldEulerAnomalyMultiplier k = 0 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    linarith [sourceHorizontalWoldEulerAnomalyMultiplier_neg hkpos]
  · intro hk
    subst k
    exact sourceHorizontalWoldEulerAnomalyMultiplier_zero

private theorem hasDerivAt_sourceHorizontalWoldEulerGreenTerm
    (k : ℕ) (u : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        y ^ (2 * k + 1) / (2 * k + 1).factorial *
          (1 / (2 * k + 1 : ℕ) : ℝ))
      (u ^ (2 * k) / (2 * k + 1).factorial) u := by
  have hpow := hasDerivAt_pow (2 * k + 1) u
  have h := (hpow.div_const ((2 * k + 1).factorial : ℝ)).mul_const
    (1 / (2 * k + 1 : ℕ) : ℝ)
  apply h.congr_deriv
  have hden : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast at hden ⊢
  field_simp

private theorem summable_sourceHorizontalWoldEulerGreenDerivativeMajorant
    (r : ℝ) :
    Summable (fun k : ℕ =>
      r ^ (2 * k + 1) / (2 * k + 1).factorial) :=
  (Real.hasSum_sinh r).summable

/-- The Green profile is genuinely the inverse Euler derivative of `sinh`, not merely a formal
coefficient analogy. -/
theorem hasDerivAt_sourceHorizontalWoldEulerGreenProfile (u : ℝ) :
    HasDerivAt sourceHorizontalWoldEulerGreenProfile
      (∑' k : ℕ, u ^ (2 * k) / (2 * k + 1).factorial) u := by
  let r : ℝ := |u| + 1
  have hr : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg u]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsum : Summable (fun k : ℕ =>
      r ^ (2 * k + 1) / (2 * k + 1).factorial) :=
    summable_sourceHorizontalWoldEulerGreenDerivativeMajorant r
  have hu : u ∈ Metric.ball (0 : ℝ) r := by
    rw [mem_ball_zero_iff]
    dsimp [r]
    linarith
  have hzero : (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := by
    rw [mem_ball_zero_iff, norm_zero]
    exact hr0
  unfold sourceHorizontalWoldEulerGreenProfile
  apply hasDerivAt_tsum_of_isPreconnected hsum Metric.isOpen_ball
      (convex_ball (0 : ℝ) r).isPreconnected
      (fun k y _ => hasDerivAt_sourceHorizontalWoldEulerGreenTerm k y) ?_
      hzero ?_ hu
  · intro k y hy
    have hyr : |y| < r := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
      exact hy
    have hyr0 : 0 ≤ r := hr0.le
    have hpow : |y| ^ (2 * k) ≤ r ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg y) hyr.le _
    have hstep : r ^ (2 * k) ≤ r ^ (2 * k + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hyr0 _) hr
    rw [Real.norm_eq_abs, abs_div, abs_pow]
    simp only [Nat.cast_nonneg, abs_of_nonneg]
    exact div_le_div_of_nonneg_right (hpow.trans hstep) (by positivity)
  · simp

/-- Differential Euler--Green law: `D (D⁻¹ sinh) = sinh`. -/
theorem sourceHorizontalWoldEulerGreenProfile_mul_deriv (u : ℝ) :
    u * deriv sourceHorizontalWoldEulerGreenProfile u = Real.sinh u := by
  rw [(hasDerivAt_sourceHorizontalWoldEulerGreenProfile u).deriv]
  have hsummable : Summable (fun k : ℕ =>
      u ^ (2 * k) / (2 * k + 1).factorial) := by
    let r : ℝ := |u| + 1
    have hr : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg u]
    refine Summable.of_norm_bounded
      (summable_sourceHorizontalWoldEulerGreenDerivativeMajorant r) ?_
    intro k
    have hu_le : |u| ≤ r := by dsimp [r]; linarith
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hpow : |u| ^ (2 * k) ≤ r ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg u) hu_le _
    have hstep : r ^ (2 * k) ≤ r ^ (2 * k + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hr0 _) hr
    rw [Real.norm_eq_abs, abs_div, abs_pow]
    simp only [Nat.cast_nonneg, abs_of_nonneg]
    exact div_le_div_of_nonneg_right (hpow.trans hstep) (by positivity)
  calc
    u * (∑' k : ℕ, u ^ (2 * k) / (2 * k + 1).factorial) =
        ∑' k : ℕ, u * (u ^ (2 * k) / (2 * k + 1).factorial) := by
          rw [hsummable.tsum_mul_left]
    _ = ∑' k : ℕ, u ^ (2 * k + 1) / (2 * k + 1).factorial := by
      apply tsum_congr
      intro k
      rw [pow_succ']
      ring
    _ = Real.sinh u := (Real.hasSum_sinh u).tsum_eq

/-- Polar work is the positive Euler--Green endpoint defect.  This welds the Wold source profile
to the Green/virial language without losing a coefficient or choosing one reflection orientation. -/
theorem sourceHorizontalWoldPrimeClockPolarRateWork_eq_eulerGreenDefect (u : ℝ) :
    sourceHorizontalWoldPrimeClockPolarRateWork u =
      Real.log 2 / 2 * u *
        (Real.sinh u - sourceHorizontalWoldEulerGreenProfile u) := by
  rw [sourceHorizontalWoldPrimeClockPolarRateWork,
    sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh]
  ring

/-- A source Euler--Green mean-value law annihilates the full coefficient-faithful profile.  This is
the exact missing producer shape; unlike reflection, it identifies endpoint and Green average on
the same pre-zero carrier. -/
theorem sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_of_eulerGreen_fixed
    {u : ℝ} (hfixed : sourceHorizontalWoldEulerGreenProfile u = Real.sinh u) :
    sourceHorizontalWoldPrimeClockUniversalProfile u = 0 := by
  rw [sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh, hfixed, sub_self]

/-- Conversely, vanishing of the retained source profile is exactly the Euler--Green mean-value
law.  Thus this law is neither weaker nor silently stronger than the missing scalar producer. -/
theorem sourceHorizontalWoldEulerGreen_fixed_iff_profile_zero (u : ℝ) :
    sourceHorizontalWoldEulerGreenProfile u = Real.sinh u ↔
      sourceHorizontalWoldPrimeClockUniversalProfile u = 0 := by
  rw [sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh]
  constructor <;> intro h <;> linarith

end

end RHTower
