import GaloisForLFunctions.BezoutValuationIncidence.UniformFloorMeansAndMovingVaughanGrams
import GaloisForLFunctions.BezoutValuationIncidence.TheParityPairAtTheLeadingExponent

/-!
# Signed reciprocal tails below their absolute power scale

Mean-zero cancellation makes each normalized Möbius reciprocal tail tend to zero.
A common absolute bound then pays products of two normalized tails whenever their
cutoff product diverges, without requiring either cutoff separately to diverge.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false


/-- Absolute convergence identifies the omitted damped mean with its signed shifted tail. -/
theorem dampedSign_reciprocal_tail_eq_tsum {s : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hs1 : ∀ d, |s d| ≤ 1) (N : ℕ) :
    (∑' d : ℕ, dampedSignWeight s ε d / d) -
        (∑ d ∈ Icc 1 N, dampedSignWeight s ε d / d) =
      ∑' i : ℕ, ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * s (i + (N + 1)) := by
  have h := (summable_dampedSignWeight_div_of_abs_le_one hε hs1).sum_add_tsum_nat_add (N + 1)
  rw [dampedSign_sum_range_succ_eq_add_Icc, dampedSignWeight] at h
  simp only [Nat.cast_zero, div_zero, zero_add] at h
  rw [← h, add_sub_cancel_left]
  exact tsum_congr fun i => dampedSignWeight_div hε _

/-- A mean-zero bounded pattern has a reciprocal tail smaller than its absolute power scale. -/
theorem tendsto_scaled_dampedSign_reciprocal_tail_of_mean_zero {s : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hs1 : ∀ d, |s d| ≤ 1) (hmean : HasMeanValue s 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ε *
      ((∑' d : ℕ, dampedSignWeight s ε d / d) -
        ∑ d ∈ Icc 1 N, dampedSignWeight s ε d / d)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let L : ℝ := η / (2 * (2 + 1 / ε))
  have hK : 0 < 2 + 1 / ε := by positivity
  have hL : 0 < L := div_pos hη (mul_pos (by norm_num) hK)
  have hsmall : ∀ᶠ x : ℕ in atTop,
      |(∑ d ∈ Icc 1 x, s d) / (x : ℝ)| < L := by
    simpa only [abs_zero] using hmean.abs.eventually
      (gt_mem_nhds (by simpa only [abs_zero] using hL))
  obtain ⟨D, hD⟩ := eventually_atTop.mp hsmall
  filter_upwards [eventually_ge_atTop (max D 1)] with N hN
  have hN1 : 1 ≤ N := (le_max_right D 1).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hS (x : ℕ) (hx : N ≤ x) : |∑ d ∈ Icc 1 x, s d| ≤ L * x := by
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hN1.trans hx
    have h := hD x (((le_max_left D 1).trans hN).trans hx)
    rw [abs_div, abs_of_pos hx0] at h
    exact ((div_lt_iff₀ hx0).mp h).le
  have ht := (abs_tsum_tail_rpow_le_of_linear hN1 hL.le hε hs1 hS).2
  rw [← dampedSign_reciprocal_tail_eq_tsum hε hs1 N] at ht
  rw [Real.dist_eq, sub_zero, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  calc
    _ ≤ (N : ℝ) ^ ε * ((2 + 1 / ε) * L * (N : ℝ) ^ (-ε)) :=
      mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hN0.le _)
    _ = η / 2 := by
      rw [Real.rpow_neg hN0.le]
      dsimp only [L]
      field_simp [(Real.rpow_pos_of_pos hN0 ε).ne', hK.ne']
    _ < η := by linarith only [hη]

theorem pmPronicVaughanSmallDensity_eq_damped_sum (ε : ℝ) (N : ℕ) :
    pmPronicVaughanSmallDensity ε N =
      ∑ d ∈ Icc 1 N, pmPowerDampedRealWeight ε d / d := by
  simp only [pmPowerDampedRealWeight, moebiusReal, pmPronicVaughanSmallDensity]
  apply sum_congr rfl
  intro d _
  ring

/-- The explicit Vaughan mean omits exactly the signed Möbius reciprocal tail. -/
theorem pmPronicVaughanSmallDensity_tail_eq_tsum {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε N =
      ∑' i : ℕ, ((i + (N + 1) : ℕ) : ℝ) ^ (-(1 + ε)) * moebiusReal (i + (N + 1)) := by
  rw [← (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq,
    pmPronicVaughanSmallDensity_eq_damped_sum]
  exact dampedSign_reciprocal_tail_eq_tsum hε abs_moebiusReal_le_one' N

/-- The omitted signed Möbius mean is little-o of the absolute reciprocal-tail power. -/
theorem tendsto_scaled_pmPronicVaughanSmallDensity_tail {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ε *
      ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε N))
      atTop (𝓝 0) := by
  have h := tendsto_scaled_dampedSign_reciprocal_tail_of_mean_zero hε
    abs_moebiusReal_le_one' hasMeanValue_moebiusReal
  change Tendsto (fun N : ℕ => (N : ℝ) ^ ε *
    ((∑' d : ℕ, pmPowerDampedRealWeight ε d / d) -
      ∑ d ∈ Icc 1 N, pmPowerDampedRealWeight ε d / d)) atTop (𝓝 0) at h
  simpa only [(hasSum_pmPowerDampedRealWeight_div hε).tsum_eq,
    ← pmPronicVaughanSmallDensity_eq_damped_sum] using h

/-- The normalized signed tail has a cutoff-independent absolute bound. -/
theorem abs_scaled_pmPronicVaughanSmallDensity_tail_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    |(N : ℝ) ^ ε *
      ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε N)| ≤ 2 + 1 / ε := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.cast_zero, Real.zero_rpow hε.ne', zero_mul, abs_zero]
    positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS (x : ℕ) (_hx : N ≤ x) : |∑ d ∈ Icc 1 x, moebiusReal d| ≤ (1 : ℝ) * x := by
    calc
      _ ≤ ∑ d ∈ Icc 1 x, |moebiusReal d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Icc 1 x, (1 : ℝ) := sum_le_sum fun d _ => abs_moebiusReal_le_one' d
      _ = _ := by simp
  have h := (abs_tsum_tail_rpow_le_of_linear hN zero_le_one hε abs_moebiusReal_le_one' hS).2
  rw [← pmPronicVaughanSmallDensity_tail_eq_tsum hε N] at h
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
  calc
    _ ≤ (N : ℝ) ^ ε * ((2 + 1 / ε) * 1 * (N : ℝ) ^ (-ε)) :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hN0.le _)
    _ = 2 + 1 / ε := by
      rw [Real.rpow_neg hN0.le]
      field_simp [(Real.rpow_pos_of_pos hN0 ε).ne']

/-- Products of bounded vanishing tails vanish whenever the product of their indices diverges. -/
theorem tendsto_mul_of_product_indices_atTop {f : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ n, |f n| ≤ M) (hzero : Tendsto f atTop (𝓝 0))
    (U V : ℕ → ℕ) (hUV : Tendsto (fun T => U T * V T) atTop atTop) :
    Tendsto (fun T => f (U T) * f (V T)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hδ : 0 < η / (M + 1) := div_pos hη (by linarith only [hM])
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.mp hzero (η / (M + 1)) hδ
  let K := max K₀ 1
  filter_upwards [hUV.eventually_ge_atTop (K * K)] with T hT
  have hlarge : K ≤ U T ∨ K ≤ V T := by
    by_contra h
    push Not at h
    have hmul := Nat.mul_le_mul (Nat.succ_le_iff.mpr h.1) (Nat.succ_le_iff.mpr h.2)
    nlinarith only [hT, hmul, Nat.zero_le (U T), Nat.zero_le (V T)]
  have hsmall (n : ℕ) (hn : K ≤ n) : |f n| < η / (M + 1) := by
    have h := hK₀ n ((le_max_left K₀ 1).trans hn)
    simpa only [Real.dist_eq, sub_zero] using h
  have hfinal : η / (M + 1) * M < η := by
    calc
      η / (M + 1) * M < η / (M + 1) * (M + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hδ
      _ = η := div_mul_cancel₀ _ (by linarith only [hM])
  rw [Real.dist_eq, sub_zero, abs_mul]
  rcases hlarge with hU | hV
  · exact (mul_le_mul (hsmall _ hU).le (hf _) (abs_nonneg _) hδ.le).trans_lt hfinal
  · rw [mul_comm]
    exact (mul_le_mul (hsmall _ hV).le (hf _) (abs_nonneg _) hδ.le).trans_lt hfinal

/-- The two signed Vaughan tails cancel at every divergent product horizon. -/
theorem tendsto_product_scaled_pmPronicVaughanSmallDensity_tails {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ → ℕ) (hUV : Tendsto (fun T => U T * V T) atTop atTop) :
    Tendsto (fun T =>
      ((U T : ℝ) ^ ε * ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε (U T))) *
      ((V T : ℝ) ^ ε * ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε (V T))))
      atTop (𝓝 0) := by
  exact tendsto_mul_of_product_indices_atTop (by positivity)
    (abs_scaled_pmPronicVaughanSmallDensity_tail_le hε)
    (tendsto_scaled_pmPronicVaughanSmallDensity_tail hε) U V hUV

end GaloisForLFunctions.BezoutValuationIncidence
