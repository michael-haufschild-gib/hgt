import GaloisForLFunctions.BezoutValuationIncidence.LogarithmicCancellationSurvivesTheDampedFloorTransform
import GaloisForLFunctions.BezoutValuationIncidence.UniformTruncatedMobiusReceiversHaveZeroTrivialDensity
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate

/-!
# Uniform logarithmic cancellation for truncated Möbius receivers

Splitting the truncated endpoint at the square root gives one logarithmic
partial-sum bound for all cutoffs. The divisor-square floor transfer preserves
every logarithmic rate after positive damping up to one half.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem sum_moebius_eq_mertens (M : ℕ) :
    (∑ d ∈ Icc 1 M, moebiusReal d) = Sieve.mertensM M := by
  induction M with
  | zero => simp [Sieve.mertensM]
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega), ih, Sieve.mertensM, Sieve.mertensM,
      Finset.sum_range_succ _ (M + 1)]
    rfl

private theorem eventually_log_pow_le_sqrt_for_truncations (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ q ≤ Real.sqrt n := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ q / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_rpow_atTop (q : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ((div_lt_one (Real.sqrt_pos.2 hn0)).mp hn).le

/-- All truncated Möbius partial sums share every logarithmic saving, with one threshold per order. -/
theorem exists_uniform_sum_truncatedMoebius_log_rate (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U : ℕ,
      |∑ d ∈ Icc 1 n, Sieve.truncatedMoebius U d| ≤
        C * (n : ℝ) / Real.log (n : ℝ) ^ q := by
  obtain ⟨B, hB, hM⟩ := Sieve.deningerMertensM_log_pow_rate q
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hM
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtlim : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  refine ⟨1 + 2 ^ q * B, by positivity, ?_⟩
  filter_upwards [hloglim.eventually_ge_atTop 1,
    hsqrtlim.eventually_ge_atTop (N₀ : ℝ), eventually_log_pow_le_sqrt_for_truncations q,
    eventually_ge_atTop 1] with n hlog hstart hhead hn U
  rw [sum_truncatedMoebius_eq_sum_min]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hmle : ((min U n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right U n
  by_cases hlarge : Real.sqrt (n : ℝ) ≤ ((min U n : ℕ) : ℝ)
  · have hm0 : (0 : ℝ) < (min U n : ℕ) := (Real.sqrt_pos.2 hn0).trans_le hlarge
    have hNm : N₀ ≤ min U n := by exact_mod_cast hstart.trans hlarge
    have hlogm : Real.log (n : ℝ) / 2 ≤ Real.log ((min U n : ℕ) : ℝ) := by
      have h := Real.log_le_log (Real.sqrt_pos.2 hn0) hlarge
      rw [Real.sqrt_eq_rpow, Real.log_rpow hn0] at h
      linarith only [h]
    have hden : (Real.log (n : ℝ) / 2) ^ q ≤
        Real.log ((min U n : ℕ) : ℝ) ^ q :=
      pow_le_pow_left₀ (by positivity) hlogm q
    rw [sum_moebius_eq_mertens]
    calc
      _ ≤ B * (min U n : ℕ) / Real.log ((min U n : ℕ) : ℝ) ^ q := hN₀ _ hNm
      _ ≤ B * n / (Real.log (n : ℝ) / 2) ^ q :=
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmle hB) (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
      _ = (2 ^ q * B) * n / Real.log (n : ℝ) ^ q := by
        rw [div_pow]
        field_simp [hl.ne']
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 2 ^ q * B ≤ 1 + 2 ^ q * B)
          (Nat.cast_nonneg n)) (by positivity)
  · have hsum : |∑ d ∈ Icc 1 (min U n), moebiusReal d| ≤ (min U n : ℕ) := by
      calc
        _ ≤ ∑ d ∈ Icc 1 (min U n), |moebiusReal d| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ Icc 1 (min U n), (1 : ℝ) :=
          sum_le_sum fun d _ => abs_moebiusReal_le_one' d
        _ = _ := by simp
    have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ q := by
      apply (le_div_iff₀ (pow_pos hl q)).mpr
      have h := mul_le_mul_of_nonneg_left hhead (Real.sqrt_nonneg (n : ℝ))
      rw [← pow_two, Real.sq_sqrt hn0.le] at h
      exact h
    calc
      _ ≤ ((min U n : ℕ) : ℝ) := hsum
      _ ≤ Real.sqrt n := (lt_of_not_ge hlarge).le
      _ ≤ (n : ℝ) / Real.log (n : ℝ) ^ q := hroot
      _ ≤ _ := div_le_div_of_nonneg_right
        (by have hcoef : 0 ≤ 2 ^ q * B * (n : ℝ) := by positivity
            nlinarith only [hcoef]) (by positivity)

/-- The damped truncated Möbius floor receivers retain every logarithmic prefix saving uniformly. -/
theorem exists_uniform_patternPrefix_truncatedMoebius_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ U : ℕ,
      |patternPrefix ε (Sieve.truncatedMoebius U) n| ≤
        K * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  have hr (U d : ℕ) : |Sieve.truncatedMoebius U d| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
  have hdiv (U d : ℕ) (hd : 1 ≤ d) :
      |Sieve.truncatedMoebius U d| ≤ 1 * (d.divisors.card : ℝ) ^ 2 := by
    have hcard : (1 : ℝ) ≤ d.divisors.card := by
      exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, by omega⟩⟩)
    exact (hr U d).trans (by nlinarith only [hcard])
  simpa only [patternPrefix] using
    exists_uniform_weightCenteredPrefix_dampedSign_log_rate_of_divisor_square
      (s := fun U => Sieve.truncatedMoebius U) hε hε2 (by norm_num : (0 : ℝ) ≤ 1)
      hdiv (fun U => summable_dampedSignWeight_div_of_abs_le_one hε (hr U))
      exists_uniform_sum_truncatedMoebius_log_rate q

end GaloisForLFunctions.BezoutValuationIncidence

