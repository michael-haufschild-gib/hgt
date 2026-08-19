/-
# The logarithmic derivative of the arbitrarily indexed genus-one product

For a square-summable family of nonzero points the genus-one canonical product has the
Mittag-Leffler logarithmic derivative

`(log P)' (z) = ∑_i ((z - a i)⁻¹ + (a i)⁻¹)`,

the series converging absolutely because its `i`-th term is `O(‖a i‖⁻²)`.  The two resolvent
factors of a pair of points are absolutely summable for the same reason.
-/
import GaloisForLFunctions.HTGeometry.CanonicalProductE1Divisor
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace

noncomputable section

open Complex Filter Topology Set

namespace RHTower

variable {ι : Type*}

/-- A square-summable family of reciprocals leaves every disc cofinitely. -/
theorem eventually_norm_ge_of_summable_inv_sq {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2)) {S : ℝ} (hS : 0 < S) :
    ∀ᶠ i in cofinite, S ≤ ‖a i‖ := by
  have htend : Tendsto (fun i => 1 / ‖a i‖ ^ 2) cofinite (𝓝 0) := hsum.tendsto_cofinite_zero
  have hlt : ∀ᶠ i in cofinite, 1 / ‖a i‖ ^ 2 < 1 / S ^ 2 :=
    htend.eventually_lt_const (by positivity)
  filter_upwards [hlt] with i hi
  have hpos : 0 < ‖a i‖ := norm_pos_iff.mpr (hane i)
  have hsq : S ^ 2 < ‖a i‖ ^ 2 := lt_of_one_div_lt_one_div (pow_pos hpos 2) hi
  exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)

/-- The Mittag-Leffler terms of the genus-one product are absolutely summable. -/
theorem summable_canonicalProductE1LogDerivTerm {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2)) {z : ℂ} (hz : ∀ i, z ≠ a i) :
    Summable (fun i : ι => (a i - z)⁻¹ - (a i)⁻¹) := by
  have hS : (0 : ℝ) < 2 * ‖z‖ + 1 := by positivity
  have hev := eventually_norm_ge_of_summable_inv_sq hane hsum hS
  refine (hsum.mul_left (2 * ‖z‖)).of_norm_bounded_eventually ?_
  filter_upwards [hev] with i hi
  have hane' : a i ≠ 0 := hane i
  have haz : a i - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz i))
  have hapos : 0 < ‖a i‖ := norm_pos_iff.mpr hane'
  have hdpos : 0 < ‖a i - z‖ := norm_pos_iff.mpr haz
  have hhalf : ‖z‖ ≤ ‖a i‖ / 2 := by linarith
  have hdiff : ‖a i‖ / 2 ≤ ‖a i - z‖ := by
    have hrev := norm_sub_norm_le (a i) z
    linarith
  rw [show (a i - z)⁻¹ - (a i)⁻¹ = z / (a i * (a i - z)) by field_simp; ring]
  rw [norm_div, norm_mul]
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0]
  rw [div_le_iff₀ (mul_pos hapos hdpos)]
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hdiff (norm_nonneg (a i))]

/-- Paired resolvent products are absolutely summable. -/
theorem summable_resolvent_pair {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2)) {z z' : ℂ}
    (hz : ∀ i, z ≠ a i) (hz' : ∀ i, z' ≠ a i) :
    Summable (fun i : ι => (z - a i)⁻¹ * (starRingEnd ℂ) ((z' - a i)⁻¹)) := by
  have hS : (0 : ℝ) < 2 * ‖z‖ + 2 * ‖z'‖ + 1 := by positivity
  have hev := eventually_norm_ge_of_summable_inv_sq hane hsum hS
  refine (hsum.mul_left 4).of_norm_bounded_eventually ?_
  filter_upwards [hev] with i hi
  have hapos : 0 < ‖a i‖ := norm_pos_iff.mpr (hane i)
  have h1 : z - a i ≠ 0 := sub_ne_zero.mpr (hz i)
  have h2 : z' - a i ≠ 0 := sub_ne_zero.mpr (hz' i)
  have hd1 : ‖a i‖ / 2 ≤ ‖z - a i‖ := by
    have hrev := norm_sub_norm_le (a i) z
    have : ‖a i - z‖ = ‖z - a i‖ := norm_sub_rev _ _
    have hzn : ‖z‖ ≤ ‖a i‖ / 2 := by
      have := norm_nonneg z'; linarith
    linarith [this ▸ hrev]
  have hd2 : ‖a i‖ / 2 ≤ ‖z' - a i‖ := by
    have hrev := norm_sub_norm_le (a i) z'
    have : ‖a i - z'‖ = ‖z' - a i‖ := norm_sub_rev _ _
    have hzn : ‖z'‖ ≤ ‖a i‖ / 2 := by
      have := norm_nonneg z; linarith
    linarith [this ▸ hrev]
  have hp1 : 0 < ‖z - a i‖ := norm_pos_iff.mpr h1
  have hp2 : 0 < ‖z' - a i‖ := norm_pos_iff.mpr h2
  rw [norm_mul, RCLike.norm_conj, norm_inv, norm_inv]
  rw [show (4 : ℝ) * (1 / ‖a i‖ ^ 2) = 4 / ‖a i‖ ^ 2 by ring]
  have hprod : (‖a i‖ / 2) * (‖a i‖ / 2) ≤ ‖z - a i‖ * ‖z' - a i‖ := by
    have hnn : (0 : ℝ) ≤ ‖a i‖ / 2 := by positivity
    exact mul_le_mul hd1 hd2 hnn (le_trans hnn hd1)
  rw [← mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hprod]

/-- **The Mittag-Leffler logarithmic derivative.** -/
theorem logDeriv_canonicalProductE1Indexed {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2)) {z : ℂ} (hz : ∀ i, z ≠ a i) :
    logDeriv (canonicalProductE1Indexed a) z = ∑' i : ι, ((z - a i)⁻¹ + (a i)⁻¹) := by
  have hfac : ∀ i, weierstrassE1 (z / a i) ≠ 0 := by
    intro i
    rw [weierstrassE1]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [sub_ne_zero]
    intro h
    exact hz i ((div_eq_one_iff_eq (hane i)).mp h.symm)
  have hsumlog : Summable (fun i : ι => (a i - z)⁻¹ - (a i)⁻¹) :=
    summable_canonicalProductE1LogDerivTerm hane hsum hz
  have hterm : ∀ i : ι, logDeriv (fun w : ℂ => weierstrassE1 (w / a i)) z
      = -((a i - z)⁻¹ - (a i)⁻¹) := by
    intro i
    have hd : a i - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz i))
    have hinv : (a i - z)⁻¹ - (a i)⁻¹ = z / ((a i - z) * a i) := by
      simpa only [sub_sub_cancel] using inv_sub_inv hd (hane i)
    rw [logDeriv_weierstrassE1_div (hane i) (hz i), hinv, mul_comm (a i - z) (a i), ← neg_div]
  have hlogs : Summable (fun i : ι => logDeriv (fun w : ℂ => weierstrassE1 (w / a i)) z) :=
    hsumlog.neg.congr (fun i => (hterm i).symm)
  have hprod : canonicalProductE1Indexed a z ≠ 0 :=
    canonicalProductE1Indexed_ne_zero a hane hsum hz
  have hlog := logDeriv_tprod_eq_tsum (ι := ι) isOpen_univ (Set.mem_univ z)
    hfac (by intro i; simp only [weierstrassE1]; fun_prop) hlogs
    (canonicalProductE1Indexed_hasProdLocallyUniformlyOn a hane hsum
      |>.multipliableLocallyUniformlyOn) hprod
  have hlog' : logDeriv (canonicalProductE1Indexed a) z =
      ∑' i : ι, logDeriv (fun w : ℂ => weierstrassE1 (w / a i)) z := hlog
  rw [hlog']
  refine tsum_congr (fun i => ?_)
  rw [hterm i]
  have hd : a i - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz i))
  have hzi : z - a i ≠ 0 := sub_ne_zero.mpr (hz i)
  field_simp
  ring

end RHTower
