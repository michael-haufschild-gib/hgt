import GaloisForLFunctions.RHTower.LiEvenCrossEulerMassJetSeries
import GaloisForLFunctions.RHTower.LiEvenCrossEulerSmallMassRemainder

/-!
# The actual LI jet's uniform two-term small-mass profile

The exact fixed-order source expansion is split before any growing-order
estimate. The full remainder bound then applies uniformly to every earlier
order in a logarithmic window.
-/

namespace RHTower

noncomputable section

/-- Exact normalization and two-term decomposition of the actual Euler jet. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_div_two_mul_mass_eq
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) =
      normalizedPrimeArchMoment 0 - (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v +
        liEvenCrossEulerNormalizedMassTail v k := by
  let f : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2) *
    normalizedPrimeArchMoment n * v ^ n
  have hf : Summable f := by
    refine ((summable_liEvenCrossFirstCurrentEvenEulerJet_massSeries hv hvquarter k).mul_right
      (1 / v)).congr fun n => ?_
    dsimp [f]
    rw [pow_succ]
    field_simp
    rw [pow_succ]
    ring
  have hjet : liEvenCrossFirstCurrentEvenEulerJet v k = 2 * v * ∑' n, f n := by
    rw [liEvenCrossFirstCurrentEvenEulerJet_eq_massSeries hv hvquarter, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [f]
    rw [pow_succ]
    ring
  have hnormalized : liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) = ∑' n, f n := by
    rw [hjet]
    field_simp
  have hpow : (2 : ℝ) ^ (2 * k + 2) = (4 : ℝ) ^ (k + 1) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  have hfzero : f 0 = normalizedPrimeArchMoment 0 := by simp [f]
  have hfone : f 1 = -(4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v := by
    simp only [f, Nat.reduceAdd, Nat.cast_ofNat, pow_one]
    rw [hpow]
    ring
  have hhead : ∑ n ∈ Finset.range 2, f n =
      normalizedPrimeArchMoment 0 - (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hfzero, hfone]
    ring
  have htail : (∑' n, f (n + 2)) = liEvenCrossEulerNormalizedMassTail v k := by
    rfl
  rw [hnormalized]
  simpa only [hhead, htail] using (hf.sum_add_tsum_nat_add 2).symm

/-- The literal two-term jet error is exactly the complete source tail. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_two_term_error_eq_tail
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) - normalizedPrimeArchMoment 0 +
        (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v =
      liEvenCrossEulerNormalizedMassTail v k := by
  rw [liEvenCrossFirstCurrentEvenEulerJet_div_two_mul_mass_eq hv hvquarter]
  ring

/-- Explicit source-dependent error bound, uniform over all earlier jet orders. -/
theorem abs_liEvenCrossFirstCurrentEvenEulerJet_two_term_profile_le
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (C : ℝ) (k : ℕ)
    (hk : (k : ℝ) ≤ -Real.log v / Real.log 4 + C)
    (hsmall : (3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent ≤ 1 / 8) :
    |liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) - normalizedPrimeArchMoment 0 +
        (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v| ≤
      18 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ C / 150) ^ 2 *
        v ^ (2 * liEvenCrossEulerSmallMassHalfExponent) := by
  rw [liEvenCrossFirstCurrentEvenEulerJet_two_term_error_eq_tail hv hvquarter]
  exact abs_liEvenCrossEulerNormalizedMassTail_log_window_le hv C k hk hsmall

/-- The actual normalized jet has a uniform two-term profile in every logarithmic window. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_uniform_log_window
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ k : ℕ,
      (k : ℝ) ≤ -Real.log v / Real.log 4 + C →
        |liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) - normalizedPrimeArchMoment 0 +
          (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v| < ε := by
  have hquarter : ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0), v < 1 / 4 :=
    (show ∀ᶠ v : ℝ in nhds 0, v < 1 / 4 from
      Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hquarter,
    liEvenCrossEulerNormalizedMassTail_uniform_log_window C hε] with v hv hvquarter htail
  intro k hk
  rw [liEvenCrossFirstCurrentEvenEulerJet_two_term_error_eq_tail hv hvquarter.le]
  exact htail k hk

end

end RHTower
