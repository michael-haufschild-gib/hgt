import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainPackets

/-!
# Sharp normalized correlation peak of a finite integer train

The maximum grouped coefficient controls the entire correlation error and is
attained at a nonzero packet center whenever the maximum is nonzero.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

namespace IntegerPacketTrain

def peakValues (d : IntegerPacketTrain) : Finset ℝ := by
  classical
  exact insert 0 ((d.lags.erase 0).image (fun k => |d.lagCoefficient k|))

def rawPeak (d : IntegerPacketTrain) : ℝ := by
  classical
  exact d.peakValues.max' ⟨0, by simp [peakValues]⟩

def peak (d : IntegerPacketTrain) : ℝ := d.rawPeak / d.mass

theorem rawPeak_nonneg (d : IntegerPacketTrain) : 0 ≤ d.rawPeak := by
  classical
  exact d.peakValues.le_max' 0 (by simp [peakValues])

theorem peak_nonneg (d : IntegerPacketTrain) : 0 ≤ d.peak :=
  div_nonneg d.rawPeak_nonneg d.mass_pos.le

theorem lagCoefficient_le_rawPeak (d : IntegerPacketTrain) {k : ℤ}
    (hk : k ∈ d.lags) (hk0 : k ≠ 0) : |d.lagCoefficient k| ≤ d.rawPeak := by
  classical
  apply d.peakValues.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨hk0, hk⟩, rfl⟩)

theorem normalized_lagCoefficient_le_peak (d : IntegerPacketTrain) {k : ℤ}
    (hk : k ∈ d.lags) (hk0 : k ≠ 0) : |d.lagCoefficient k| / d.mass ≤ d.peak :=
  div_le_div_of_nonneg_right (d.lagCoefficient_le_rawPeak hk hk0) d.mass_pos.le

theorem peak_attained (d : IntegerPacketTrain) : d.peak = 0 ∨
    ∃ k ∈ d.lags, k ≠ 0 ∧ d.peak = |d.lagCoefficient k| / d.mass := by
  classical
  have hm : d.rawPeak ∈ d.peakValues := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with hz | hm
  · left
    simp only [peak, hz, zero_div]
  · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hm
    obtain ⟨hk0, hk⟩ := Finset.mem_erase.mp hk
    exact Or.inr ⟨k, hk, hk0, by rw [peak, ← he]⟩

theorem normalized_source_at_lag (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D < S) {k : ℤ} (hk : k ∈ d.lags) :
    normalizedSourceCorrelation (d.source f S) ((k : ℝ) * S) = d.lagCoefficient k / d.mass := by
  unfold normalizedSourceCorrelation
  rw [d.autocorr_source_at_lag hf hfc hD hs hS hk, d.autocorr_source_zero hf hfc hD hs hS]
  field_simp [hR.ne', d.mass_pos.ne']

theorem seed_zero_at_nonzero_lag {f : ℝ → ℝ} {D S : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D < S) {k : ℤ} (hk0 : k ≠ 0) :
    normalizedSourceCorrelation f ((k : ℝ) * S) = 0 := by
  have hx : |(k : ℝ) * S - (k : ℝ) * S| ≤ D := by simpa only [sub_self, abs_zero] using hD
  have ho := other_lag_outside hD hS (Ne.symm hk0) hx
  simp only [Int.cast_zero, zero_mul, sub_zero] at ho
  simp only [normalizedSourceCorrelation, hs _ ho, zero_div]

theorem normalized_source_error_at_lag (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D < S) {k : ℤ} (hk : k ∈ d.lags) (hk0 : k ≠ 0) :
    |normalizedSourceCorrelation (d.source f S) ((k : ℝ) * S) -
      normalizedSourceCorrelation f ((k : ℝ) * S)| = |d.lagCoefficient k| / d.mass := by
  rw [d.normalized_source_at_lag hf hfc hR hD hs hS hk,
    seed_zero_at_nonzero_lag hD hs hS hk0, sub_zero, abs_div, abs_of_pos d.mass_pos]

/-- Every signed correlation error is controlled by the same attained coefficient peak. -/
theorem normalized_source_error_le_peak (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D < S) (x : ℝ) :
    |normalizedSourceCorrelation (d.source f S) x - normalizedSourceCorrelation f x| ≤ d.peak := by
  classical
  by_cases hp : ∃ k ∈ d.lags, k ≠ 0 ∧ |x - (k : ℝ) * S| ≤ D
  · obtain ⟨k, hk, hk0, hx⟩ := hp
    have ho := other_lag_outside hD hS (Ne.symm hk0) hx
    simp only [Int.cast_zero, zero_mul, sub_zero] at ho
    have hz : normalizedSourceCorrelation f x = 0 := by
      simp only [normalizedSourceCorrelation, hs x ho, zero_div]
    have he : normalizedSourceCorrelation (d.source f S) x =
        (d.lagCoefficient k / d.mass) * normalizedSourceCorrelation f (x - (k : ℝ) * S) := by
      unfold normalizedSourceCorrelation
      rw [d.autocorr_source_near_lag hf hfc hD hs hS hk hx, d.autocorr_source_zero hf hfc hD hs hS]
      field_simp [hR.ne', d.mass_pos.ne']
    rw [he, hz, sub_zero, abs_mul, abs_div, abs_of_pos d.mass_pos]
    calc
      _ ≤ (|d.lagCoefficient k| / d.mass) * 1 :=
        mul_le_mul_of_nonneg_left (normalizedSourceCorrelation_abs_le_one hf hfc hR _)
          (div_nonneg (abs_nonneg _) d.mass_pos.le)
      _ ≤ d.peak := by simpa only [mul_one] using d.normalized_lagCoefficient_le_peak hk hk0
  · have hz (k : ℤ) (hk : k ∈ d.lags) (hk0 : k ≠ 0) : autocorr f (x - (k : ℝ) * S) = 0 :=
      hs _ (lt_of_not_ge (fun hx => hp ⟨k, hk, hk0, hx⟩))
    have he : autocorr (d.source f S) x = d.mass * autocorr f x := by
      rw [d.autocorr_source_grouped hf hfc, Finset.sum_eq_single 0]
      · simp only [d.lagCoefficient_zero, Int.cast_zero, zero_mul, sub_zero]
      · intro k hk hk0
        rw [hz k hk hk0, mul_zero]
      · exact fun h => (h d.zero_mem_lags).elim
    have hn : normalizedSourceCorrelation (d.source f S) x = normalizedSourceCorrelation f x := by
      unfold normalizedSourceCorrelation
      rw [he, d.autocorr_source_zero hf hfc hD hs hS]
      field_simp [hR.ne', d.mass_pos.ne']
    rw [hn, sub_self, abs_zero]
    exact d.peak_nonneg

theorem nonzero_lag_outside_half {D S x : ℝ} (hD : 0 ≤ D) (hS : 2 * D < S)
    {k : ℤ} (hk : k ≠ 0) (hx : |x| ≤ S / 2) : D < |x - (k : ℝ) * S| := by
  have hS0 : 0 < S := by linarith only [hD, hS]
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hb : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have hm := mul_le_mul_of_nonneg_right hb hS0.le
    exact lt_of_lt_of_le (by nlinarith only [hxlo, hm, hS] : D < x - (k : ℝ) * S)
      (le_abs_self _)
  · have hb : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hb hS0.le
    exact lt_of_lt_of_le (by nlinarith only [hxhi, hm, hS] : D < -(x - (k : ℝ) * S))
      (neg_le_abs _)

theorem autocorr_source_local_half (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {D S x : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D < S)
    (hx : |x| ≤ S / 2) : autocorr (d.source f S) x = d.mass * autocorr f x := by
  classical
  rw [d.autocorr_source_grouped hf hfc, Finset.sum_eq_single 0]
  · simp only [d.lagCoefficient_zero, Int.cast_zero, zero_mul, sub_zero]
  · intro k _ hk
    rw [hs _ (nonzero_lag_outside_half hD hS hk hx), mul_zero]
  · exact fun h => (h d.zero_mem_lags).elim

theorem normalized_source_local_half (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S x : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D < S) (hx : |x| ≤ S / 2) :
    normalizedSourceCorrelation (d.source f S) x = normalizedSourceCorrelation f x := by
  unfold normalizedSourceCorrelation
  rw [d.autocorr_source_local_half hf hfc hD hs hS hx, d.autocorr_source_zero hf hfc hD hs hS]
  field_simp [hR.ne', d.mass_pos.ne']

end IntegerPacketTrain
end
end GaloisForLFunctions.BiScaleUncertainty
