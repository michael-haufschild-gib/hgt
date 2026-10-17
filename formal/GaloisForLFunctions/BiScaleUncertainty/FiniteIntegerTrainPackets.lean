import GaloisForLFunctions.BiScaleUncertainty.DistantCopyCorrelationTopology
import GaloisForLFunctions.BiScaleUncertainty.FiniteTrainActiveLags

/-!
# Actual finite trains on distinct integer sites

Finite coefficient data produce compact sources. Grouping equal differences retains
all signed interference; integer spacing isolates the complete correlation packets.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Concrete finite data, with no analytic interface or correlation constraint. -/
structure IntegerPacketTrain where
  last : ℕ
  coefficient : Fin (last + 1) → ℝ
  site : Fin (last + 1) → ℤ
  site_injective : Function.Injective site
  coefficient_nonzero : ∃ i, coefficient i ≠ 0

namespace IntegerPacketTrain

def mass (d : IntegerPacketTrain) : ℝ := copyTrainMass d.coefficient

theorem mass_pos (d : IntegerPacketTrain) : 0 < d.mass :=
  copyTrainMass_pos_of_exists d.coefficient_nonzero

def lags (d : IntegerPacketTrain) : Finset ℤ :=
  (Finset.univ ×ˢ Finset.univ).image (fun p => d.site p.2 - d.site p.1)

def lagCoefficient (d : IntegerPacketTrain) (k : ℤ) : ℝ :=
  ∑ i, ∑ j, if d.site j - d.site i = k then d.coefficient i * d.coefficient j else 0

def source (d : IntegerPacketTrain) (f : ℝ → ℝ) (S : ℝ) : ℝ → ℝ :=
  finiteTranslateSource f Finset.univ d.coefficient (fun i => (d.site i : ℝ) * S)

def expSymbol (d : IntegerPacketTrain) (S β : ℝ) : ℝ :=
  ∑ i, d.coefficient i * Real.exp (β * ((d.site i : ℝ) * S))

theorem difference_mem_lags (d : IntegerPacketTrain) (i j : Fin (d.last + 1)) :
    d.site j - d.site i ∈ d.lags := by
  apply Finset.mem_image.mpr
  exact ⟨(i, j), by simp, rfl⟩

theorem zero_mem_lags (d : IntegerPacketTrain) : 0 ∈ d.lags := by
  simpa only [sub_self] using d.difference_mem_lags 0 0

theorem lagCoefficient_zero (d : IntegerPacketTrain) : d.lagCoefficient 0 = d.mass := by
  classical
  unfold lagCoefficient mass copyTrainMass
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = d.coefficient i * d.coefficient i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hn : d.site j - d.site i ≠ 0 := by
          intro h
          exact hji (d.site_injective (sub_eq_zero.mp h))
        simp only [if_neg hn]
      · simp
    _ = _ := by ring

theorem lagCoefficient_neg (d : IntegerPacketTrain) (k : ℤ) :
    d.lagCoefficient (-k) = d.lagCoefficient k := by
  classical
  unfold lagCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : d.site i - d.site j = -k ↔ d.site j - d.site i = k := by omega
  simp only [he]
  split_ifs <;> ring

theorem contDiff_source (d : IntegerPacketTrain) {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hf : ContDiff ℝ r f) (S : ℝ) : ContDiff ℝ r (d.source f S) :=
  contDiff_finiteTranslateSource hf _ _ _

theorem hasCompactSupport_source (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (S : ℝ) : HasCompactSupport (d.source f S) :=
  hasCompactSupport_finiteTranslateSource hfc _ _ _

/-- The finite difference set groups all pair interactions, with their signs. -/
theorem autocorr_source_grouped (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (S x : ℝ) :
    autocorr (d.source f S) x =
      ∑ k ∈ d.lags, d.lagCoefficient k * autocorr f (x - (k : ℝ) * S) := by
  classical
  rw [source, autocorr_finiteTranslateSource hf hfc]
  symm
  simp only [lagCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (d.site j - d.site i)]
  · simp only [Int.cast_sub]
    congr 2
    ring
  · intro k _ hk
    rw [if_neg (Ne.symm hk), zero_mul]
  · exact fun h => (h (d.difference_mem_lags i j)).elim

/-- Separated integer centers cannot both lie within the correlation radius. -/
theorem other_lag_outside {D S x : ℝ} (hD : 0 ≤ D) (hS : 2 * D < S)
    {k l : ℤ} (hkl : l ≠ k) (hx : |x - (k : ℝ) * S| ≤ D) :
    D < |x - (l : ℝ) * S| := by
  have hS0 : 0 < S := by linarith only [hD, hS]
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hb : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show l + 1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hb hS0.le
    exact lt_of_lt_of_le (by nlinarith only [hxlo, hm, hS] : D < x - (l : ℝ) * S)
      (le_abs_self _)
  · have hb : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast (show k + 1 ≤ l by omega)
    have hm := mul_le_mul_of_nonneg_right hb hS0.le
    exact lt_of_lt_of_le (by nlinarith only [hxhi, hm, hS] : D < -(x - (l : ℝ) * S))
      (neg_le_abs _)

theorem autocorr_source_near_lag (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {D S x : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D < S)
    {k : ℤ} (hk : k ∈ d.lags) (hx : |x - (k : ℝ) * S| ≤ D) :
    autocorr (d.source f S) x = d.lagCoefficient k * autocorr f (x - (k : ℝ) * S) := by
  classical
  rw [d.autocorr_source_grouped hf hfc]
  apply Finset.sum_eq_single k
  · intro l _ hl
    rw [hs _ (other_lag_outside hD hS hl hx), mul_zero]
  · exact fun h => (h hk).elim

theorem autocorr_source_at_lag (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {D S : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D < S)
    {k : ℤ} (hk : k ∈ d.lags) :
    autocorr (d.source f S) ((k : ℝ) * S) = d.lagCoefficient k * autocorr f 0 := by
  simpa only [sub_self] using d.autocorr_source_near_lag (x := (k : ℝ) * S) hf hfc hD hs hS hk
    (by simpa only [sub_self, abs_zero] using hD)

theorem autocorr_source_zero (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {D S : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D < S) :
    autocorr (d.source f S) 0 = d.mass * autocorr f 0 := by
  simpa only [Int.cast_zero, zero_mul, d.lagCoefficient_zero] using
    d.autocorr_source_at_lag hf hfc hD hs hS d.zero_mem_lags

theorem autocorr_source_zero_pos (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D S : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D < S) :
    0 < autocorr (d.source f S) 0 := by
  rw [d.autocorr_source_zero hf hfc hD hs hS]
  exact mul_pos d.mass_pos hR

end IntegerPacketTrain
end
end GaloisForLFunctions.BiScaleUncertainty
