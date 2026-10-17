import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainPeak
import GaloisForLFunctions.BiScaleUncertainty.LocalCorrelationEnergyStability
import GaloisForLFunctions.BiScaleUncertainty.SignedGridEnergySources
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Count-independent energy convergence of integer trains

Agreement on the growing half-spacing window removes the singular energy core.
One explicit ceiling contains every finite coefficient vector and integer-site set.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem IntegerPacketTrain.energy_error_le_half_tail (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D < S) :
    |normalizedArchEnergy (d.source f S) - normalizedArchEnergy f| ≤
      2 * ∫ x in Ioi (S / 2), archLevySinhWeight x := by
  apply normalizedArchEnergy_abs_sub_le_of_local hf hfc hR (d.contDiff_source hf S)
    (d.hasCompactSupport_source hfc S) (d.autocorr_source_zero_pos hf.continuous hfc hR hD hs hS)
    (by linarith only [hD, hS])
  intro x hx0 hx
  exact d.normalized_source_local_half hf.continuous hfc hR hD hs hS
    (by rwa [abs_of_nonneg hx0])

/-- Escaping spacing controls energy even when counts, sites and coefficients all vary. -/
theorem tendsto_integerTrain_energy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (d : ℕ → IntegerPacketTrain) (S : ℕ → ℝ)
    (hsep : ∀ n, 2 * D < S n) (hS : Tendsto S atTop atTop) :
    Tendsto (fun n => normalizedArchEnergy ((d n).source f (S n))) atTop
      (𝓝 (normalizedArchEnergy f)) := by
  have hh : Tendsto (fun n => S n / 2) atTop atTop := by
    convert Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hS using 1
    funext n
    ring
  have ht : Tendsto (fun n => 2 * ∫ x in Ioi (S n / 2), archLevySinhWeight x) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_integral_Ioi_zero (f := archLevySinhWeight) (μ := volume) hh).const_mul 2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with n hn
  rw [Real.dist_eq]
  exact ((d n).energy_error_le_half_tail hf hfc hR hD hs (hsep n)).trans_lt hn

def integerTrainEnergyCeiling (f : ℝ → ℝ) : ℝ :=
  normalizedArchEnergy f + 2 * ∫ x in Ioi 1, archLevySinhWeight x

theorem archLevy_tail_one_nonneg : 0 ≤ ∫ x in Ioi 1, archLevySinhWeight x := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact (archLevySinhWeight_pos (lt_trans (by norm_num) hx)).le

theorem normalizedArchEnergy_le_integerTrainEnergyCeiling (f : ℝ → ℝ) :
    normalizedArchEnergy f ≤ integerTrainEnergyCeiling f := by
  have hn := archLevy_tail_one_nonneg
  unfold integerTrainEnergyCeiling
  linarith only [hn]

theorem integerTrainEnergyCeiling_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) : 0 ≤ integerTrainEnergyCeiling f :=
  add_nonneg (div_nonneg (biScaleLevyEnergy_nonneg hfc hf) hR.le)
    (mul_nonneg (by norm_num) archLevy_tail_one_nonneg)

theorem IntegerPacketTrain.energy_le_ceiling (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (hS : 2 * D + 2 ≤ S) : normalizedArchEnergy (d.source f S) ≤ integerTrainEnergyCeiling f := by
  have hsep : 2 * D < S := by linarith only [hS]
  have he : |normalizedArchEnergy (d.source f S) - normalizedArchEnergy f| ≤
      2 * ∫ x in Ioi 1, archLevySinhWeight x := by
    apply normalizedArchEnergy_abs_sub_le_of_local hf hfc hR (d.contDiff_source hf S)
      (d.hasCompactSupport_source hfc S) (d.autocorr_source_zero_pos hf.continuous hfc hR hD hs hsep)
      (by norm_num : (0 : ℝ) < 1)
    intro x hx0 hx1
    exact d.normalized_source_local_half hf.continuous hfc hR hD hs hsep
      (by rw [abs_of_nonneg hx0]; linarith only [hx1, hD, hS])
  have hl := le_abs_self (normalizedArchEnergy (d.source f S) - normalizedArchEnergy f)
  unfold integerTrainEnergyCeiling
  linarith only [he, hl]

def levyIntegerTrainSeed (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hR : 0 < autocorr f 0) : LevyEnergySource (integerTrainEnergyCeiling f) where
  source := f
  smooth := hf
  mass_pos := hR
  energy_le := normalizedArchEnergy_le_integerTrainEnergyCeiling f

def levyIntegerTrain (d : IntegerPacketTrain) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hR : 0 < autocorr f 0) {D S : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D + 2 ≤ S) :
    LevyEnergySource (integerTrainEnergyCeiling f) where
  source := ⟨⟨d.source f S, (d.contDiff_source hf S).continuous⟩,
    d.hasCompactSupport_source f.hasCompactSupport S⟩
  smooth := d.contDiff_source hf S
  mass_pos := d.autocorr_source_zero_pos f.continuous f.hasCompactSupport hR hD hs (by linarith only [hS])
  energy_le := d.energy_le_ceiling hf f.hasCompactSupport hR hD hs hS

end
end GaloisForLFunctions.BiScaleUncertainty
