import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridUniformTail
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Actual bounded-energy sources with unrestricted signed grid values

The source domain includes no grid constraints. Its normalized correlations have a
common envelope and a quantitative signed sampling error controlled by Levy energy.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Actual compact C² sources at a normalized energy ceiling, with signed nodes unrestricted. -/
structure LevyEnergySource (K : ℝ) where
  source : C_c(ℝ, ℝ)
  smooth : ContDiff ℝ 2 (source : ℝ → ℝ)
  mass_pos : 0 < autocorr source 0
  energy_le : normalizedArchEnergy source ≤ K

variable {K : ℝ}

def LevyEnergySource.correlation (f : LevyEnergySource K) (x : ℝ) : ℝ :=
  autocorr f.source x / autocorr f.source 0

theorem LevyEnergySource.continuous_correlation (f : LevyEnergySource K) :
    Continuous f.correlation :=
  (continuous_autocorr f.smooth f.source.hasCompactSupport).div_const _

theorem LevyEnergySource.abs_correlation_le_one (f : LevyEnergySource K) (x : ℝ) :
    |f.correlation x| ≤ 1 := by
  rw [correlation, abs_div, abs_of_pos f.mass_pos]
  exact (div_le_one f.mass_pos).mpr
    (abs_autocorr_le_zero f.source.hasCompactSupport f.source.continuous x)

@[simp]
theorem LevyEnergySource.correlation_zero (f : LevyEnergySource K) :
    f.correlation 0 = 1 := div_self f.mass_pos.ne'

@[simp]
theorem LevyEnergySource.correlation_neg (f : LevyEnergySource K) (x : ℝ) :
    f.correlation (-x) = f.correlation x := by
  simp only [correlation, autocorr_neg]

theorem LevyEnergySource.correlation_abs (f : LevyEnergySource K) (x : ℝ) :
    f.correlation |x| = f.correlation x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), correlation_neg]

/-- Each actual source correlation vanishes outside a finite symmetric interval. -/
theorem LevyEnergySource.exists_correlation_zero_radius (f : LevyEnergySource K) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, A ≤ |x| → f.correlation x = 0 := by
  obtain ⟨D, hD, hz⟩ := exists_pos_autocorr_support_radius f.source.hasCompactSupport
  refine ⟨D + 1, by linarith, ?_⟩
  intro x hx
  rw [correlation, hz x (by linarith), zero_div]

def LevyEnergySource.complexCorrelation (f : LevyEnergySource K) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (f.correlation x : ℂ))
    (Complex.continuous_ofReal.comp f.continuous_correlation) 1
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using f.abs_correlation_le_one x)

@[simp]
theorem LevyEnergySource.complexCorrelation_apply (f : LevyEnergySource K) (x : ℝ) :
    f.complexCorrelation x = (f.correlation x : ℂ) := rfl

/-- The actual signed sample is retained in the uniform quadratic sampling estimate. -/
theorem LevyEnergySource.signed_sample_error_sq_le (f : LevyEnergySource K)
    {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-(1 / 2 : ℝ)) * T *
      (f.correlation T - f.correlation (Real.log (logarithmicCeilNode T : ℝ))) ^ 2 ≤ 8 * K := by
  have hb := div_le_div_of_nonneg_right
    (autocorr_logarithmicCeilNode_error_sq_le f.smooth f.source.hasCompactSupport hT)
    (sq_nonneg (autocorr f.source 0))
  calc
    _ = (Real.exp (-(1 / 2 : ℝ)) * T *
        (autocorr f.source T - autocorr f.source (Real.log (logarithmicCeilNode T : ℝ))) ^ 2) /
        autocorr f.source 0 ^ 2 := by unfold correlation; ring
    _ ≤ (8 * autocorr f.source 0 * biScaleLevyEnergy f.source) /
        autocorr f.source 0 ^ 2 := hb
    _ = 8 * normalizedArchEnergy f.source := by
      unfold normalizedArchEnergy
      field_simp [f.mass_pos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left f.energy_le (by norm_num)

/-- One radius controls signed sampling errors for the entire bounded-energy source domain. -/
theorem exists_uniform_signed_sample_radius (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : LevyEnergySource K, ∀ T : ℝ, A ≤ T →
      |f.correlation T - f.correlation (Real.log (logarithmicCeilNode T : ℝ))| < ε := by
  let c : ℝ := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hd : 0 < c * ε ^ 2 := mul_pos hc (sq_pos_of_pos hε)
  let A := 1 + 8 * max K 0 / (c * ε ^ 2)
  have hA : 0 < A := by
    have hn := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (le_max_right K 0)) hd.le
    dsimp [A]
    linarith
  have hAe : A * (c * ε ^ 2) = c * ε ^ 2 + 8 * max K 0 := by
    dsimp [A]
    field_simp
  refine ⟨A, hA, ?_⟩
  intro f T hAT
  have hT : 0 < T := hA.trans_le hAT
  have hb := f.signed_sample_error_sq_le hT.le
  change c * T * (f.correlation T -
    f.correlation (Real.log (logarithmicCeilNode T : ℝ))) ^ 2 ≤ 8 * K at hb
  by_contra hn
  have he := le_of_not_gt hn
  have hs : ε ^ 2 ≤ (f.correlation T -
      f.correlation (Real.log (logarithmicCeilNode T : ℝ))) ^ 2 := by
    nlinarith only [he, sq_abs (f.correlation T -
      f.correlation (Real.log (logarithmicCeilNode T : ℝ))), hε]
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hc.le hT.le)
  have hAT' := mul_le_mul_of_nonneg_right hAT hd.le
  have hK := le_max_left K 0
  nlinarith only [hb, hm, hAT', hAe, hd, hK]

end

end GaloisForLFunctions.BiScaleUncertainty
