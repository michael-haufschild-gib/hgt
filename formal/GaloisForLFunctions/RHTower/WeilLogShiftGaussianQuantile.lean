import GaloisForLFunctions.HTGeometry.QuadraticTransportCost
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Gaussian quantile convergence and the exact zero-variance coupling cost. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry Filter Set
open scoped Topology

noncomputable section
namespace RHTower

theorem finiteWeil_gaussian_cdf_strictMono (v : NNReal) (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal 0 v)) := by
  intro x y hxy
  have hpos : 0 < gaussianReal 0 v (Ioc x y) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hvol : (volume : Measure ℝ) (Ioc x y) = 0 :=
      gaussianReal_absolutelyContinuous' 0 hv hz
    have hvolpos : 0 < (volume : Measure ℝ) (Ioc x y) := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)
    exact hvolpos.ne' hvol
  rw [← measure_cdf (gaussianReal 0 v), StieltjesFunction.measure_Ioc] at hpos
  exact sub_pos.mp (ENNReal.ofReal_pos.mp hpos)

theorem finiteWeil_gaussian_cdf_tendsto (μ : ℕ → ProbabilityMeasure ℝ)
    (v : NNReal) (hv : v ≠ 0)
    (hweak : Tendsto μ atTop (𝓝 (⟨gaussianReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ))) (x : ℝ) :
    Tendsto (fun r => cdf (μ r : Measure ℝ) x) atTop (𝓝 (cdf (gaussianReal 0 v) x)) := by
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := Iic x) (by
      rw [frontier_Iic]
      exact gaussianReal_absolutelyContinuous 0 hv (measure_singleton x))
  have h := (ENNReal.tendsto_toReal (measure_ne_top (gaussianReal 0 v) (Iic x))).comp hport
  have hcdf : cdf (gaussianReal 0 v) x = ((gaussianReal 0 v) (Iic x)).toReal := by
    rw [cdf_eq_real, Measure.real]
  rw [hcdf]
  refine h.congr fun r => ?_
  simp [cdf_eq_real, Measure.real]

theorem finiteWeil_gaussian_quantile_tendsto (μ : ℕ → ProbabilityMeasure ℝ)
    (v : NNReal) (hv : v ≠ 0)
    (hweak : Tendsto μ atTop (𝓝 (⟨gaussianReal 0 v, inferInstance⟩ : ProbabilityMeasure ℝ)))
    (p : {p : ℝ // p ∈ Ioo (0 : ℝ) 1}) :
    Tendsto (fun r => quantile (μ r : Measure ℝ) p.val) atTop (𝓝 (quantile (gaussianReal 0 v) p.val)) := by
  apply tendsto_quantile_of_tendsto_cdf (fun r => (μ r : Measure ℝ)) (gaussianReal 0 v)
    (finiteWeil_gaussian_cdf_tendsto μ v hv hweak) p.property.1 p.property.2
  · intro ε hε
    by_contra h
    have hq := (quantile_le_iff (μ := gaussianReal 0 v) p.property.1 p.property.2).mpr (le_of_not_gt h)
    linarith only [hq, hε]
  · intro ε hε
    exact (le_cdf_quantile p.property.1 p.property.2).trans_lt
      (finiteWeil_gaussian_cdf_strictMono v hv (by linarith))

theorem finiteWeil_quantile_dirac_zero (p : {p : ℝ // p ∈ Ioo (0 : ℝ) 1}) :
    quantile (Measure.dirac (0 : ℝ)) p.val = 0 := by
  apply le_antisymm
  · apply (quantile_le_iff p.property.1 p.property.2).mpr
    simpa [cdf_eq_real, Measure.real] using p.property.2.le
  · by_contra h
    have hneg : quantile (Measure.dirac (0 : ℝ)) p.val < 0 := lt_of_not_ge h
    have hle := le_cdf_quantile (μ := Measure.dirac (0 : ℝ)) p.property.1 p.property.2
    have hz : cdf (Measure.dirac (0 : ℝ)) (quantile (Measure.dirac (0 : ℝ)) p.val) = 0 := by
      simp [cdf_eq_real, Measure.real, not_le.mpr hneg]
    rw [hz] at hle
    exact (not_le_of_gt p.property.1) hle

theorem finiteWeil_monotoneCoupling_dirac_sq (μ : ProbabilityMeasure ℝ) :
    (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling (μ : Measure ℝ) (Measure.dirac (0 : ℝ)))) =
      ∫ x, x ^ 2 ∂(μ : Measure ℝ) := by
  rw [integral_monotoneCoupling_sq_sub]
  calc
    _ = ∫ p in Ioo (0 : ℝ) 1, quantile (μ : Measure ℝ) p ^ 2 := by
      apply integral_congr_ae
      apply (ae_restrict_iff' measurableSet_Ioo).mpr
      exact Eventually.of_forall fun p hp => by
        dsimp only
        rw [finiteWeil_quantile_dirac_zero ⟨p, hp⟩, sub_zero, sq_abs]
    _ = _ := integral_quantile_sq_eq_second_moment (μ : Measure ℝ)

end RHTower
