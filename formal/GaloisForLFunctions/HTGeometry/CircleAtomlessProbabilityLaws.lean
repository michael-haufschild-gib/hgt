import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Density of atomless probability laws on the circle

Normalized restrictions of Haar measure to shrinking metric balls form an
atomless approximate identity at zero.  Convolution with this family
approximates every probability law by atomless laws.  Combined with the generic
`G_delta` theorem, atomless circle laws therefore form a dense `G_delta`.
-/

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance unitAddCircleHaarNullSingletonClass :
    NullSingletonClass (AddCircle.haarAddCircle : Measure UnitAddCircle) where
  measure_singleton x := by
    have h := AddCircle.volume_closedBall (1 : ℝ) (x := x) 0
    rw [AddCircle.volume_eq_smul_haarAddCircle] at h
    simpa using h

/-- Radius of the `n`-th atomless circle approximate identity. -/
def circleApproximateIdentityRadius (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Haar measure restricted to the shrinking ball at zero. -/
def circleApproximateIdentityFiniteMeasure (n : ℕ) : FiniteMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle.restrict
    (ball 0 (circleApproximateIdentityRadius n)), inferInstance⟩

theorem circleApproximateIdentityFiniteMeasure_ne_zero (n : ℕ) :
    circleApproximateIdentityFiniteMeasure n ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff]
  intro hmass
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hmass
  rw [ENNReal.coe_zero, FiniteMeasure.ennreal_mass] at hcoe
  change (AddCircle.haarAddCircle.restrict
    (ball 0 (circleApproximateIdentityRadius n))) Set.univ = 0 at hcoe
  rw [Measure.restrict_apply_univ] at hcoe
  have hr : 0 < circleApproximateIdentityRadius n := by
    simp only [circleApproximateIdentityRadius]
    positivity
  exact (measure_ball_pos AddCircle.haarAddCircle 0 hr).ne' hcoe

/-- The atomless probability law obtained by normalizing Haar measure on a
shrinking metric ball. -/
def circleApproximateIdentityLaw (n : ℕ) : ProbabilityMeasure UnitAddCircle :=
  (circleApproximateIdentityFiniteMeasure n).normalize

theorem circleApproximateIdentityLaw_ball (n : ℕ) :
    (circleApproximateIdentityLaw n : Measure UnitAddCircle)
      (ball 0 (circleApproximateIdentityRadius n)) = 1 := by
  change ((circleApproximateIdentityFiniteMeasure n).normalize : Measure UnitAddCircle)
    (ball 0 (circleApproximateIdentityRadius n)) = 1
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
    (circleApproximateIdentityFiniteMeasure n)
    (circleApproximateIdentityFiniteMeasure_ne_zero n)]
  rw [Measure.smul_apply]
  change (↑((circleApproximateIdentityFiniteMeasure n).mass⁻¹) : ℝ≥0∞) *
    (circleApproximateIdentityFiniteMeasure n : Measure UnitAddCircle)
      (ball 0 (circleApproximateIdentityRadius n)) = 1
  have hmass : (circleApproximateIdentityFiniteMeasure n).mass ≠ 0 :=
    (FiniteMeasure.mass_nonzero_iff
      (circleApproximateIdentityFiniteMeasure n)).mpr
      (circleApproximateIdentityFiniteMeasure_ne_zero n)
  rw [ENNReal.coe_inv hmass, FiniteMeasure.ennreal_mass]
  change ((AddCircle.haarAddCircle.restrict
      (ball 0 (circleApproximateIdentityRadius n))) Set.univ)⁻¹ *
    (AddCircle.haarAddCircle.restrict
      (ball 0 (circleApproximateIdentityRadius n)))
      (ball 0 (circleApproximateIdentityRadius n)) = 1
  rw [Measure.restrict_apply_univ, Measure.restrict_apply_self]
  apply ENNReal.inv_mul_cancel
  · have hr : 0 < circleApproximateIdentityRadius n := by
      simp only [circleApproximateIdentityRadius]
      positivity
    exact (measure_ball_pos AddCircle.haarAddCircle 0 hr).ne'
  · exact measure_ne_top _ _

theorem circleApproximateIdentityLaw_noAtoms (n : ℕ) :
    NullSingletonClass (circleApproximateIdentityLaw n : Measure UnitAddCircle) := by
  constructor
  intro x
  change ((circleApproximateIdentityFiniteMeasure n).normalize :
    Measure UnitAddCircle) {x} = 0
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
    (circleApproximateIdentityFiniteMeasure n)
    (circleApproximateIdentityFiniteMeasure_ne_zero n)]
  rw [Measure.smul_apply]
  change (↑((circleApproximateIdentityFiniteMeasure n).mass⁻¹) : ℝ≥0∞) *
    (circleApproximateIdentityFiniteMeasure n : Measure UnitAddCircle) {x} = 0
  apply mul_eq_zero_of_right
  change (AddCircle.haarAddCircle.restrict
    (ball 0 (circleApproximateIdentityRadius n))) {x} = 0
  simp

theorem circleApproximateIdentityRadius_tendsto_zero :
    Tendsto circleApproximateIdentityRadius atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem circleApproximateIdentityLaw_tendsto_dirac :
    Tendsto circleApproximateIdentityLaw atTop (𝓝 (diracProba 0)) := by
  apply tendsto_diracProba_of_eventually_measure_nhds_eq_one
  intro U hU
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hev : ∀ᶠ n in atTop, circleApproximateIdentityRadius n < epsilon :=
    circleApproximateIdentityRadius_tendsto_zero.eventually_lt_const hepsilon
  filter_upwards [hev] with n hn
  have hsub : ball 0 (circleApproximateIdentityRadius n) ⊆ U :=
    (ball_subset_ball hn.le).trans hball
  apply le_antisymm
  · have hmono := measure_mono (μ := (circleApproximateIdentityLaw n :
      Measure UnitAddCircle)) (subset_univ U : U ⊆ (Set.univ : Set UnitAddCircle))
    simpa using hmono
  · have hmono := measure_mono (μ := (circleApproximateIdentityLaw n :
      Measure UnitAddCircle)) hsub
    rw [circleApproximateIdentityLaw_ball] at hmono
    exact hmono

/-- Additive convolution of circle probability laws. -/
def circleProbabilityConvolution
    (mu nu : ProbabilityMeasure UnitAddCircle) : ProbabilityMeasure UnitAddCircle :=
  (mu.prod nu).map continuous_add.measurable.aemeasurable

theorem circleProbabilityConvolution_continuous :
    Continuous (fun p : ProbabilityMeasure UnitAddCircle × ProbabilityMeasure UnitAddCircle =>
      circleProbabilityConvolution p.1 p.2) := by
  exact (ProbabilityMeasure.continuous_map continuous_add).comp
    ProbabilityMeasure.continuous_prod

theorem circleProbabilityConvolution_dirac_zero
    (mu : ProbabilityMeasure UnitAddCircle) :
    circleProbabilityConvolution mu (diracProba 0) = mu := by
  apply ProbabilityMeasure.toMeasure_injective
  change (mu : Measure UnitAddCircle) ∗ (Measure.dirac 0) =
    (mu : Measure UnitAddCircle)
  exact Measure.conv_dirac_zero (mu : Measure UnitAddCircle)

theorem circleProbabilityConvolution_noAtoms_right
    (mu nu : ProbabilityMeasure UnitAddCircle)
    (hnu : NullSingletonClass (nu : Measure UnitAddCircle)) :
    NullSingletonClass (circleProbabilityConvolution mu nu : Measure UnitAddCircle) := by
  constructor
  intro z
  change (((mu.prod nu).map continuous_add.measurable.aemeasurable :
    ProbabilityMeasure UnitAddCircle) : Measure UnitAddCircle) {z} = 0
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (f := fun p : UnitAddCircle × UnitAddCircle => p.1 + p.2)
    continuous_add.measurable (measurableSet_singleton z)]
  rw [ProbabilityMeasure.toMeasure_prod]
  have hmeas : MeasurableSet
      ((fun p : UnitAddCircle × UnitAddCircle => p.1 + p.2) ⁻¹' {z}) :=
    continuous_add.measurable (measurableSet_singleton z)
  rw [Measure.prod_apply hmeas]
  have hfiber : ∀ x : UnitAddCircle,
      Prod.mk x ⁻¹' ((fun p : UnitAddCircle × UnitAddCircle => p.1 + p.2) ⁻¹' {z}) =
        {z - x} := by
    intro x
    ext y
    simp [eq_sub_iff_add_eq, add_comm]
  simp_rw [hfiber, hnu.measure_singleton]
  exact lintegral_zero

theorem circleProbabilityConvolution_approximateIdentity_tendsto
    (mu : ProbabilityMeasure UnitAddCircle) :
    Tendsto (fun n => circleProbabilityConvolution mu
      (circleApproximateIdentityLaw n)) atTop (𝓝 mu) := by
  have hpair : Tendsto (fun n => (mu, circleApproximateIdentityLaw n)) atTop
      (𝓝 (mu, diracProba 0)) :=
    tendsto_const_nhds.prodMk_nhds circleApproximateIdentityLaw_tendsto_dirac
  have hmap := Filter.Tendsto.comp circleProbabilityConvolution_continuous.continuousAt hpair
  simpa only [Function.comp_def, circleProbabilityConvolution_dirac_zero] using hmap

/-- Atomless probability laws are dense on the circle. -/
theorem circle_atomlessProbabilityLaws_dense :
    Dense (atomlessProbabilityLaws (X := UnitAddCircle)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro mu
  apply mem_closure_of_tendsto
    (circleProbabilityConvolution_approximateIdentity_tendsto mu)
  filter_upwards with n
  exact circleProbabilityConvolution_noAtoms_right mu
    (circleApproximateIdentityLaw n) (circleApproximateIdentityLaw_noAtoms n)

/-- Atomless probability laws form a dense `G_delta` in the weak topology on
circle probability measures. -/
theorem circle_atomlessProbabilityLaws_dense_gdelta :
    Dense (atomlessProbabilityLaws (X := UnitAddCircle)) ∧
      IsGδ (atomlessProbabilityLaws (X := UnitAddCircle)) :=
  ⟨circle_atomlessProbabilityLaws_dense, atomlessProbabilityLaws_isGdelta⟩

end

end GaloisForLFunctions.HTGeometry
