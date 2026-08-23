import GaloisForLFunctions.HTGeometry.CirclePoissonHellinger
import Mathlib.MeasureTheory.Integral.Pi

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Product of the real Poisson densities in finitely many circle coordinates. -/
def finiteCirclePoissonDensity (a : ι → CirclePoissonParameter) (z : ι → Circle) : ℝ :=
  ∏ i, poissonKernel 0 (a i : ℂ) (z i : ℂ)

theorem finiteCirclePoissonDensity_nonneg (a : ι → CirclePoissonParameter) (z : ι → Circle) :
    0 ≤ finiteCirclePoissonDensity a z :=
  Finset.prod_nonneg fun i _ => circlePoissonDensity_nonneg (a i) (z i)

theorem continuous_finiteCirclePoissonDensity (a : ι → CirclePoissonParameter) :
    Continuous (finiteCirclePoissonDensity a) := by
  unfold finiteCirclePoissonDensity
  exact continuous_finsetProd Finset.univ fun i _ =>
    (continuous_circlePoissonDensity_real (a i)).comp (continuous_apply i)

theorem integrable_finiteCirclePoissonDensity (a : ι → CirclePoissonParameter) :
    Integrable (finiteCirclePoissonDensity a)
      (Measure.pi fun _ : ι => circleLebesgue) :=
  (continuous_finiteCirclePoissonDensity a).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A finite product of circle Poisson laws is the product Haar law weighted by the product
density. -/
theorem measure_pi_circlePoissonMeasure_eq_withDensity
    (a : ι → CirclePoissonParameter) :
    Measure.pi (fun i => circlePoissonMeasure (a i)) =
      (Measure.pi fun _ : ι => circleLebesgue).withDensity
        (fun z => ENNReal.ofReal (finiteCirclePoissonDensity a z)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  have hintegrable : ∀ i : ι,
      Integrable (fun z : Circle => poissonKernel 0 (a i : ℂ) (z : ℂ))
        (circleLebesgue.restrict (s i)) := fun i =>
    ((continuous_circlePoissonDensity_real (a i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).restrict
  have hprodInt : Integrable (finiteCirclePoissonDensity a)
      (Measure.pi fun i => circleLebesgue.restrict (s i)) :=
    Integrable.fintype_prod hintegrable
  have hnonneg : (0 : (ι → Circle) → ℝ)
      ≤ᵐ[Measure.pi fun i => circleLebesgue.restrict (s i)] finiteCirclePoissonDensity a := by
    filter_upwards with z
    exact finiteCirclePoissonDensity_nonneg a z
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    ← ofReal_integral_eq_lintegral_ofReal hprodInt hnonneg]
  rw [show (∫ z, finiteCirclePoissonDensity a z
        ∂(Measure.pi fun i => circleLebesgue.restrict (s i))) =
      ∏ i, ∫ z in s i, poissonKernel 0 (a i : ℂ) (z : ℂ) ∂circleLebesgue from
    integral_fintype_prod_eq_prod
      (fun (i : ι) (z : Circle) => poissonKernel 0 (a i : ℂ) (z : ℂ))]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun z => circlePoissonDensity_nonneg (a i) z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [circlePoissonMeasure, withDensity_apply _ (hs i)]
  change ENNReal.ofReal
      (∫ z in s i, poissonKernel 0 (a i : ℂ) (z : ℂ) ∂circleLebesgue) =
    ∫⁻ z in s i, ENNReal.ofReal (poissonKernel 0 (a i : ℂ) (z : ℂ)) ∂circleLebesgue
  rw [← ofReal_integral_eq_lintegral_ofReal (hintegrable i)
    (Filter.Eventually.of_forall fun z => circlePoissonDensity_nonneg (a i) z)]

/-- Product of the square roots of finitely many circle Poisson densities. -/
def finiteCirclePoissonHalfDensity
    (a : ι → CirclePoissonParameter) (z : ι → Circle) : ℝ :=
  ∏ i, circlePoissonHalfDensity (a i) (z i)

theorem finiteCirclePoissonHalfDensity_nonneg
    (a : ι → CirclePoissonParameter) (z : ι → Circle) :
    0 ≤ finiteCirclePoissonHalfDensity a z :=
  Finset.prod_nonneg fun i _ => circlePoissonHalfDensity_nonneg (a i) (z i)

theorem continuous_finiteCirclePoissonHalfDensity
    (a : ι → CirclePoissonParameter) :
    Continuous (finiteCirclePoissonHalfDensity a) := by
  unfold finiteCirclePoissonHalfDensity
  exact continuous_finsetProd Finset.univ fun i _ =>
    (continuous_circlePoissonHalfDensity (a i)).comp (continuous_apply i)

theorem finiteCirclePoissonHalfDensity_sq
    (a : ι → CirclePoissonParameter) (z : ι → Circle) :
    finiteCirclePoissonHalfDensity a z ^ 2 = finiteCirclePoissonDensity a z := by
  classical
  calc
    finiteCirclePoissonHalfDensity a z ^ 2 =
        ∏ i, circlePoissonHalfDensity (a i) (z i) ^ 2 := by
      simp only [finiteCirclePoissonHalfDensity, pow_two, Finset.prod_mul_distrib]
    _ = finiteCirclePoissonDensity a z := by
      unfold finiteCirclePoissonDensity
      exact Finset.prod_congr rfl fun i _ => circlePoissonHalfDensity_sq (a i) (z i)

/-- Pointwise product of the local Hellinger half-density overlaps. -/
def finiteCirclePoissonOverlapDensity
    (a b : ι → CirclePoissonParameter) (z : ι → Circle) : ℝ :=
  ∏ i, circlePoissonHalfDensity (a i) (z i) * circlePoissonHalfDensity (b i) (z i)

theorem finiteCirclePoissonOverlapDensity_eq_mul
    (a b : ι → CirclePoissonParameter) (z : ι → Circle) :
    finiteCirclePoissonOverlapDensity a b z =
      finiteCirclePoissonHalfDensity a z * finiteCirclePoissonHalfDensity b z := by
  classical
  simp only [finiteCirclePoissonOverlapDensity, finiteCirclePoissonHalfDensity,
    Finset.prod_mul_distrib]

theorem finiteCirclePoissonOverlapDensity_nonneg
    (a b : ι → CirclePoissonParameter) (z : ι → Circle) :
    0 ≤ finiteCirclePoissonOverlapDensity a b z := by
  rw [finiteCirclePoissonOverlapDensity_eq_mul]
  exact mul_nonneg (finiteCirclePoissonHalfDensity_nonneg a z)
    (finiteCirclePoissonHalfDensity_nonneg b z)

theorem continuous_finiteCirclePoissonOverlapDensity
    (a b : ι → CirclePoissonParameter) :
    Continuous (finiteCirclePoissonOverlapDensity a b) := by
  rw [funext fun z => finiteCirclePoissonOverlapDensity_eq_mul a b z]
  exact (continuous_finiteCirclePoissonHalfDensity a).mul
    (continuous_finiteCirclePoissonHalfDensity b)

theorem integrable_finiteCirclePoissonOverlapDensity
    (a b : ι → CirclePoissonParameter) :
    Integrable (finiteCirclePoissonOverlapDensity a b)
      (Measure.pi fun _ : ι => circleLebesgue) :=
  (continuous_finiteCirclePoissonOverlapDensity a b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_finiteCirclePoissonOverlapDensity
    (a b : ι → CirclePoissonParameter) :
    ∫ z, finiteCirclePoissonOverlapDensity a b z
        ∂(Measure.pi fun _ : ι => circleLebesgue) =
      ∏ i, circlePoissonHellingerAffinity (a i) (b i) := by
  unfold finiteCirclePoissonOverlapDensity circlePoissonHellingerAffinity
  exact integral_fintype_prod_eq_prod
    (fun i z => circlePoissonHalfDensity (a i) z * circlePoissonHalfDensity (b i) z)

/-- Neyman--Pearson comparison event for two finite Poisson products. -/
def finiteCirclePoissonDecisionEvent
    (a b : ι → CirclePoissonParameter) : Set (ι → Circle) :=
  {z | finiteCirclePoissonDensity b z ≤ finiteCirclePoissonDensity a z}

theorem measurableSet_finiteCirclePoissonDecisionEvent
    (a b : ι → CirclePoissonParameter) :
    MeasurableSet (finiteCirclePoissonDecisionEvent a b) := by
  exact measurableSet_le (continuous_finiteCirclePoissonDensity b).measurable
    (continuous_finiteCirclePoissonDensity a).measurable

theorem finiteCirclePoissonDensity_le_overlap_of_mem_decision
    (a b : ι → CirclePoissonParameter) {z : ι → Circle}
    (hz : z ∈ finiteCirclePoissonDecisionEvent a b) :
    finiteCirclePoissonDensity b z ≤ finiteCirclePoissonOverlapDensity a b z := by
  have ha0 := finiteCirclePoissonHalfDensity_nonneg a z
  have hb0 := finiteCirclePoissonHalfDensity_nonneg b z
  have hsqa := finiteCirclePoissonHalfDensity_sq a z
  have hsqb := finiteCirclePoissonHalfDensity_sq b z
  have hhalf : finiteCirclePoissonHalfDensity b z ≤ finiteCirclePoissonHalfDensity a z := by
    change finiteCirclePoissonDensity b z ≤ finiteCirclePoissonDensity a z at hz
    rw [← hsqb, ← hsqa] at hz
    nlinarith
  rw [finiteCirclePoissonOverlapDensity_eq_mul, ← hsqb]
  simpa [pow_two] using mul_le_mul_of_nonneg_right hhalf hb0

theorem finiteCirclePoissonDensity_le_overlap_of_mem_decision_compl
    (a b : ι → CirclePoissonParameter) {z : ι → Circle}
    (hz : z ∈ (finiteCirclePoissonDecisionEvent a b)ᶜ) :
    finiteCirclePoissonDensity a z ≤ finiteCirclePoissonOverlapDensity a b z := by
  have ha0 := finiteCirclePoissonHalfDensity_nonneg a z
  have hb0 := finiteCirclePoissonHalfDensity_nonneg b z
  have hsqa := finiteCirclePoissonHalfDensity_sq a z
  have hsqb := finiteCirclePoissonHalfDensity_sq b z
  have hhalf : finiteCirclePoissonHalfDensity a z ≤ finiteCirclePoissonHalfDensity b z := by
    have hlt : finiteCirclePoissonDensity a z < finiteCirclePoissonDensity b z := by
      simpa [finiteCirclePoissonDecisionEvent] using hz
    rw [← hsqa, ← hsqb] at hlt
    nlinarith
  rw [finiteCirclePoissonOverlapDensity_eq_mul, ← hsqa]
  simpa [pow_two] using mul_le_mul_of_nonneg_left hhalf ha0

theorem measure_pi_circlePoissonMeasure_decision_le_overlap
    (a b : ι → CirclePoissonParameter) :
    (Measure.pi fun i => circlePoissonMeasure (b i))
        (finiteCirclePoissonDecisionEvent a b) ≤
      ENNReal.ofReal (∏ i, circlePoissonHellingerAffinity (a i) (b i)) := by
  classical
  let m : Measure (ι → Circle) := Measure.pi fun _ : ι => circleLebesgue
  let E := finiteCirclePoissonDecisionEvent a b
  have hE : MeasurableSet E := measurableSet_finiteCirclePoissonDecisionEvent a b
  have hbint : Integrable (finiteCirclePoissonDensity b) (m.restrict E) :=
    (integrable_finiteCirclePoissonDensity b).restrict
  have hovint : Integrable (finiteCirclePoissonOverlapDensity a b) (m.restrict E) :=
    (integrable_finiteCirclePoissonOverlapDensity a b).restrict
  have hmono : (∫ z in E, finiteCirclePoissonDensity b z ∂m) ≤
      ∫ z in E, finiteCirclePoissonOverlapDensity a b z ∂m := by
    apply integral_mono_ae hbint hovint
    filter_upwards [ae_restrict_mem hE] with z hz
    exact finiteCirclePoissonDensity_le_overlap_of_mem_decision a b hz
  have hrestrict : (∫ z in E, finiteCirclePoissonOverlapDensity a b z ∂m) ≤
      ∫ z, finiteCirclePoissonOverlapDensity a b z ∂m := by
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun z => finiteCirclePoissonOverlapDensity_nonneg a b z)
      (integrable_finiteCirclePoissonOverlapDensity a b)
  rw [measure_pi_circlePoissonMeasure_eq_withDensity b,
    withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal hbint
      (Eventually.of_forall fun z => finiteCirclePoissonDensity_nonneg b z),
    ← integral_finiteCirclePoissonOverlapDensity]
  exact ENNReal.ofReal_le_ofReal (hmono.trans hrestrict)

theorem measure_pi_circlePoissonMeasure_decision_compl_le_overlap
    (a b : ι → CirclePoissonParameter) :
    (Measure.pi fun i => circlePoissonMeasure (a i))
        (finiteCirclePoissonDecisionEvent a b)ᶜ ≤
      ENNReal.ofReal (∏ i, circlePoissonHellingerAffinity (a i) (b i)) := by
  classical
  let m : Measure (ι → Circle) := Measure.pi fun _ : ι => circleLebesgue
  let E := (finiteCirclePoissonDecisionEvent a b)ᶜ
  have hE : MeasurableSet E := (measurableSet_finiteCirclePoissonDecisionEvent a b).compl
  have haint : Integrable (finiteCirclePoissonDensity a) (m.restrict E) :=
    (integrable_finiteCirclePoissonDensity a).restrict
  have hovint : Integrable (finiteCirclePoissonOverlapDensity a b) (m.restrict E) :=
    (integrable_finiteCirclePoissonOverlapDensity a b).restrict
  have hmono : (∫ z in E, finiteCirclePoissonDensity a z ∂m) ≤
      ∫ z in E, finiteCirclePoissonOverlapDensity a b z ∂m := by
    apply integral_mono_ae haint hovint
    filter_upwards [ae_restrict_mem hE] with z hz
    exact finiteCirclePoissonDensity_le_overlap_of_mem_decision_compl a b hz
  have hrestrict : (∫ z in E, finiteCirclePoissonOverlapDensity a b z ∂m) ≤
      ∫ z, finiteCirclePoissonOverlapDensity a b z ∂m := by
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun z => finiteCirclePoissonOverlapDensity_nonneg a b z)
      (integrable_finiteCirclePoissonOverlapDensity a b)
  rw [measure_pi_circlePoissonMeasure_eq_withDensity a,
    withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal haint
      (Eventually.of_forall fun z => finiteCirclePoissonDensity_nonneg a z),
    ← integral_finiteCirclePoissonOverlapDensity]
  exact ENNReal.ofReal_le_ofReal (hmono.trans hrestrict)

end

end GaloisForLFunctions.HTGeometry
