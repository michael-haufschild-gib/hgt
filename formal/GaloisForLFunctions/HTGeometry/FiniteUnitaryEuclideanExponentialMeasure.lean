import GaloisForLFunctions.HTGeometry.FiniteUnitaryExponentialCoordinateMeasure
import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryNormalizationAnalytic

/-!
# Euclidean exponential coordinates for finite unitary Haar transfer

Choose a finite real basis of the self-adjoint matrices.  Its continuous
linear coordinate map makes the exponential chart a globally real-analytic
map from a literal finite Euclidean space.  Consequently, analytic null-set
lemmas over finite products of `ℝ` apply directly to the positive local
coordinate measures used in finite-unitary Haar transfer.
-/

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.L2Operator Real Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite real coordinate system for self-adjoint finite complex matrices. -/
def finiteUnitarySelfAdjointCoordinateEquiv
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ))) → ℝ) ≃L[ℝ]
      selfAdjoint (Matrix ι ι ℂ) :=
  (Module.finBasis ℝ (selfAdjoint (Matrix ι ι ℂ))).equivFun.symm
    |>.toContinuousLinearEquiv

/-- Restrict Euclidean volume to a coordinate ball and push it through the
self-adjoint exponential. -/
def finiteUnitaryEuclideanExponentialMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    Measure (Matrix.unitaryGroup ι ℂ) :=
  Measure.map (fun x => selfAdjoint.expUnitary
    (finiteUnitarySelfAdjointCoordinateEquiv ι x))
    (volume.restrict (closedBall 0 r))

/-- The Euclidean exponential coordinate map is continuous. -/
theorem continuous_finiteUnitaryEuclideanExp
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun x : Fin (Module.finrank ℝ
      (selfAdjoint (Matrix ι ι ℂ))) → ℝ => selfAdjoint.expUnitary
        (finiteUnitarySelfAdjointCoordinateEquiv ι x)) :=
  selfAdjoint.continuous_expUnitary.comp
    (finiteUnitarySelfAdjointCoordinateEquiv ι).continuous

/-- A Euclidean coordinate ball maps inside the local logarithm chart's
self-adjoint source ball. -/
theorem exists_finiteUnitaryEuclideanExp_closedBall
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ r : ℝ, 0 < r ∧ closedBall 0 r ⊆
      (finiteUnitarySelfAdjointCoordinateEquiv ι) ⁻¹'
        ball (0 : selfAdjoint (Matrix ι ι ℂ)) Real.pi := by
  let e := finiteUnitarySelfAdjointCoordinateEquiv ι
  have hpre : e ⁻¹' ball (0 : selfAdjoint (Matrix ι ι ℂ)) Real.pi ∈ 𝓝 0 := by
    have hball : ball (0 : selfAdjoint (Matrix ι ι ℂ)) Real.pi ∈ 𝓝 (e 0) := by
      rw [map_zero]
      exact ball_mem_nhds _ (by positivity)
    exact e.continuousAt.preimage_mem_nhds hball
  exact nhds_basis_closedBall.mem_iff.mp hpre

/-- Matrix coefficients of the Euclidean unitary exponential are real
analytic. -/
theorem analyticAt_finiteUnitaryEuclideanExp_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ))) → ℝ) :
    AnalyticAt ℝ (fun y =>
      (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι y) :
        Matrix ι ι ℂ)) x := by
  exact (analyticAt_expUnitary_coe_real
    (finiteUnitarySelfAdjointCoordinateEquiv ι x)).comp
      ((finiteUnitarySelfAdjointCoordinateEquiv ι).analyticAt x)

/-- Matrix coefficients of the normalized Euclidean unitary exponential are
real analytic. -/
theorem analyticAt_finiteUnitaryEuclideanNormalizedExp_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (x : Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ))) → ℝ) :
    AnalyticAt ℝ (fun y =>
      (specialUnitaryNormalize i0
        (selfAdjoint.expUnitary (finiteUnitarySelfAdjointCoordinateEquiv ι y)) :
        Matrix ι ι ℂ)) x := by
  exact (analyticAt_specialUnitaryNormalize_expUnitary_coe i0
    (finiteUnitarySelfAdjointCoordinateEquiv ι x)).comp
      ((finiteUnitarySelfAdjointCoordinateEquiv ι).analyticAt x)

/-- Matrix coefficients of every left-translated normalized Euclidean
exponential chart are real analytic. -/
theorem analyticAt_finiteUnitaryEuclideanNormalizedLeftExp_coe
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (U : Matrix.unitaryGroup ι ℂ)
    (x : Fin (Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ))) → ℝ) :
    AnalyticAt ℝ (fun y =>
      (specialUnitaryNormalize i0
        (U * selfAdjoint.expUnitary
          (finiteUnitarySelfAdjointCoordinateEquiv ι y)) : Matrix ι ι ℂ)) x := by
  exact (analyticAt_specialUnitaryNormalize_mul_expUnitary_coe i0 U
    (finiteUnitarySelfAdjointCoordinateEquiv ι x)).comp
      ((finiteUnitarySelfAdjointCoordinateEquiv ι).analyticAt x)

/-- The Euclidean exponential coordinate measure has exactly its source
ball's mass. -/
theorem finiteUnitaryEuclideanExponentialMeasure_apply_univ
    (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    finiteUnitaryEuclideanExponentialMeasure ι r Set.univ =
      (volume : Measure (Fin (Module.finrank ℝ
        (selfAdjoint (Matrix ι ι ℂ))) → ℝ)) (closedBall 0 r) := by
  unfold finiteUnitaryEuclideanExponentialMeasure
  rw [Measure.map_apply (continuous_finiteUnitaryEuclideanExp (ι := ι)).measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := volume) (closedBall 0 r)

/-- Every positive-radius Euclidean exponential-coordinate ball has positive
mass. -/
theorem finiteUnitaryEuclideanExponentialMeasure_univ_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r) :
    0 < finiteUnitaryEuclideanExponentialMeasure ι r Set.univ := by
  rw [finiteUnitaryEuclideanExponentialMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hr

/-- Bounded Euclidean exponential-coordinate measures are finite. -/
noncomputable instance finiteUnitaryEuclideanExponentialMeasure_isFinite
    (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    IsFiniteMeasure (finiteUnitaryEuclideanExponentialMeasure ι r) where
  measure_univ_lt_top := by
    rw [finiteUnitaryEuclideanExponentialMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- A measurable set is null for a Euclidean exponential-coordinate measure
if its coordinate preimage inside the defining ball is Lebesgue-null. -/
theorem finiteUnitaryEuclideanExponentialMeasure_eq_zero_of_preimage_null
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    {s : Set (Matrix.unitaryGroup ι ℂ)} (hs : MeasurableSet s)
    (hzero : (volume : Measure (Fin (Module.finrank ℝ
      (selfAdjoint (Matrix ι ι ℂ))) → ℝ))
      ((fun x => selfAdjoint.expUnitary
        (finiteUnitarySelfAdjointCoordinateEquiv ι x)) ⁻¹' s ∩ closedBall 0 r) = 0) :
    finiteUnitaryEuclideanExponentialMeasure ι r s = 0 := by
  unfold finiteUnitaryEuclideanExponentialMeasure
  rw [Measure.map_apply (continuous_finiteUnitaryEuclideanExp (ι := ι)).measurable hs,
    Measure.restrict_apply
      ((continuous_finiteUnitaryEuclideanExp (ι := ι)).measurable hs)]
  exact hzero

/-- Concrete `U(d)` Haar-null transfer for Euclidean exponential coordinates. -/
theorem finiteUnitaryHaar_eq_zero_of_euclideanExponential_translates_null
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r)
    {s : Set (Matrix.unitaryGroup ι ℂ)} (hs : MeasurableSet s)
    (htrans : ∀ U : Matrix.unitaryGroup ι ℂ,
      finiteUnitaryEuclideanExponentialMeasure ι r
        ((fun V => U * V) ⁻¹' s) = 0) :
    finiteUnitaryHaar ι s = 0 :=
  finiteUnitaryHaar_eq_zero_of_all_left_translates_null
    (finiteUnitaryEuclideanExponentialMeasure ι r) hs
    (finiteUnitaryEuclideanExponentialMeasure_univ_pos hr) htrans

end

end GaloisForLFunctions.HTGeometry
