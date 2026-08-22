import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarNullTransfer
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Positive local exponential-coordinate measure on finite unitary groups

The self-adjoint unitary exponential is a genuine local homeomorphism onto an
open neighbourhood of the identity in `U(d)`.  Additive Haar measure on the
finite-dimensional real self-adjoint space therefore supplies a finite,
positive local coordinate measure suitable for the finite-unitary Haar-null
transfer theorem.
-/

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric
open scoped Matrix.Norms.L2Operator Real Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The finite-dimensional real vector space of self-adjoint finite complex
matrices carries its Borel measurable structure. -/
noncomputable instance finiteUnitarySelfAdjointMeasurableSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (selfAdjoint (Matrix ι ι ℂ)) :=
  borel _

instance finiteUnitarySelfAdjointBorelSpace
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    BorelSpace (selfAdjoint (Matrix ι ι ℂ)) :=
  ⟨rfl⟩

/-- Finite self-adjoint matrix spaces are finite-dimensional over the reals. -/
noncomputable instance finiteUnitarySelfAdjointFiniteDimensional
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) := by
  change FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ))
  infer_instance

/-- A fixed additive Haar measure on finite self-adjoint matrices. -/
noncomputable def finiteUnitarySelfAdjointHaar
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Measure (selfAdjoint (Matrix ι ι ℂ)) :=
  Measure.addHaarMeasure
    (Classical.choice (show Nonempty
      (PositiveCompacts (selfAdjoint (Matrix ι ι ℂ))) by infer_instance))

/-- The chosen source measure is additive Haar measure. -/
noncomputable instance finiteUnitarySelfAdjointHaarIsAddHaarMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsAddHaarMeasure (finiteUnitarySelfAdjointHaar ι) :=
  Measure.isAddHaarMeasure_addHaarMeasure _

/-- Push additive Haar on a bounded self-adjoint ball through the unitary
exponential. -/
def finiteUnitaryExponentialCoordinateMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    Measure (Matrix.unitaryGroup ι ℂ) :=
  Measure.map selfAdjoint.expUnitary
    ((finiteUnitarySelfAdjointHaar ι).restrict (closedBall 0 r))

/-- The finite unitary exponential is continuous. -/
theorem continuous_finiteUnitary_expUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (selfAdjoint.expUnitary : selfAdjoint (Matrix ι ι ℂ) →
      Matrix.unitaryGroup ι ℂ) :=
  selfAdjoint.continuous_expUnitary

/-- The source ball `ball 0 π` of Mathlib's local logarithm chart contains a
positive-radius closed ball.  Stating the source directly avoids elaborating
the heavy C⋆-algebra instance in a public theorem type. -/
theorem exists_finiteUnitary_expUnitary_closedBall
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ r : ℝ, 0 < r ∧ closedBall 0 r ⊆
      Metric.ball (0 : selfAdjoint (Matrix ι ι ℂ)) Real.pi := by
  exact nhds_basis_closedBall.mem_iff.mp
    (Metric.ball_mem_nhds _ (by positivity))

/-- The exponential coordinate measure has exactly its source ball's mass. -/
theorem finiteUnitaryExponentialCoordinateMeasure_apply_univ
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ) :
    finiteUnitaryExponentialCoordinateMeasure ι r Set.univ =
      finiteUnitarySelfAdjointHaar ι (closedBall 0 r) := by
  unfold finiteUnitaryExponentialCoordinateMeasure
  rw [Measure.map_apply continuous_finiteUnitary_expUnitary.measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (μ := finiteUnitarySelfAdjointHaar ι)
    (closedBall 0 r)

/-- Every positive-radius exponential-coordinate ball has positive mass. -/
theorem finiteUnitaryExponentialCoordinateMeasure_univ_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r) :
    0 < finiteUnitaryExponentialCoordinateMeasure ι r Set.univ := by
  rw [finiteUnitaryExponentialCoordinateMeasure_apply_univ]
  exact Metric.measure_closedBall_pos (finiteUnitarySelfAdjointHaar ι) 0 hr

/-- Exponential coordinate measures on bounded balls are finite. -/
noncomputable instance finiteUnitaryExponentialCoordinateMeasure_isFinite
    (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℝ) :
    IsFiniteMeasure (finiteUnitaryExponentialCoordinateMeasure ι r) where
  measure_univ_lt_top := by
    rw [finiteUnitaryExponentialCoordinateMeasure_apply_univ]
    exact measure_closedBall_lt_top

/-- A measurable set is null for a bounded exponential-coordinate measure if
its source preimage inside the defining ball is additive-Haar-null. -/
theorem finiteUnitaryExponentialCoordinateMeasure_eq_zero_of_preimage_null
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℝ)
    {s : Set (Matrix.unitaryGroup ι ℂ)}
    (hs : MeasurableSet s)
    (hzero : finiteUnitarySelfAdjointHaar ι
      (selfAdjoint.expUnitary ⁻¹' s ∩ closedBall 0 r) = 0) :
    finiteUnitaryExponentialCoordinateMeasure ι r s = 0 := by
  unfold finiteUnitaryExponentialCoordinateMeasure
  rw [Measure.map_apply continuous_finiteUnitary_expUnitary.measurable hs,
    Measure.restrict_apply
      (continuous_finiteUnitary_expUnitary.measurable hs)]
  exact hzero

/-- Concrete `U(d)` form of Haar-null transfer for an exponential-coordinate
measure. -/
theorem finiteUnitaryHaar_eq_zero_of_exponentialCoordinate_translates_null
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℝ} (hr : 0 < r)
    {s : Set (Matrix.unitaryGroup ι ℂ)}
    (hs : MeasurableSet s)
    (htrans : ∀ U : Matrix.unitaryGroup ι ℂ,
      finiteUnitaryExponentialCoordinateMeasure ι r
        ((fun V => U * V) ⁻¹' s) = 0) :
    finiteUnitaryHaar ι s = 0 :=
  finiteUnitaryHaar_eq_zero_of_all_left_translates_null
    (finiteUnitaryExponentialCoordinateMeasure ι r) hs
    (finiteUnitaryExponentialCoordinateMeasure_univ_pos hr) htrans

end

end GaloisForLFunctions.HTGeometry
