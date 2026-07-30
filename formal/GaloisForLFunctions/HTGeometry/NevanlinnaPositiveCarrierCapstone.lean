import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch
import GaloisForLFunctions.HTGeometry.ProjectiveFiniteConstraintCarrierAperture
import GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual
import Mathlib.Topology.Baire.BaireMeasurable

/-!
# Positive normalized Nevanlinna carrier capstone

This file closes the gap between the residual affine transversality theorem and the actual
probability-carrier chart.  The normalized frozen tangent has zero total mass.  Consequently its
open unit ball, translated by the constant density one, consists of strictly positive probability
densities.  Every residual relation-free locus in the tangent restricts to a dense residual locus
in that positive chart.  Strictly positive reweighting then preserves atomlessness and singularity
of a singular-continuous Nevanlinna carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Filter
open scoped ENNReal OnePoint Topology

noncomputable section

/-- Membership in a normalized frozen tangent forces the perturbation to have total mass zero. -/
theorem normalizedProjectiveNevanlinna_frozenTangent_mass_zero
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im)
    (w : LinearMap.ker
      (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
        a q z n ha hq mu hupper).toLinearMap) :
    linftyIntegralCLM mu w.1 = 0 := by
  have hw := LinearMap.mem_ker.mp w.2
  exact congrArg Prod.fst hw

/-- Every point of the normalized tangent unit ball gives a strictly positive density of total
mass one after translation by the constant density. -/
theorem normalizedProjectiveNevanlinna_frozenTangent_unitBall_is_probabilityDensity
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im)
    (w : LinearMap.ker
      (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
        a q z n ha hq mu hupper).toLinearMap)
    (hw : ‖w‖ < 1) :
    LinftyStrictlyPositive mu (linftyOne mu + w.1) ∧
      ∫ t, (linftyOne mu + w.1) t ∂mu = 1 := by
  constructor
  · exact linftyOne_add_strictlyPositive_of_norm_lt_one mu w.1
      (by simpa using hw)
  · rw [← linftyIntegralCLM_apply, map_add,
      GaloisForLFunctions.HTGeometry.linftyIntegralCLM_linftyOne,
      normalizedProjectiveNevanlinna_frozenTangent_mass_zero
        a q z n ha hq mu hupper w]
    norm_num

/-- A residual locus in the normalized tangent remains dense residual after restriction to the
positive probability chart.  Positivity and normalization hold at every point of the chart, not
merely on its residual subset. -/
theorem normalizedProjectiveNevanlinna_positiveChart_dense_residual
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im)
    (good : Set (LinearMap.ker
      (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
        a q z n ha hq mu hupper).toLinearMap))
    (hgood : good ∈ residual (LinearMap.ker
      (normalizedProjectiveNevanlinnaJetLinftyContinuousControl
        a q z n ha hq mu hupper).toLinearMap)) :
    let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
      a q z n ha hq mu hupper
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let positiveGood : Set positiveChart := Subtype.val ⁻¹' good
    Dense positiveGood ∧ positiveGood ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive mu (linftyOne mu + w.1.1) ∧
          ∫ t, (linftyOne mu + w.1.1) t ∂mu = 1 := by
  dsimp only
  let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
    a q z n ha hq mu hupper
  let S := LinearMap.ker frozen.toLinearMap
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  let positiveChart : Set S := Metric.ball 0 1
  have hpositiveOpen : IsOpen positiveChart := Metric.isOpen_ball
  letI : BaireSpace positiveChart := hpositiveOpen.baireSpace
  have hres : Subtype.val ⁻¹' good ∈ residual positiveChart :=
    (tendsto_residual_of_isOpenMap continuous_subtype_val
      hpositiveOpen.isOpenMap_subtype_val) hgood
  refine ⟨dense_of_mem_residual hres, hres, ?_⟩
  intro w
  have hwball : ‖w.1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using w.property
  exact normalizedProjectiveNevanlinna_frozenTangent_unitBall_is_probabilityDensity
    a q z n ha hq mu hupper w.1 hwball

/-- Membership in a normalized projective Cauchy frozen tangent forces zero total mass. -/
theorem normalizedProjectiveCauchy_frozenTangent_mass_zero
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (x i).im)
    (w : LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        x n mu hupper).toLinearMap) :
    linftyIntegralCLM mu w.1 = 0 := by
  have hw := LinearMap.mem_ker.mp w.2
  exact congrArg Prod.fst hw

/-- The unit ball in a normalized projective Cauchy frozen tangent translates to strictly
positive probability densities. -/
theorem normalizedProjectiveCauchy_frozenTangent_unitBall_is_probabilityDensity
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (x i).im)
    (w : LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        x n mu hupper).toLinearMap)
    (hw : ‖w‖ < 1) :
    LinftyStrictlyPositive mu (linftyOne mu + w.1) ∧
      ∫ t, (linftyOne mu + w.1) t ∂mu = 1 := by
  constructor
  · exact linftyOne_add_strictlyPositive_of_norm_lt_one mu w.1
      (by simpa using hw)
  · rw [← linftyIntegralCLM_apply, map_add,
      GaloisForLFunctions.HTGeometry.linftyIntegralCLM_linftyOne,
      normalizedProjectiveCauchy_frozenTangent_mass_zero x n mu hupper w]
    norm_num

/-- A residual locus in a normalized projective Cauchy frozen tangent remains dense residual in
its positive mass-one chart.  This version has no amplitude or coordinate-derivative hypothesis
at the frozen points. -/
theorem normalizedProjectiveCauchy_positiveChart_dense_residual
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (x i).im)
    (good : Set (LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        x n mu hupper).toLinearMap))
    (hgood : good ∈ residual (LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        x n mu hupper).toLinearMap)) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      x n mu hupper
    let S := LinearMap.ker frozen.toLinearMap
    let positiveChart : Set S := Metric.ball 0 1
    let positiveGood : Set positiveChart := Subtype.val ⁻¹' good
    Dense positiveGood ∧ positiveGood ∈ residual positiveChart ∧
      ∀ w : positiveChart,
        LinftyStrictlyPositive mu (linftyOne mu + w.1.1) ∧
          ∫ t, (linftyOne mu + w.1.1) t ∂mu = 1 := by
  dsimp only
  let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
    x n mu hupper
  let S := LinearMap.ker frozen.toLinearMap
  have hSclosed : IsClosed (S : Set (Lp ℝ (⊤ : ENNReal) mu)) := frozen.isClosed_ker
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : BaireSpace S := by
    set_option synthInstance.maxHeartbeats 100000 in
      infer_instance
  let positiveChart : Set S := Metric.ball 0 1
  have hpositiveOpen : IsOpen positiveChart := Metric.isOpen_ball
  letI : BaireSpace positiveChart := hpositiveOpen.baireSpace
  have hres : Subtype.val ⁻¹' good ∈ residual positiveChart :=
    (tendsto_residual_of_isOpenMap continuous_subtype_val
      hpositiveOpen.isOpenMap_subtype_val) hgood
  refine ⟨dense_of_mem_residual hres, hres, ?_⟩
  intro w
  have hwball : ‖w.1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using w.property
  exact normalizedProjectiveCauchy_frozenTangent_unitBall_is_probabilityDensity
    x n mu hupper w.1 hwball

/-- Absolute continuity toward an atomless carrier transfers atomlessness to a positive
reweighting. -/
theorem weightedBoundaryCarrier_noAtoms_of_base
    {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (hbase : NullSingletonClass
      (boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ)))) :
    NullSingletonClass (weightedBoundaryCarrier F eta w) := by
  have hac := (weightedBoundaryCarrier_mutuallyAbsolutelyContinuous F eta hw).1
  constructor
  intro x
  exact hac (hbase.measure_singleton x)

/-- Singularity of a carrier is invariant under strictly positive reweighting of its projective
parameter law. -/
theorem weightedBoundaryCarrier_mutuallySingular_of_base
    {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (hbase : boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ)) ⟂ₘ
      (volume : Measure ℝ)) :
    weightedBoundaryCarrier F eta w ⟂ₘ (volume : Measure ℝ) := by
  exact hbase.mono_ac
    (weightedBoundaryCarrier_mutuallyAbsolutelyContinuous F eta hw).1
    Measure.AbsolutelyContinuous.rfl

/-- A positive normalized reweighting of a singular-continuous projective parameter law is an
atomless singular probability carrier with the same Hamburger moments.  Thus the whole positive
chart, including its dense residual relation-free part, remains inside the singular-continuous
Nevanlinna carrier class. -/
theorem weightedBoundaryCarrier_singularContinuous_probability
    {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (heta : eta ∈ projectiveSingularContinuousProbabilityLaws)
    (hnull : ∀ E : Set (OnePoint ℝ), MeasurableSet E →
      (projectiveLebesgueProbability : Measure (OnePoint ℝ)) E = 0 →
      (volume : Measure ℝ) (F.matrix.projectiveLabel ⁻¹' E) = 0)
    (w : Lp ℝ (⊤ : ENNReal) (eta : Measure (OnePoint ℝ)))
    (hw : LinftyStrictlyPositive (eta : Measure (OnePoint ℝ)) w)
    (hint : ∫ t, w t ∂(eta : Measure (OnePoint ℝ)) = 1) :
    IsProbabilityMeasure (weightedBoundaryCarrier F (eta : Measure (OnePoint ℝ)) w) ∧
      NullSingletonClass (weightedBoundaryCarrier F (eta : Measure (OnePoint ℝ)) w) ∧
      weightedBoundaryCarrier F (eta : Measure (OnePoint ℝ)) w ⟂ₘ
        (volume : Measure ℝ) ∧
      HasHamburgerMoments s
        (weightedBoundaryCarrier F (eta : Measure (OnePoint ℝ)) w) := by
  letI : IsProbabilityMeasure (eta : Measure (OnePoint ℝ)) := eta.prop
  letI : NullSingletonClass (eta : Measure (OnePoint ℝ)) := heta.1
  letI : IsProbabilityMeasure
      (linftyDensityMeasure (eta : Measure (OnePoint ℝ)) w) :=
    linftyDensityMeasure_isProbabilityMeasure
      (eta : Measure (OnePoint ℝ)) w hw hint
  have hprob : IsProbabilityMeasure
      (weightedBoundaryCarrier F (eta : Measure (OnePoint ℝ)) w) := by
    dsimp only [weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure
      (linftyDensityMeasure (eta : Measure (OnePoint ℝ)) w)
      (fun t => (F.leaf t : Measure ℝ)) F.measurable_leaf
      (fun t => (F.leaf t).prop)
  have hbaseAtoms : NullSingletonClass
      (boundaryBarycenter (eta : Measure (OnePoint ℝ))
        (fun t => (F.leaf t : Measure ℝ))) := by
    simpa [NevanlinnaBoundaryFamily.barycenter, probabilityBoundaryBarycenter] using
      (F.barycenter_noAtoms eta)
  have hbaseSingular :
      boundaryBarycenter (eta : Measure (OnePoint ℝ))
          (fun t => (F.leaf t : Measure ℝ)) ⟂ₘ (volume : Measure ℝ) := by
    exact boundaryBarycenter_mutuallySingular
      (eta : Measure (OnePoint ℝ))
      (projectiveLebesgueProbability : Measure (OnePoint ℝ))
      (volume : Measure ℝ) (fun t => (F.leaf t : Measure ℝ))
      F.matrix.projectiveLabel F.measurable_leaf
      (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
      F.map_projectiveLabel_leaf heta.2 hnull
  exact ⟨hprob,
    weightedBoundaryCarrier_noAtoms_of_base F (eta : Measure (OnePoint ℝ)) w hw hbaseAtoms,
    weightedBoundaryCarrier_mutuallySingular_of_base
      F (eta : Measure (OnePoint ℝ)) w hw hbaseSingular,
    weightedBoundaryCarrier_hasHamburgerMoments
      F (eta : Measure (OnePoint ℝ)) w hw hint⟩

end

end GaloisForLFunctions.HTGeometry
