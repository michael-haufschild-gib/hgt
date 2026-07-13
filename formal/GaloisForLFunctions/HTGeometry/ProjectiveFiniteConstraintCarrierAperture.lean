import GaloisForLFunctions.HTGeometry.AtomlessProjectivePositiveAperture
import GaloisForLFunctions.HTGeometry.InfiniteSupportPositiveAperture
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryKernel
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory OnePoint
open scoped ENNReal OnePoint
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

noncomputable def linftyL1ConstraintOperator {k : ℕ} (g : Fin k → Lp ℝ 1 μ) :
    (Lp ℝ ⊤ μ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ⊤) (g i)

lemma linftyL1ConstraintOperator_apply {k : ℕ} (g : Fin k → Lp ℝ 1 μ)
    (w : Lp ℝ ⊤ μ) (i : Fin k) :
    linftyL1ConstraintOperator μ g w i =
      ∫ x, (g i x) * w x ∂μ := by
  rw [linftyL1ConstraintOperator, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  rfl

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

noncomputable def linftyDensityMeasure (w : Lp ℝ ⊤ μ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

lemma linftyDensityMeasure_injective_on_strictlyPositive
    {w u : Lp ℝ ⊤ μ} (hw : LinftyStrictlyPositive μ w)
    (hu : LinftyStrictlyPositive μ u)
    (hmeasure : linftyDensityMeasure μ w = linftyDensityMeasure μ u) : w = u := by
  have hwmeas : AEMeasurable (fun x => ENNReal.ofReal (w x)) μ :=
    (Lp.memLp w).1.aemeasurable.ennreal_ofReal
  have humeas : AEMeasurable (fun x => ENNReal.ofReal (u x)) μ :=
    (Lp.memLp u).1.aemeasurable.ennreal_ofReal
  have hENN : (fun x => ENNReal.ofReal (w x)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (u x)) := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hwmeas humeas
    intro s hs _
    have hset := congrArg (fun ν : Measure α => ν s) hmeasure
    simpa only [linftyDensityMeasure, withDensity_apply _ hs] using hset
  apply Lp.ext
  filter_upwards [hw, hu, hENN] with x hwx hux hx
  exact (ENNReal.ofReal_eq_ofReal_iff hwx.le hux.le).mp hx

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory OnePoint
open scoped ENNReal OnePoint
noncomputable section

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]

noncomputable def weightedBoundaryCarrier (w : Lp ℝ ⊤ eta) : Measure ℝ :=
  boundaryBarycenter (linftyDensityMeasure eta w)
    (fun t => (F.leaf t : Measure ℝ))

theorem weightedBoundaryCarrier_injective_on_strictlyPositive
    {w u : Lp ℝ ⊤ eta} (hw : LinftyStrictlyPositive eta w)
    (hu : LinftyStrictlyPositive eta u)
    (hcarrier : weightedBoundaryCarrier F eta w = weightedBoundaryCarrier F eta u) :
    w = u := by
  apply linftyDensityMeasure_injective_on_strictlyPositive eta hw hu
  exact boundaryBarycenter_injective
    (fun t => (F.leaf t : Measure ℝ)) F.matrix.projectiveLabel
    F.measurable_leaf
    (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
    F.map_projectiveLabel_leaf hcarrier

omit [IsFiniteMeasure eta] in
/-- Strictly positive reweighting preserves the measure class of the boundary carrier. -/
theorem weightedBoundaryCarrier_mutuallyAbsolutelyContinuous
    {w : Lp ℝ ⊤ eta} (hw : LinftyStrictlyPositive eta w) :
    weightedBoundaryCarrier F eta w ≪
        boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ)) ∧
      boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ)) ≪
        weightedBoundaryCarrier F eta w := by
  let raw : OnePoint ℝ → ENNReal := fun t => ENNReal.ofReal (w t)
  have hrawmeas : AEMeasurable raw eta :=
    (Lp.memLp w).1.aemeasurable.ennreal_ofReal
  let f : OnePoint ℝ → ENNReal := hrawmeas.mk raw
  have hfmeas : Measurable f := hrawmeas.measurable_mk
  have hfeq : f =ᵐ[eta] raw := hrawmeas.ae_eq_mk.symm
  have hparam : linftyDensityMeasure eta w = eta.withDensity f := by
    exact withDensity_congr_ae hfeq.symm
  have htransport := F.boundaryBarycenter_withDensity_projective eta f hfmeas
  rw [weightedBoundaryCarrier, hparam, htransport]
  constructor
  · exact withDensity_absolutelyContinuous _ _
  · apply withDensity_absolutelyContinuous'
    · exact (hfmeas.comp
        (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable).aemeasurable
    · have hf0 : ∀ᵐ t ∂eta, f t ≠ 0 := by
        filter_upwards [hw, hfeq] with t hwt hft
        rw [hft]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr hwt)
      have hf0meas : MeasurableSet {t | f t ≠ 0} := by
        change MeasurableSet ((f ⁻¹' {(0 : ENNReal)})ᶜ)
        exact (hfmeas (measurableSet_singleton (0 : ENNReal))).compl
      change ∀ᵐ x ∂boundaryBarycenter eta (fun t => (F.leaf t : Measure ℝ)),
        f (F.matrix.projectiveLabel x) ≠ 0
      rw [← ae_map_iff
        ((F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable.aemeasurable)
        hf0meas]
      rw [map_boundaryBarycenter_eq (fun t => (F.leaf t : Measure ℝ))
        F.matrix.projectiveLabel F.measurable_leaf
        (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable
        F.map_projectiveLabel_leaf]
      exact hf0

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def linftyIntegralCLM : (Lp ℝ ⊤ μ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ⊤) (Lp.const 1 μ 1)

theorem linftyIntegralCLM_apply (w : Lp ℝ ⊤ μ) :
    linftyIntegralCLM μ w = ∫ x, w x ∂μ := by
  rw [linftyIntegralCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 1 μ (1 : ℝ)] with x hx
  simp

theorem linftyDensityMeasure_isProbabilityMeasure
    (w : Lp ℝ ⊤ μ) (hw : LinftyStrictlyPositive μ w)
    (hint : ∫ x, w x ∂μ = 1) :
    IsProbabilityMeasure (linftyDensityMeasure μ w) := by
  constructor
  rw [linftyDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hwint : Integrable (⇑w) μ :=
    MemLp.integrable (by simp) (Lp.memLp w)
  have hwnonneg : 0 ≤ᶠ[ae μ] ⇑w := by
    filter_upwards [hw] with x hx
    exact hx.le
  rw [← ofReal_integral_eq_lintegral_ofReal hwint hwnonneg]
  rw [hint]
  norm_num

noncomputable def linftyDensityProbabilityMeasure
    (w : Lp ℝ ⊤ μ) (hw : LinftyStrictlyPositive μ w)
    (hint : ∫ x, w x ∂μ = 1) : ProbabilityMeasure α :=
  ⟨linftyDensityMeasure μ w, linftyDensityMeasure_isProbabilityMeasure μ w hw hint⟩

variable {X : Type*} [TopologicalSpace X]
variable [TopologicalSpace α] [BorelSpace α] [SecondCountableTopologyEither α ℝ]

theorem continuous_linftyDensityProbabilityMeasure
    (w : X → Lp ℝ ⊤ μ) (hwcont : Continuous w)
    (hpos : ∀ x, LinftyStrictlyPositive μ (w x))
    (hint : ∀ x, ∫ y, w x y ∂μ = 1) :
    Continuous (fun x => linftyDensityProbabilityMeasure μ (w x) (hpos x) (hint x)) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  let g : Lp ℝ 1 μ := BoundedContinuousFunction.toLp 1 μ ℝ f
  let L : (Lp ℝ ⊤ μ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ⊤) g
  have heq : (fun x => ∫ y, f y ∂(linftyDensityProbabilityMeasure μ
      (w x) (hpos x) (hint x) : Measure α)) = fun x => L (w x) := by
    funext x
    change ∫ y, f y ∂(linftyDensityMeasure μ (w x)) = L (w x)
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun y => ENNReal.ofReal (w x y)) μ :=
      (Lp.memLp (w x)).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
    dsimp only [L]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hpos x, BoundedContinuousFunction.coeFn_toLp 1 μ ℝ f]
      with y hy hgy
    rw [ENNReal.toReal_ofReal hy.le, hgy]
    simp [mul_comm]
  rw [heq]
  exact L.continuous.comp hwcont

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory OnePoint
open scoped ENNReal OnePoint
noncomputable section

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]

theorem weightedBoundaryCarrier_hasHamburgerMoments
    (w : Lp ℝ ⊤ eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ x, w x ∂eta = 1) :
    HasHamburgerMoments s (weightedBoundaryCarrier F eta w) := by
  let rho : ProbabilityMeasure (OnePoint ℝ) :=
    linftyDensityProbabilityMeasure eta w hw hint
  simpa [weightedBoundaryCarrier, NevanlinnaBoundaryFamily.barycenter,
    probabilityBoundaryBarycenter, rho] using F.barycenter_hasHamburgerMoments rho

noncomputable def weightedBoundaryProbabilityCarrier
    (w : Lp ℝ ⊤ eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ x, w x ∂eta = 1) : ProbabilityMeasure ℝ :=
  F.barycenter (linftyDensityProbabilityMeasure eta w hw hint)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem weightedBoundaryProbabilityCarrier_isClosedEmbedding
    (w : X → Lp ℝ ⊤ eta) (hwcont : Continuous w) (hwinj : Function.Injective w)
    (hpos : ∀ x, LinftyStrictlyPositive eta (w x))
    (hint : ∀ x, ∫ y, w x y ∂eta = 1) :
    Topology.IsClosedEmbedding (fun x =>
      weightedBoundaryProbabilityCarrier F eta (w x) (hpos x) (hint x)) := by
  have hcont : Continuous (fun x =>
      weightedBoundaryProbabilityCarrier F eta (w x) (hpos x) (hint x)) :=
    F.barycenter_isClosedEmbedding.continuous.comp
      (continuous_linftyDensityProbabilityMeasure eta w hwcont hpos hint)
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact hcont
  · intro x y hxy
    apply hwinj
    apply linftyDensityMeasure_injective_on_strictlyPositive eta (hpos x) (hpos y)
    exact congrArg ProbabilityMeasure.toMeasure
      (F.barycenter_isClosedEmbedding.injective hxy)
  · exact hcont.isClosedMap

/-- Real normalization followed by an arbitrary finite packet of `L¹` constraints. -/
noncomputable def normalizedLinftyL1ConstraintOperator {k : ℕ}
    (g : Fin k → Lp ℝ 1 eta) : (Lp ℝ ⊤ eta) →L[ℝ] (Fin (k + 1) → ℝ) :=
  linftyL1ConstraintOperator eta (Fin.cases (Lp.const 1 eta 1) g)

theorem normalizedLinftyL1ConstraintOperator_zero {k : ℕ}
    (g : Fin k → Lp ℝ 1 eta) (w : Lp ℝ ⊤ eta) :
    normalizedLinftyL1ConstraintOperator eta g w 0 = linftyIntegralCLM eta w := by
  rfl

theorem linftyIntegralCLM_linftyOne : linftyIntegralCLM eta (linftyOne eta) = 1 := by
  rw [linftyIntegralCLM_apply]
  calc
    ∫ x, ⇑(linftyOne eta) x ∂eta = ∫ _x : OnePoint ℝ, (1 : ℝ) ∂eta := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const ⊤ eta (1 : ℝ)] with x hx
      exact hx
    _ = 1 := by simp

/-- **Carrier-valued positive finite-constraint aperture.** Every finite packet of real `L¹`
constraints on an atomless projective parameter law admits a closed Hilbert cube of positive
normalized densities.  The induced Nevanlinna boundary carriers are pairwise distinct and all
retain the complete Hamburger moment sequence. -/
theorem exists_positiveHilbertCube_weightedBoundaryCarriers
    [NoAtoms eta] {k : ℕ} (g : Fin k → Lp ℝ 1 eta)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ v : ℕ → Lp ℝ ⊤ eta, ∃ ell : ℕ → (Lp ℝ ⊤ eta) →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding
        (affinePositiveHilbertCubeMap (linftyOne eta) delta v) ∧
      (∀ t : SignedHilbertCube,
        normalizedLinftyL1ConstraintOperator eta g
            (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) =
          normalizedLinftyL1ConstraintOperator eta g (linftyOne eta) ∧
        LinftyStrictlyPositive eta
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) ∧
        HasHamburgerMoments s
          (weightedBoundaryCarrier F eta
            (affinePositiveHilbertCubeMap (linftyOne eta) delta v t))) ∧
      ∃ carrier : SignedHilbertCube → ProbabilityMeasure ℝ,
        Topology.IsClosedEmbedding carrier ∧
        ∀ t, (carrier t : Measure ℝ) = weightedBoundaryCarrier F eta
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) := by
  obtain ⟨v, ell, hvnorm, _hvker, hbio, hembed, hfiber⟩ :=
    exists_positive_closedEmbeddedHilbertCube_in_atomlessProjectiveConstraintFiber
      eta (normalizedLinftyL1ConstraintOperator eta g) hdelta0 hdelta1
  have hpos (t : SignedHilbertCube) : LinftyStrictlyPositive eta
      (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) := (hfiber t).2
  have hint (t : SignedHilbertCube) : ∫ x,
      affinePositiveHilbertCubeMap (linftyOne eta) delta v t x ∂eta = 1 := by
    have hzero := congrFun (hfiber t).1 (0 : Fin (k + 1))
    rw [normalizedLinftyL1ConstraintOperator_zero,
      normalizedLinftyL1ConstraintOperator_zero, linftyIntegralCLM_linftyOne] at hzero
    rw [← linftyIntegralCLM_apply]
    exact hzero
  let carrier : SignedHilbertCube → ProbabilityMeasure ℝ := fun t =>
    weightedBoundaryProbabilityCarrier F eta
      (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) (hpos t) (hint t)
  refine ⟨v, ell, hvnorm, hbio, hembed, ?_, carrier, ?_, ?_⟩
  · intro t
    exact ⟨(hfiber t).1, hpos t,
      weightedBoundaryCarrier_hasHamburgerMoments F eta _ (hpos t) (hint t)⟩
  · exact weightedBoundaryProbabilityCarrier_isClosedEmbedding F eta
      (affinePositiveHilbertCubeMap (linftyOne eta) delta v)
      hembed.continuous hembed.injective hpos hint
  · intro t
    rfl

/-- **Infinite-support carrier aperture.** Atomlessness is not needed: infinite topological
support alone forces the same positive carrier-valued Hilbert cube in every finite `L¹`
constraint fiber. -/
theorem exists_positiveHilbertCube_weightedBoundaryCarriers_of_infiniteSupport
    (heta : eta.support.Infinite) {k : ℕ} (g : Fin k → Lp ℝ 1 eta)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ v : ℕ → Lp ℝ ⊤ eta, ∃ ell : ℕ → (Lp ℝ ⊤ eta) →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding
        (affinePositiveHilbertCubeMap (linftyOne eta) delta v) ∧
      (∀ t : SignedHilbertCube,
        normalizedLinftyL1ConstraintOperator eta g
            (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) =
          normalizedLinftyL1ConstraintOperator eta g (linftyOne eta) ∧
        LinftyStrictlyPositive eta
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) ∧
        HasHamburgerMoments s
          (weightedBoundaryCarrier F eta
            (affinePositiveHilbertCubeMap (linftyOne eta) delta v t))) ∧
      ∃ carrier : SignedHilbertCube → ProbabilityMeasure ℝ,
        Topology.IsClosedEmbedding carrier ∧
        ∀ t, (carrier t : Measure ℝ) = weightedBoundaryCarrier F eta
          (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) := by
  letI : SecondCountableTopology (OnePoint ℝ) :=
    (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).secondCountableTopology
  obtain ⟨v, ell, hvnorm, _hvker, hbio, hembed, hfiber⟩ :=
    exists_positive_closedEmbeddedHilbertCube_in_infiniteSupportConstraintFiber
      eta heta Measure.support_mem_ae
        (normalizedLinftyL1ConstraintOperator eta g) hdelta0 hdelta1
  have hpos (t : SignedHilbertCube) : LinftyStrictlyPositive eta
      (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) := (hfiber t).2
  have hint (t : SignedHilbertCube) : ∫ x,
      affinePositiveHilbertCubeMap (linftyOne eta) delta v t x ∂eta = 1 := by
    have hzero := congrFun (hfiber t).1 (0 : Fin (k + 1))
    rw [normalizedLinftyL1ConstraintOperator_zero,
      normalizedLinftyL1ConstraintOperator_zero, linftyIntegralCLM_linftyOne] at hzero
    rw [← linftyIntegralCLM_apply]
    exact hzero
  let carrier : SignedHilbertCube → ProbabilityMeasure ℝ := fun t =>
    weightedBoundaryProbabilityCarrier F eta
      (affinePositiveHilbertCubeMap (linftyOne eta) delta v t) (hpos t) (hint t)
  refine ⟨v, ell, hvnorm, hbio, hembed, ?_, carrier, ?_, ?_⟩
  · intro t
    exact ⟨(hfiber t).1, hpos t,
      weightedBoundaryCarrier_hasHamburgerMoments F eta _ (hpos t) (hint t)⟩
  · exact weightedBoundaryProbabilityCarrier_isClosedEmbedding F eta
      (affinePositiveHilbertCubeMap (linftyOne eta) delta v)
      hembed.continuous hembed.injective hpos hint
  · intro t
    rfl

end
end GaloisForLFunctions.HTGeometry
