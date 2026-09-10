import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCoreTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFormAdmission
/-! The literal native primitive lies in the original Friedrichs operator domain, with its actual forcing. -/
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.D4BMNativeResponse
open D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The literal native primitive is exactly the covariance of its actual mass-plus-forcing
under the original joint form embedding. -/
theorem nativeJointTimePrimitive_covariance (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    formEmbeddingCovariance jointEmbedding
      ((nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t)+
       (nativeJointEllipticForcing_memLp q s amplitude t).toLp
        (nativeJointEllipticForcing q s amplitude t)) =
      (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t) := by
  let W := (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
    (nativeJointTimePrimitiveField q s amplitude t)
  let G := (nativeJointEllipticForcing_memLp q s amplitude t).toLp
    (nativeJointEllipticForcing q s amplitude t)
  obtain ⟨v,hv⟩ := nativeJointTimePrimitive_form_admission q s amplitude t
  let e : jointDomain := v-jointEmbedding.adjoint (W+G)
  have hc (f : RadialCore) (g : CoreField) :
      inner ℂ (jointGraph f g) (e : JointEnergySpace) = 0 := by
    change inner ℂ (⟨jointGraph f g,jointGraph_mem f g⟩ : jointDomain)
      (v-jointEmbedding.adjoint (W+G)) = 0
    rw [inner_sub_right,← jointCoreDifferential_inner,jointEmbedding.adjoint_inner_right,hv]
    change inner ℂ (jointCoreDifferential f g) W-
      inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector g)) (W+G) = 0
    exact sub_eq_zero.mpr (nativeTimePrimitive_core_transposition q s amplitude t f g)
  let L : JointEnergySpace →L[ℂ] ℂ := innerSL ℂ (e : JointEnergySpace)
  have hs : jointDomain ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨f,g⟩,rfl⟩
      change inner ℂ (e : JointEnergySpace) (jointGraph f g) = 0
      have h := congrArg conj (hc f g)
      simpa only [inner_conj_symm,map_zero] using h
    · exact L.isClosed_ker
  have hz : inner ℂ e e = 0 := hs e.property
  have he : e = 0 := inner_self_eq_zero.mp hz
  have heq : v = jointEmbedding.adjoint (W+G) := sub_eq_zero.mp he
  change jointEmbedding (jointEmbedding.adjoint (W+G)) = W
  rw [← heq]
  exact hv

/-- The actual native primitive belongs to the original unbounded Friedrichs operator
domain, and its operator value is its literal mass-plus-forcing. -/
theorem nativeJointTimePrimitive_operator_action (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    ∃ hmem : (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t) ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨(nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t),hmem⟩ =
      (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t)+
      (nativeJointEllipticForcing_memLp q s amplitude t).toLp
        (nativeJointEllipticForcing q s amplitude t) := by
  let W := (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
    (nativeJointTimePrimitiveField q s amplitude t)
  let G := (nativeJointEllipticForcing_memLp q s amplitude t).toLp
    (nativeJointEllipticForcing q s amplitude t)
  have hc := nativeJointTimePrimitive_covariance q s amplitude t
  change formEmbeddingCovariance jointEmbedding (W+G) = W at hc
  have h := friedrichsFormOperator_apply_covariance jointEmbedding jointEmbedding_injective
    jointEmbedding_dense (W+G)
  have hmem : W ∈ jointEnergyOperator.domain := hc ▸ h.1
  refine ⟨hmem,?_⟩
  have hx : (⟨W,hmem⟩ : jointEnergyOperator.domain) =
      ⟨formEmbeddingCovariance jointEmbedding (W+G),h.1⟩ := Subtype.ext hc.symm
  exact (congrArg jointEnergyOperator hx).trans h.2

/-- The native residual obeys the bounded covariance equation with its original integrated
forcing. This is the exact equation used for causal comparison. -/
theorem nativeJointResidual_covariance_equation (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    formEmbeddingCovariance jointEmbedding (nativeJointResidual q s amplitude t)+
      (1-formEmbeddingCovariance jointEmbedding)
        ((nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
          (nativeJointTimePrimitiveField q s amplitude t)) =
    formEmbeddingCovariance jointEmbedding
      ((nativeJointIntegratedForcing_memLp q s amplitude t).toLp
        (nativeJointIntegratedForcing q s amplitude t)) := by
  have he : (nativeJointEllipticForcing_memLp q s amplitude t).toLp
      (nativeJointEllipticForcing q s amplitude t) =
      (nativeJointIntegratedForcing_memLp q s amplitude t).toLp
        (nativeJointIntegratedForcing q s amplitude t)-nativeJointResidual q s amplitude t := by
    apply Lp.ext
    filter_upwards [(nativeJointEllipticForcing_memLp q s amplitude t).coeFn_toLp,
      Lp.coeFn_sub ((nativeJointIntegratedForcing_memLp q s amplitude t).toLp
        (nativeJointIntegratedForcing q s amplitude t)) (nativeJointResidual q s amplitude t),
      (nativeJointIntegratedForcing_memLp q s amplitude t).coeFn_toLp,
      nativeJointResidual_original_ae q s amplitude t] with p hp hs hF hU
    rw [hp,hs,Pi.sub_apply,hF,hU]
    rfl
  have hc := nativeJointTimePrimitive_covariance q s amplitude t
  rw [he,map_add,map_sub] at hc
  simp only [sub_apply,one_apply_eq_self]
  let B := formEmbeddingCovariance jointEmbedding
  let W := (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
    (nativeJointTimePrimitiveField q s amplitude t)
  let F := (nativeJointIntegratedForcing_memLp q s amplitude t).toLp
    (nativeJointIntegratedForcing q s amplitude t)
  let U := nativeJointResidual q s amplitude t
  change B W+(B F-B U)=W at hc
  change B U+(W-B W)=B F
  calc
    B U+(W-B W) = B U+((B W+(B F-B U))-B W) := congrArg (fun y => B U+(y-B W)) hc.symm
    _ = B F := by abel

end
end RHTower.D4BMNativeResponse
