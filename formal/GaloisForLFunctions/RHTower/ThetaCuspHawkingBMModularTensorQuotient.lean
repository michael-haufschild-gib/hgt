import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularTangentAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularBackground
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularMixedTensor

/-! Actual metric and source evaluations descend to the geometric modular tangent-pair quotient. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- Bilinear evaluation of the actual complex metric tensor on two real coordinate tangent vectors. -/
def tensorPair (M : Matrix (Fin 4) (Fin 4) ℂ) (u v : Fin 4 → ℝ) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (u i:ℂ)*M i j*(v j:ℂ)

set_option maxHeartbeats 800000 in
/-- Both actual coordinate differentials give exactly the displayed tensor pullback. -/
theorem tensorPair_pullback (A : SL(2,ℤ)) (z : UpperHalfPlane) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (u v : Fin 4 → ℝ) :
    tensorPair M (modularSpacetimeDifferential A z u) (modularSpacetimeDifferential A z v) =
      tensorPair (modularTensorPullback A z M) u v := by
  simp only [modularSpacetimeDifferential_apply,modularTensorPullback,modularJacobian]
  generalize 1/(denom A z)^2 = c
  simp [tensorPair,Matrix.mul_apply,Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im]
  ring

/-- Tensor covariance makes the actual tangent-pair evaluation invariant under the geometric group action. -/
theorem tensorEvaluation_modular (F : UpperHalfPlane → Matrix (Fin 4) (Fin 4) ℂ)
    (hF : ∀ A : SL(2,ℤ), ∀ z, modularTensorPullback A z (F (A • z)) = F z)
    (A : SL(2,ℤ)) (p : ModularTangentPair) :
    tensorPair (F (A • p).point) (A • p).left (A • p).right =
      tensorPair (F p.point) p.left p.right := by
  change tensorPair (F (A • p.point)) (modularSpacetimeDifferential A p.point p.left)
    (modularSpacetimeDifferential A p.point p.right) = _
  rw [tensorPair_pullback,hF]

/-- Evaluation on the actual quotient of angular points and both transported tangent vectors. -/
def quotientTensorEvaluation (F : UpperHalfPlane → Matrix (Fin 4) (Fin 4) ℂ)
    (hF : ∀ A : SL(2,ℤ), ∀ z, modularTensorPullback A z (F (A • z)) = F z) :
    ModularTangentQuotient → ℂ :=
  Quotient.lift (fun p : ModularTangentPair => tensorPair (F p.point) p.left p.right) (by
    intro p q h
    rcases MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h) with ⟨A,hA⟩
    rw [← hA]
    exact tensorEvaluation_modular F hF A q)

/-- The quotient evaluation recovers the exact original tensor on every lifted tangent pair. -/
theorem quotientTensorEvaluation_mk (F : UpperHalfPlane → Matrix (Fin 4) (Fin 4) ℂ)
    (hF : ∀ A : SL(2,ℤ), ∀ z, modularTensorPullback A z (F (A • z)) = F z)
    (p : ModularTangentPair) :
    quotientTensorEvaluation F hF (Quotient.mk _ p) = tensorPair (F p.point) p.left p.right := rfl

/-- The constructed mixed metric evaluated on the actual modular tangent quotient. -/
def quotientForcedMetric (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t r : ℝ) :
    ModularTangentQuotient → ℂ :=
  quotientTensorEvaluation (fun z => forcedMetricField q branch a (spacetimePoint t r z))
    (fun A z => forcedMetricField_modular q branch a A t r z)

/-- The complete literal source in the same original spacetime chart as the constructed metric. -/
def spacetimeMixedSource (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t r : ℝ)
    (z : UpperHalfPlane) : Matrix (Fin 4) (Fin 4) ℂ :=
  literalMixedSource q branch r
    (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a (spacetimePoint t r z))
    (coordinates z)

/-- The actual spacetime source, with its original envelope, is modular covariant. -/
theorem spacetimeMixedSource_modular (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (t r : ℝ) (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    modularTensorPullback A z (spacetimeMixedSource q branch a t r (A • z)) =
      spacetimeMixedSource q branch a t r z := by
  exact literalMixedSource_modular q branch r _ A z

/-- The complete retained source evaluated on that same actual tangent quotient. -/
def quotientMixedSource (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t r : ℝ) :
    ModularTangentQuotient → ℂ :=
  quotientTensorEvaluation (spacetimeMixedSource q branch a t r)
    (spacetimeMixedSource_modular q branch a t r)

/-- The original BM background evaluated on the same geometric quotient. -/
def quotientBackgroundMetric (r : ℂ) : ModularTangentQuotient → ℂ :=
  quotientTensorEvaluation (fun z => D4BMBackground.metric r z.im)
    (fun A z => backgroundMetric_modular A z r)

/-- The descended metric retains the actual constructed metric on every representative. -/
theorem quotientForcedMetric_mk (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t r : ℝ)
    (p : ModularTangentPair) :
    quotientForcedMetric q branch a t r (Quotient.mk _ p) =
      tensorPair (forcedMetricField q branch a (spacetimePoint t r p.point)) p.left p.right := rfl

/-- The descended source retains its full original amplitude, time and angular dependence. -/
theorem quotientMixedSource_mk (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t r : ℝ)
    (p : ModularTangentPair) :
    quotientMixedSource q branch a t r (Quotient.mk _ p) =
      tensorPair (spacetimeMixedSource q branch a t r p.point) p.left p.right := rfl

/-- The descended background is the original metric on every lifted tangent pair. -/
theorem quotientBackgroundMetric_mk (r : ℂ) (p : ModularTangentPair) :
    quotientBackgroundMetric r (Quotient.mk _ p) =
      tensorPair (D4BMBackground.metric r p.point.im) p.left p.right := rfl

end
end RHTower.D4BMModularCore
