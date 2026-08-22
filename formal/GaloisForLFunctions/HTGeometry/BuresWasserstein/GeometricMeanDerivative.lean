import GaloisForLFunctions.HTGeometry.CFCSqrtDerivative
import GaloisForLFunctions.HTGeometry.BuresWasserstein.OperatorGeometricMean

/-!
# Differentiability of the operator geometric mean in its second argument

`Z ↦ a # Z` is the composition of two conjugations with the continuous functional calculus square
root, so `hasStrictFDerivAt_saSqrt` and the chain rule make it strictly Fréchet differentiable at
every strictly positive `Z`, with derivative

`h ↦ a^{1/2} · Λ_{√c}⁻¹ (a^{-1/2} h a^{-1/2}) · a^{1/2}`,   `c = a^{-1/2} Z a^{-1/2}`,

where `Λ_{√c}⁻¹` is understood in the twisted form `(Λ_{√c} ∘ P + (1 - P))⁻¹` used throughout.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Conjugation `x ↦ b x b` as a bounded real-linear map. -/
noncomputable def conjMap (b : A) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A b).comp ((ContinuousLinearMap.mul ℝ A).flip b)

omit [PartialOrder A] [StarOrderedRing A] in
lemma conjMap_apply (b x : A) : conjMap b x = b * (x * b) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma conjMap_apply' (b x : A) : conjMap b x = b * x * b := by
  rw [conjMap_apply, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma isSelfAdjoint_conjMap {b : A} (hb : IsSelfAdjoint b) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (conjMap b x) := by
  rw [conjMap_apply']
  exact hx.conjugate_self hb

/-- The geometric mean as a map of its second argument, extended to all of `A`. -/
noncomputable def gmMap (a Z : A) : A :=
  conjMap (a ^ (1/2 : ℝ)) (saSqrt (conjMap (a ^ (-(1/2) : ℝ)) Z))

lemma gmMap_eq_gm (a : A) {Z : A} (hZ : IsSelfAdjoint Z) : gmMap a Z = gm a Z := by
  have hc : IsSelfAdjoint (conjMap (a ^ (-(1/2) : ℝ)) Z) :=
    isSelfAdjoint_conjMap (isSelfAdjoint_rpow a _) hZ
  unfold gmMap
  rw [saSqrt_of_isSelfAdjoint hc, conjMap_apply', conjMap_apply', gm_eq_sqrt]

/-- **Strict differentiability of `Z ↦ a # Z`.** -/
theorem hasStrictFDerivAt_gmMap {a Z : A} (hZ : IsStrictlyPositive (conjMap (a ^ (-(1/2) : ℝ)) Z))
    {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) Z))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    HasStrictFDerivAt (gmMap a)
      ((conjMap (a ^ (1/2 : ℝ))).comp
        ((↑u⁻¹ : A →L[ℝ] A).comp (conjMap (a ^ (-(1/2) : ℝ))))) Z := by
  have h1 : HasStrictFDerivAt (fun z : A => conjMap (a ^ (-(1/2) : ℝ)) z)
      (conjMap (a ^ (-(1/2) : ℝ))) Z := (conjMap (a ^ (-(1/2) : ℝ))).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (saSqrt : A → A) (↑u⁻¹ : A →L[ℝ] A)
      (conjMap (a ^ (-(1/2) : ℝ)) Z) := hasStrictFDerivAt_saSqrt hZ hu
  have h3 : HasStrictFDerivAt (fun z : A => conjMap (a ^ (1/2 : ℝ)) z)
      (conjMap (a ^ (1/2 : ℝ))) (saSqrt (conjMap (a ^ (-(1/2) : ℝ)) Z)) :=
    (conjMap (a ^ (1/2 : ℝ))).hasStrictFDerivAt
  have h12 : HasStrictFDerivAt (fun z : A => saSqrt (conjMap (a ^ (-(1/2) : ℝ)) z))
      ((↑u⁻¹ : A →L[ℝ] A).comp (conjMap (a ^ (-(1/2) : ℝ)))) Z := h2.comp Z h1
  exact HasStrictFDerivAt.comp (f := fun z : A => saSqrt (conjMap (a ^ (-(1/2) : ℝ)) z))
    (g := fun z : A => conjMap (a ^ (1/2 : ℝ)) z) Z h3 h12

/-- The conjugation of a strictly positive element by `a^{-1/2}` is strictly positive. -/
lemma isStrictlyPositive_conjMap_rpow {a Z : A} (ha : IsStrictlyPositive a)
    (hZ : IsStrictlyPositive Z) :
    IsStrictlyPositive (conjMap (a ^ (-(1/2) : ℝ)) Z) := by
  rw [conjMap_apply']
  exact IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint Z _
    (ha.rpow a _).isUnit (isSelfAdjoint_rpow a _) hZ

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
