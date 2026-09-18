import GaloisForLFunctions.RHTower.MaassModelHilbertOrbitDerivatives

/-!
# The completed Maass model as a unitary `SL(2,R)` representation

The quotient `L²` action preserves the closed image of the completed complementary-series
model.  This file restricts that literal unitary action to the invariant image and identifies
it isometrically with the completed Maass model.  Thus an exceptional Maass eigenform has a
closed, full-group local Hilbert realization; no global lift or local factorization is asserted.
-/

open MeasureTheory
namespace GaloisForLFunctions.RHTower
open MaassModelQuotientL2

noncomputable section

/-- The completed Maass-model embedding, with codomain restricted to its linear range. -/
def completedModelRangeIsometry
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    ComplementaryHilbert lam →ₗᵢ[ℂ]
      LinearMap.range (completedModelIsometry N lam f).toLinearMap where
  toLinearMap := (completedModelIsometry N lam f).toLinearMap.rangeRestrict
  norm_map' := by
    intro v
    change ‖completedModelIsometry N lam f v‖ = ‖v‖
    exact (completedModelIsometry N lam f).norm_map v

/-- The restricted completed embedding is onto its range. -/
theorem completedModelRangeIsometry_surjective
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    Function.Surjective (completedModelRangeIsometry N lam f) := by
  intro y
  rcases y.property with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  exact hv

/-- Canonical unitary equivalence from the completed complementary model to its quotient-
`L²` image. -/
def completedModelRangeEquiv
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    ComplementaryHilbert lam ≃ₗᵢ[ℂ]
      LinearMap.range (completedModelIsometry N lam f).toLinearMap :=
  LinearIsometryEquiv.ofSurjective (completedModelRangeIsometry N lam f)
    (completedModelRangeIsometry_surjective N lam f)

/-- The ambient quotient unitary, restricted to the completed Maass-model image. -/
def completedModelRangeAction
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) :
    LinearMap.range (completedModelIsometry N lam f).toLinearMap →ₗ[ℂ]
      LinearMap.range (completedModelIsometry N lam f).toLinearMap where
  toFun x := ⟨integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g x.1,
    integralSubgroupUnitary_mapsTo_completedModelIsometry_range_SL2R N lam f g x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g).map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g).map_smul c x.1

/-- Restriction is still unitary for the inherited Hilbert structure. -/
theorem completedModelRangeAction_inner
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R)
    (x y : LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
    inner ℂ (completedModelRangeAction N lam f g x)
      (completedModelRangeAction N lam f g y) = inner ℂ x y := by
  convert integralSubgroupUnitary_inner (CongruenceSubgroup.Gamma (N + 1)) g x.1 y.1 using 1 <;> rfl

/-- The invariant completed Maass-model image carries the restricted full `SL(2,R)` action. -/
def completedModelRangeRepresentation
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    Representation ℂ SL2R
      (LinearMap.range (completedModelIsometry N lam f).toLinearMap) where
  toFun g := completedModelRangeAction N lam f g
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [completedModelRangeAction] using
      integralSubgroupUnitary_one (CongruenceSubgroup.Gamma (N + 1)) x.1
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa [completedModelRangeAction, Module.End.mul_apply] using
      integralSubgroupUnitary_mul (CongruenceSubgroup.Gamma (N + 1)) g h x.1

/-- The restricted action is literal quotient translation after inclusion into quotient `L²`. -/
theorem completedModelRangeRepresentation_coe
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R)
    (x : LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
    ((completedModelRangeRepresentation N lam f g x :
      LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
      Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g x.1 := rfl

/-- The canonical model equivalence intertwines the local action with the original quotient
unitary action. -/
theorem completedModelRangeEquiv_intertwines
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) (v : ComplementaryHilbert lam) :
    ((completedModelRangeRepresentation N lam f g (completedModelRangeEquiv N lam f v) :
      LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
      Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g
        (completedModelIsometry N lam f v) := rfl

/-- Transport the restricted quotient action across the canonical completed-model equivalence. -/
def completedComplementaryModelAction
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) : ComplementaryHilbert lam →ₗ[ℂ] ComplementaryHilbert lam :=
  (completedModelRangeEquiv N lam f).symm.toLinearMap.comp
    ((completedModelRangeAction N lam f g).comp
      (completedModelRangeEquiv N lam f).toLinearMap)

/-- The transported action is conjugate to the literal action on the invariant quotient range. -/
@[simp] theorem completedComplementaryModelAction_conj
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) (v : ComplementaryHilbert lam) :
    completedModelRangeEquiv N lam f (completedComplementaryModelAction N lam f g v) =
      completedModelRangeAction N lam f g (completedModelRangeEquiv N lam f v) := by
  simp [completedComplementaryModelAction]

/-- Full local `SL(2,R)` representation on the completed complementary Maass model. -/
def completedComplementaryModelRepresentation
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1) :
    Representation ℂ SL2R (ComplementaryHilbert lam) where
  toFun g := completedComplementaryModelAction N lam f g
  map_one' := by
    apply LinearMap.ext
    intro v
    apply (completedModelRangeEquiv N lam f).injective
    rw [completedComplementaryModelAction_conj]
    change completedModelRangeRepresentation N lam f 1 (completedModelRangeEquiv N lam f v) =
      completedModelRangeEquiv N lam f v
    simpa only [Module.End.one_apply] using LinearMap.congr_fun
      (completedModelRangeRepresentation N lam f).map_one (completedModelRangeEquiv N lam f v)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply (completedModelRangeEquiv N lam f).injective
    rw [Module.End.mul_apply]
    simp only [completedComplementaryModelAction_conj]
    change completedModelRangeRepresentation N lam f (g * h) (completedModelRangeEquiv N lam f v) =
      completedModelRangeRepresentation N lam f g
        (completedModelRangeRepresentation N lam f h (completedModelRangeEquiv N lam f v))
    exact LinearMap.congr_fun ((completedModelRangeRepresentation N lam f).map_mul g h)
      (completedModelRangeEquiv N lam f v)

/-- The completed complementary model action is unitary for every exceptional parameter. -/
theorem completedComplementaryModelRepresentation_inner
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) (v w : ComplementaryHilbert lam) :
    inner ℂ (completedComplementaryModelRepresentation N lam f g v)
      (completedComplementaryModelRepresentation N lam f g w) = inner ℂ v w := by
  change inner ℂ (completedComplementaryModelAction N lam f g v)
    (completedComplementaryModelAction N lam f g w) = inner ℂ v w
  let e := completedModelRangeEquiv N lam f
  calc
    inner ℂ (completedComplementaryModelAction N lam f g v)
        (completedComplementaryModelAction N lam f g w) =
        inner ℂ (e (completedComplementaryModelAction N lam f g v))
          (e (completedComplementaryModelAction N lam f g w)) :=
      (e.inner_map_map _ _).symm
    _ = inner ℂ (completedModelRangeAction N lam f g (e v))
          (completedModelRangeAction N lam f g (e w)) := by
      rw [completedComplementaryModelAction_conj, completedComplementaryModelAction_conj]
    _ = inner ℂ (e v) (e w) :=
      completedModelRangeAction_inner N lam f g (e v) (e w)
    _ = inner ℂ v w := e.inner_map_map v w

/-- The completed Maass model action intertwines with literal quotient translation. -/
theorem completedComplementaryModelRepresentation_intertwines
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (g : SL2R) (v : ComplementaryHilbert lam) :
    ((completedModelRangeEquiv N lam f
      (completedComplementaryModelRepresentation N lam f g v) :
      LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
      Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g
        (completedModelIsometry N lam f v) := by
  change ((completedModelRangeEquiv N lam f
    (completedComplementaryModelAction N lam f g v) :
    LinearMap.range (completedModelIsometry N lam f).toLinearMap) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) = _
  rw [completedComplementaryModelAction_conj]
  exact completedModelRangeEquiv_intertwines N lam f g v

end

end GaloisForLFunctions.RHTower
