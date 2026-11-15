import GaloisForLFunctions.RepresentationLifting.Descent.SemilinearDescent
import GaloisForLFunctions.RepresentationLifting.KTheory.FieldGrothendieckGroup
import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Twisting descent data preserves the field K-zero class

Tensor a representation over the fixed field with the acted-on field, and
let the group act diagonally. This is an actual semilinear representation.
Its invariant vectors are isomorphic over the fixed field to the original
underlying vector space. Thus twisting the descent datum preserves its
dimension and its class in the field's Grothendieck group.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open Module
open scoped TensorProduct
universe u
variable (G L : Type u) [Group G] [Field L]
  [MulSemiringAction G L]
  (W : Type u) [AddCommGroup W] [Module (FixedPoints.subfield G L) W]
  (ρ : Representation (FixedPoints.subfield G L) G W)

/-- The actual diagonal action on the scalar extension of a representation. -/
def galoisTwistedTensorRepresentation :
    Representation (FixedPoints.subfield G L) G (L ⊗[FixedPoints.subfield G L] W) :=
  (Representation.ofDistribMulAction (FixedPoints.subfield G L) G L).tprod ρ

abbrev galoisTwistedTensorAction : DistribMulAction G (L ⊗[FixedPoints.subfield G L] W) :=
  DistribMulAction.compHom _ (galoisTwistedTensorRepresentation G L W ρ)

/-- The diagonal action conjugates the extended scalars. -/
theorem galoisTwistedTensorSemilinear :
    @SMulDistribClass G L (L ⊗[FixedPoints.subfield G L] W)
      _ (galoisTwistedTensorAction G L W ρ).toSMul _ := by
  letI : SMul G (L ⊗[FixedPoints.subfield G L] W) :=
    (galoisTwistedTensorAction G L W ρ).toSMul
  refine ⟨fun g a v => ?_⟩
  change galoisTwistedTensorRepresentation G L W ρ g (a • v) =
    (g • a) • galoisTwistedTensorRepresentation G L W ρ g v
  induction v using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul l w =>
    change TensorProduct.map
      (Representation.ofDistribMulAction (FixedPoints.subfield G L) G L g) (ρ g)
      (a • (l ⊗ₜ w)) =
      (g • a) • TensorProduct.map
        (Representation.ofDistribMulAction (FixedPoints.subfield G L) G L g) (ρ g) (l ⊗ₜ w)
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    change (g • (a * l)) ⊗ₜ (ρ g w) = ((g • a) * (g • l)) ⊗ₜ (ρ g w)
    rw [smul_mul']
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]

variable [Fintype G] [FaithfulSMul G L]
  [FiniteDimensional (FixedPoints.subfield G L) W]

/-- Descending the diagonally twisted scalar extension recovers the original vector-space dimension. -/
def galoisTwistedTensorDescentEquiv :
    (galoisTwistedTensorRepresentation G L W ρ).invariants ≃ₗ[FixedPoints.subfield G L] W := by
  let e₀ := @semilinearFixedCoordinates G L (L ⊗[FixedPoints.subfield G L] W)
    _ _ _ _ _ (galoisTwistedTensorAction G L W ρ)
    (galoisTwistedTensorSemilinear G L W ρ) _ _ _
  -- The tensor's native fixed-field action agrees with restriction of its extended scalars.
  let e₁ : (galoisTwistedTensorRepresentation G L W ρ).invariants ≃ₗ[FixedPoints.subfield G L]
      (Fin (Module.finrank L (L ⊗[FixedPoints.subfield G L] W)) → FixedPoints.subfield G L) :=
    { toFun := fun v => e₀ ⟨v.val, v.property⟩
      invFun := fun f => ⟨(e₀.symm f).val, (e₀.symm f).property⟩
      left_inv := fun v => Subtype.ext
        (congrArg Subtype.val (e₀.symm_apply_apply ⟨v.val, v.property⟩))
      right_inv := e₀.apply_symm_apply
      map_add' := fun v w => e₀.map_add ⟨v.val, v.property⟩ ⟨w.val, w.property⟩
      map_smul' := by
        intro a v
        refine (congrArg e₀ ?_).trans (e₀.map_smul a ⟨v.val, v.property⟩)
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_smul L a v.val).symm }
  have hr : Module.finrank L (L ⊗[FixedPoints.subfield G L] W) =
      Module.finrank (FixedPoints.subfield G L) W :=
    Module.finrank_baseChange (R := L) (S := FixedPoints.subfield G L) (M' := W)
  let b := (Module.finBasis (FixedPoints.subfield G L) W).reindex
    (Equiv.cast (congrArg Fin hr.symm))
  exact e₁.trans b.equivFun.symm

instance galoisTwistedTensorDescentFinite :
    FiniteDimensional (FixedPoints.subfield G L)
      (galoisTwistedTensorRepresentation G L W ρ).invariants :=
  FiniteDimensional.of_injective (galoisTwistedTensorDescentEquiv G L W ρ).toLinearMap
    (galoisTwistedTensorDescentEquiv G L W ρ).injective

/-- Twisting actual descent data acts on field K-zero through the underlying dimension. -/
theorem galoisTwistedTensorDescent_K0_class :
    fieldK0Class (FixedPoints.subfield G L) (FGModuleCat.of (FixedPoints.subfield G L)
      (galoisTwistedTensorRepresentation G L W ρ).invariants) =
    fieldK0Class (FixedPoints.subfield G L) (FGModuleCat.of (FixedPoints.subfield G L) W) := by
  apply (fieldK0EquivInt (FixedPoints.subfield G L)).injective
  change fieldK0Rank (FixedPoints.subfield G L) (fieldK0Class (FixedPoints.subfield G L)
      (FGModuleCat.of (FixedPoints.subfield G L) (galoisTwistedTensorRepresentation G L W ρ).invariants)) =
    fieldK0Rank (FixedPoints.subfield G L) (fieldK0Class (FixedPoints.subfield G L)
      (FGModuleCat.of (FixedPoints.subfield G L) W))
  rw [fieldK0Rank_class, fieldK0Rank_class]
  exact_mod_cast (galoisTwistedTensorDescentEquiv G L W ρ).finrank_eq

end GaloisForLFunctions.RepresentationLifting
