import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import GaloisForLFunctions.HTGeometry.ShortExactRankConservation
import GaloisForLFunctions.HTGeometry.GrothendieckKTheoryIntersectionApplications

/-!
# The Grothendieck group of finite-dimensional vector spaces

The carrier starts with actual objects of `FGModuleCat K`, identified by
isomorphism. Dimension classifies these objects, with direct sums and tensor
products giving addition and multiplication. Grothendieck completion then
gives the integer-valued rank, and every short exact sequence satisfies the
corresponding additive class relation.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open CategoryTheory Algebra
open scoped TensorProduct
universe u
variable (K : Type u) [Field K]

/-- Isomorphism classes of actual finite-dimensional vector spaces. -/
def FiniteVectorSpaceClasses : Type (u + 1) :=
  Quotient (CategoryTheory.isIsomorphicSetoid (FGModuleCat.{u} K))

def finiteVectorSpaceClass (V : FGModuleCat.{u} K) : FiniteVectorSpaceClasses K :=
  Quotient.mk _ V

def finiteVectorSpaceRank : FiniteVectorSpaceClasses K → ℕ :=
  Quotient.lift (fun V : FGModuleCat.{u} K => Module.finrank K V)
    (by rintro V W ⟨e⟩; exact (FGModuleCat.isoToLinearEquiv e).finrank_eq)

theorem finiteVectorSpaceRank_class (V : FGModuleCat.{u} K) :
    finiteVectorSpaceRank K (finiteVectorSpaceClass K V) = Module.finrank K V := rfl

/-- Dimension completely classifies finite-dimensional vector spaces. -/
def finiteVectorSpaceClassesEquivNat : FiniteVectorSpaceClasses K ≃ ℕ where
  toFun := finiteVectorSpaceRank K
  invFun n := finiteVectorSpaceClass K (FGModuleCat.of K (Fin n → K))
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro V
    apply Quotient.sound
    exact ⟨(Module.finBasis K V).equivFun.symm.toFGModuleCatIso⟩
  right_inv n := by
    change Module.finrank K (Fin n → K) = n
    simp

instance : CommSemiring (FiniteVectorSpaceClasses K) :=
  (finiteVectorSpaceClassesEquivNat K).commSemiring

def finiteVectorSpaceRankEquiv : FiniteVectorSpaceClasses K ≃+* ℕ :=
  (finiteVectorSpaceClassesEquivNat K).ringEquiv

/-- Addition of classes is represented by the actual direct sum. -/
theorem finiteVectorSpaceClass_prod (V W : FGModuleCat.{u} K) :
    finiteVectorSpaceClass K (FGModuleCat.of K (V × W)) =
      finiteVectorSpaceClass K V + finiteVectorSpaceClass K W := by
  apply (finiteVectorSpaceRankEquiv K).injective
  rw [map_add]
  exact Module.finrank_prod

/-- Multiplication of classes is represented by the actual tensor product. -/
theorem finiteVectorSpaceClass_tensor (V W : FGModuleCat.{u} K) :
    finiteVectorSpaceClass K (FGModuleCat.of K (V ⊗[K] W)) =
      finiteVectorSpaceClass K V * finiteVectorSpaceClass K W := by
  apply (finiteVectorSpaceRankEquiv K).injective
  rw [map_mul]
  exact Module.finrank_tensorProduct

theorem finiteVectorSpaceClass_field :
    finiteVectorSpaceClass K (FGModuleCat.of K K) = 1 := by
  apply (finiteVectorSpaceRankEquiv K).injective
  rw [map_one]
  exact Module.finrank_self K

/-- Grothendieck completion of finite-dimensional vector spaces under direct sum. -/
abbrev FieldK0 := GrothendieckAddGroup (FiniteVectorSpaceClasses K)

/-- Rank identifies the Grothendieck group of a field with the integers. -/
def fieldK0EquivInt : FieldK0 K ≃+ ℤ :=
  (GaloisForLFunctions.HTGeometry.grothendieckAddGroupCongr
    (finiteVectorSpaceRankEquiv K).toAddEquiv).trans
      GaloisForLFunctions.HTGeometry.naturalMultiplicityK0EquivInt

def fieldK0Rank : FieldK0 K →+ ℤ :=
  (fieldK0EquivInt K).toAddMonoidHom

def fieldK0Class (V : FGModuleCat.{u} K) : FieldK0 K :=
  GrothendieckAddGroup.of (finiteVectorSpaceClass K V)

theorem fieldK0Rank_class (V : FGModuleCat.{u} K) :
    fieldK0Rank K (fieldK0Class K V) = (Module.finrank K V : ℤ) := by
  change GaloisForLFunctions.HTGeometry.naturalMultiplicityK0Class
    (GaloisForLFunctions.HTGeometry.grothendieckAddGroupMap
      (finiteVectorSpaceRankEquiv K).toAddEquiv.toAddMonoidHom
      (GrothendieckAddGroup.of (finiteVectorSpaceClass K V))) = _
  rw [GaloisForLFunctions.HTGeometry.grothendieckAddGroupMap_of,
    GaloisForLFunctions.HTGeometry.naturalMultiplicityK0Class_of]
  rfl

theorem fieldK0Class_prod (V W : FGModuleCat.{u} K) :
    fieldK0Class K (FGModuleCat.of K (V × W)) = fieldK0Class K V + fieldK0Class K W := by
  unfold fieldK0Class
  rw [finiteVectorSpaceClass_prod, map_add]

theorem finiteVectorSpaceClass_eq_nsmul_field (V : FGModuleCat.{u} K) :
    finiteVectorSpaceClass K V =
      Module.finrank K V • finiteVectorSpaceClass K (FGModuleCat.of K K) := by
  apply (finiteVectorSpaceRankEquiv K).injective
  rw [map_nsmul, finiteVectorSpaceClass_field, map_one]
  change Module.finrank K V = Module.finrank K V • (1 : ℕ)
  simp

theorem fieldK0Class_eq_nsmul_field (V : FGModuleCat.{u} K) :
    fieldK0Class K V = Module.finrank K V • fieldK0Class K (FGModuleCat.of K K) := by
  unfold fieldK0Class
  rw [finiteVectorSpaceClass_eq_nsmul_field, map_nsmul]

def integerToFieldK0 : ℤ →+ FieldK0 K :=
  zmultiplesHom _ (fieldK0Class K (FGModuleCat.of K K))

theorem fieldK0Rank_rightInverse (z : ℤ) :
    fieldK0Rank K (integerToFieldK0 K z) = z := by
  change fieldK0Rank K (z • fieldK0Class K (FGModuleCat.of K K)) = z
  rw [map_zsmul, fieldK0Rank_class]
  simp

theorem fieldK0Rank_leftInverse (x : FieldK0 K) :
    integerToFieldK0 K (fieldK0Rank K x) = x := by
  apply (fieldK0EquivInt K).injective
  exact fieldK0Rank_rightInverse K (fieldK0Rank K x)

/-- Every short exact sequence gives the defining additive relation of algebraic `K₀`. -/
theorem fieldK0Class_shortExact (A B C : FGModuleCat.{u} K)
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : LinearMap.range f = LinearMap.ker g) :
    fieldK0Class K B = fieldK0Class K A + fieldK0Class K C := by
  apply (fieldK0EquivInt K).injective
  change fieldK0Rank K (fieldK0Class K B) = fieldK0Rank K (fieldK0Class K A + fieldK0Class K C)
  rw [map_add, fieldK0Rank_class, fieldK0Rank_class, fieldK0Rank_class]
  exact_mod_cast (_root_.HTGeometry.finrank_add_of_shortExact f g hf hg hfg).symm

def fieldK0Tensor (x y : FieldK0 K) : FieldK0 K :=
  (fieldK0EquivInt K).symm (fieldK0Rank K x * fieldK0Rank K y)

theorem fieldK0Tensor_class (V W : FGModuleCat.{u} K) :
    fieldK0Tensor K (fieldK0Class K V) (fieldK0Class K W) =
      fieldK0Class K (FGModuleCat.of K (V ⊗[K] W)) := by
  apply (fieldK0EquivInt K).injective
  rw [fieldK0Tensor, AddEquiv.apply_symm_apply]
  change fieldK0Rank K (fieldK0Class K V) * fieldK0Rank K (fieldK0Class K W) =
    fieldK0Rank K (fieldK0Class K (FGModuleCat.of K (V ⊗[K] W)))
  rw [fieldK0Rank_class, fieldK0Rank_class, fieldK0Rank_class]
  exact_mod_cast (Module.finrank_tensorProduct (R := K) (S := K) (M := V) (M' := W)).symm

end GaloisForLFunctions.RepresentationLifting
