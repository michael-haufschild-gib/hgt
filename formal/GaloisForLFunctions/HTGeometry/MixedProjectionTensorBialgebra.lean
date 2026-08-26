import GaloisForLFunctions.HTGeometry.MixedProjectionTensorPresentation

/-!
# Bialgebra structure on the mixed projection tensor presentation

The joint tensor presentation of the two projection images is compatible with counit and
comultiplication.  The canonical map from the original mixed coordinate algebra onto this tensor
presentation is a surjective bialgebra morphism, and composing it with the joint presentation is
the original subgroup quotient map.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace MixedProjectionTensorBialgebra

noncomputable section

open AffineExponentialGroup AffineExponentialProjectionImages
open AffineExponentialProjectionClassification
open GroupAlgebraHopfIdealClassification
open SymmetricAlgebraSubmoduleQuotient
open MixedTorusProjectionSaturation
open MixedAdditiveProjectionClassification
open MixedProjectionTensorPresentation

variable (k : Type*) [Field k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

local instance torusProjectionHopfIdeal :
    (torusProjectionIdeal k I).IsHopfIdeal k :=
  torusProjectionIdeal_isHopfIdeal k I

local instance additiveProjectionHopfIdeal :
    (additiveProjectionIdeal k I).IsHopfIdeal k :=
  additiveProjectionIdeal_isHopfIdeal k I

local instance mixedQuotientCoideal :
    (I.restrictScalars k).IsCoideal := Ideal.IsHopfIdeal.toIsCoideal

local instance mixedQuotientHopfAlgebra :
    HopfAlgebra k (CoordinateAlgebra k n ⧸ I) := by
  infer_instance

/-- The character-group quotient map with its codomain expressed through the exact torus relation
lattice of the mixed ideal. -/
noncomputable def torusRelationQuotientBialgHom :
    TorusCoordinateAlgebra k n →ₐc[k]
      AddMonoidAlgebra k
        ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) :=
  quotientGroupMap (torusProjectionIdeal k I)

@[simp] theorem torusRelationQuotientBialgHom_apply
    (x : TorusCoordinateAlgebra k n) :
    torusRelationQuotientBialgHom k I x =
      quotientGroupMap (torusProjectionIdeal k I) x := rfl

theorem torusRelationQuotientBialgHom_surjective :
    Function.Surjective (torusRelationQuotientBialgHom k I) :=
  quotientGroupMap_surjective (torusProjectionIdeal k I)

/-- Surjective bialgebra quotient from original mixed coordinates to the tensor product of the two
classified projection coordinate algebras. -/
noncomputable def mixedProjectionTensorQuotientBialgHom :
    CoordinateAlgebra k n →ₐc[k]
      AddMonoidAlgebra k
          ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) ⊗[k]
        SymmetricAlgebra k
          ((Fin n → k) ⧸ additiveRelationSubspace k I) :=
  Bialgebra.TensorProduct.map
    (torusRelationQuotientBialgHom k I)
    (SymmetricAlgebraSubmoduleQuotient.quotientBialgHom
      (additiveRelationSubspace k I))

@[simp] theorem mixedProjectionTensorQuotientBialgHom_tmul
    (x : TorusCoordinateAlgebra k n) (y : AdditiveCoordinateAlgebra k n) :
    mixedProjectionTensorQuotientBialgHom k I (x ⊗ₜ[k] y) =
      torusRelationQuotientBialgHom k I x ⊗ₜ[k]
        SymmetricAlgebraSubmoduleQuotient.quotientBialgHom
          (additiveRelationSubspace k I) y := by
  change torusRelationQuotientBialgHom k I x ⊗ₜ[k]
      SymmetricAlgebraSubmoduleQuotient.quotientMap
        (additiveRelationSubspace k I) y = _
  rfl

theorem mixedProjectionTensorQuotientBialgHom_surjective :
    Function.Surjective (mixedProjectionTensorQuotientBialgHom k I) := by
  intro p
  induction p using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', by simp⟩
  | tmul x y =>
      obtain ⟨x', rfl⟩ := torusRelationQuotientBialgHom_surjective k I x
      obtain ⟨y', rfl⟩ :=
        SymmetricAlgebraSubmoduleQuotient.quotientBialgHom_surjective
          (additiveRelationSubspace k I) y
      exact ⟨x' ⊗ₜ[k] y', by
        rw [mixedProjectionTensorQuotientBialgHom_tmul]⟩

theorem torusRelationGroupAlgHomIntoSubgroupQuotient_torusRelationQuotient
    (x : TorusCoordinateAlgebra k n) :
    torusRelationGroupAlgHomIntoSubgroupQuotient k I
        (torusRelationQuotientBialgHom k I x) =
      torusProjectionMap k I x :=
  torusRelationGroupAlgHomIntoSubgroupQuotient_quotientGroupMap k I x

theorem additiveRelationSymmetricAlgHomIntoSubgroupQuotient_quotientBialgHom
    (x : AdditiveCoordinateAlgebra k n) :
    additiveRelationSymmetricAlgHomIntoSubgroupQuotient k I
        (SymmetricAlgebraSubmoduleQuotient.quotientBialgHom
          (additiveRelationSubspace k I) x) =
      additiveProjectionMap k I x :=
  additiveRelationSymmetricAlgHomIntoSubgroupQuotient_quotientMap k I x

/-- Composing the joint tensor presentation with the original-coordinate quotient recovers the
actual mixed subgroup quotient map. -/
theorem mixedProjectionTensorAlgHom_comp_quotientBialgHom :
    (mixedProjectionTensorAlgHom k I).comp
        (mixedProjectionTensorQuotientBialgHom k I).toAlgHom =
      (subgroupQuotientMap k I).toAlgHom := by
  apply DFunLike.ext'
  funext p
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      change mixedProjectionTensorAlgHom k I
          (mixedProjectionTensorQuotientBialgHom k I (x ⊗ₜ[k] y)) =
        subgroupQuotientMap k I (x ⊗ₜ[k] y)
      rw [mixedProjectionTensorQuotientBialgHom_tmul,
        mixedProjectionTensorAlgHom_tmul,
        torusRelationGroupAlgHomIntoSubgroupQuotient_torusRelationQuotient,
        additiveRelationSymmetricAlgHomIntoSubgroupQuotient_quotientBialgHom]
      simp only [torusProjectionMap, additiveProjectionMap, subgroupQuotientMap]
      change Ideal.Quotient.mk I (x ⊗ₜ[k] 1) *
          Ideal.Quotient.mk I (1 ⊗ₜ[k] y) =
        Ideal.Quotient.mk I (x ⊗ₜ[k] y)
      rw [← map_mul]
      congr 1
      simp

/-- The joint projection presentation is a bialgebra morphism. -/
noncomputable def mixedProjectionTensorBialgHom :
    AddMonoidAlgebra k
        ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) ⊗[k]
      SymmetricAlgebra k
        ((Fin n → k) ⧸ additiveRelationSubspace k I) →ₐc[k]
      CoordinateAlgebra k n ⧸ I :=
  BialgHom.ofAlgHom
    (R := k)
    (A := AddMonoidAlgebra k
        ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) ⊗[k]
      SymmetricAlgebra k
        ((Fin n → k) ⧸ additiveRelationSubspace k I))
    (B := CoordinateAlgebra k n ⧸ I)
    (mixedProjectionTensorAlgHom k I) (by
    apply DFunLike.ext'
    funext z
    obtain ⟨p, rfl⟩ := mixedProjectionTensorQuotientBialgHom_surjective k I z
    have hcomp := DFunLike.congr_fun
      (mixedProjectionTensorAlgHom_comp_quotientBialgHom k I) p
    have hfp : mixedProjectionTensorAlgHom k I
        (mixedProjectionTensorQuotientBialgHom k I p) =
      subgroupQuotientMap k I p := hcomp
    simp only [AlgHom.comp_apply]
    rw [hfp]
    simp) (by
    apply DFunLike.ext'
    funext z
    obtain ⟨p, rfl⟩ := mixedProjectionTensorQuotientBialgHom_surjective k I z
    let q := mixedProjectionTensorQuotientBialgHom k I
    let f := mixedProjectionTensorAlgHom k I
    let g := subgroupQuotientMap k I
    have hcomp : f.comp q.toAlgHom = g.toAlgHom :=
      mixedProjectionTensorAlgHom_comp_quotientBialgHom k I
    have hfp : f (q p) = g p := DFunLike.congr_fun hcomp p
    simp only [AlgHom.comp_apply]
    rw [hfp]
    have hq := CoalgHomClass.map_comp_comul_apply q p
    have hg := CoalgHomClass.map_comp_comul_apply g p
    change Algebra.TensorProduct.map q.toAlgHom q.toAlgHom
        ((Bialgebra.comulAlgHom k (CoordinateAlgebra k n)) p) =
      (Bialgebra.comulAlgHom k
        (AddMonoidAlgebra k
            ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) ⊗[k]
          SymmetricAlgebra k
            ((Fin n → k) ⧸ additiveRelationSubspace k I))) (q p) at hq
    change Algebra.TensorProduct.map g.toAlgHom g.toAlgHom
        ((Bialgebra.comulAlgHom k (CoordinateAlgebra k n)) p) =
      (Bialgebra.comulAlgHom k (CoordinateAlgebra k n ⧸ I)) (g p) at hg
    rw [← hq, ← hg]
    let w := (Bialgebra.comulAlgHom k (CoordinateAlgebra k n)) p
    change Algebra.TensorProduct.map f f
        (Algebra.TensorProduct.map q.toAlgHom q.toAlgHom w) =
      Algebra.TensorProduct.map g.toAlgHom g.toAlgHom w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x y =>
        have hx : f (q.toAlgHom x) = g.toAlgHom x :=
          DFunLike.congr_fun hcomp x
        have hy : f (q.toAlgHom y) = g.toAlgHom y :=
          DFunLike.congr_fun hcomp y
        simp only [Algebra.TensorProduct.map_tmul]
        rw [hx, hy])

theorem mixedProjectionTensorBialgHom_toAlgHom :
    (mixedProjectionTensorBialgHom k I).toAlgHom =
      mixedProjectionTensorAlgHom k I := rfl

theorem mixedProjectionTensorBialgHom_surjective :
    Function.Surjective (mixedProjectionTensorBialgHom k I) :=
  mixedProjectionTensorAlgHom_surjective k I

end
end MixedProjectionTensorBialgebra
end GaloisForLFunctions.HTGeometry
