import GaloisForLFunctions.HTGeometry.AffineExponentialCrossHomFinite
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Kernels of Hopf-algebra morphisms

This file proves missing functorial machinery for closed affine subgroup images.  Antipodes commute
with bialgebra morphisms because both candidate composites are convolution inverses.  Over a field,
the kernel of a morphism of commutative Hopf algebras is then a Hopf ideal.  Coideal closure is
proved by descending through the linear kernel quotient and using injectivity after tensoring.
-/

open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace HopfIdealKernel

noncomputable section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- A morphism of commutative Hopf algebras commutes with antipodes. -/
theorem map_antipode (f : A →ₐc[R] B) :
    (HopfAlgebra.antipodeAlgHom R B).comp f.toAlgHom =
      f.toAlgHom.comp (HopfAlgebra.antipodeAlgHom R A) := by
  let u : WithConv (A →ₐ[R] B) := WithConv.toConv f.toAlgHom
  have hbase := AlgHom.antipode_id_cancel (R := R) (A := B)
  have hpre := AlgHom.convMul_comp_bialgHom_distrib
    (WithConv.toConv (HopfAlgebra.antipodeAlgHom R B))
    (WithConv.toConv (AlgHom.id R B)) f
  rw [hbase] at hpre
  have honecomp :
      (WithConv.ofConv (1 : WithConv (B →ₐ[R] B))).comp f.toAlgHom =
        WithConv.ofConv (1 : WithConv (A →ₐ[R] B)) := by
    ext x
    simp
  have hmul :
      WithConv.toConv ((HopfAlgebra.antipodeAlgHom R B).comp f.toAlgHom) * u = 1 := by
    apply WithConv.ofConv_injective
    exact hpre.symm.trans honecomp
  have hinv := eq_inv_of_mul_eq_one_left hmul
  change WithConv.toConv ((HopfAlgebra.antipodeAlgHom R B).comp f.toAlgHom) =
    WithConv.toConv (f.toAlgHom.comp (HopfAlgebra.antipodeAlgHom R A)) at hinv
  exact WithConv.toConv_injective hinv

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

variable {k C D : Type*} [Field k] [CommRing C] [CommRing D]
  [HopfAlgebra k C] [HopfAlgebra k D]

/-- Over a field, the ring-theoretic kernel of a morphism of commutative Hopf algebras is a Hopf
ideal. -/
theorem ker_isHopfIdeal (f : C →ₐc[k] D) :
    (RingHom.ker (f : C →+* D)).IsHopfIdeal k := by
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro x hx
    change f x = 0 at hx
    have h := DFunLike.congr_fun (BialgHom.counitAlgHom_comp f) x
    change Coalgebra.counit (R := k) (f x) = Coalgebra.counit (R := k) x at h
    rw [hx, map_zero] at h
    exact h.symm
  · intro x hx
    change f x = 0 at hx
    let K : Submodule k C := (RingHom.ker (f : C →+* D)).restrictScalars k
    have hK : K = LinearMap.ker f.toLinearMap := by
      ext y
      change (f y = 0) ↔ (f y = 0)
      rfl
    let g : C ⧸ K →ₗ[k] D := K.liftQ f.toLinearMap (by
      intro y hy
      rw [hK] at hy
      exact hy)
    have hg : Function.Injective g := LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot' K f.toLinearMap hK)
    have hgg : Function.Injective (TensorProduct.map g g) :=
      TensorProduct.map_injective_of_flat_flat _ _ hg hg
    change TensorProduct.map K.mkQ K.mkQ (Coalgebra.comul (R := k) x) = 0
    apply hgg
    rw [TensorProduct.map_map]
    have hcomp : g ∘ₗ K.mkQ = f.toLinearMap := by
      ext y
      rfl
    rw [hcomp]
    have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) x
    change TensorProduct.map f.toLinearMap f.toLinearMap (Coalgebra.comul (R := k) x) =
      Coalgebra.comul (R := k) (f x) at hmap
    rw [hmap, hx, map_zero]
    simp
  · intro x hx
    change f x = 0 at hx
    change f (HopfAlgebra.antipode k x) = 0
    have h := DFunLike.congr_fun (map_antipode f) x
    change HopfAlgebra.antipode k (f x) = f (HopfAlgebra.antipode k x) at h
    rw [hx, map_zero] at h
    exact h.symm

end
end HopfIdealKernel
end GaloisForLFunctions.HTGeometry
