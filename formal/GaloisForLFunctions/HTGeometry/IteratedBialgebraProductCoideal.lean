import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductStabilization
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Coideal law for a stable affine product image

Coassociativity and the canonical tensor associator identify multiplication of two finite product
blocks with one combined block.  Once product-image kernels stabilize, this regrouping proves the
exact quotient-tensor coideal law for the stable kernel.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry

universe u

noncomputable section

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- Naturality of the canonical linear tensor associator. -/
theorem tensorProduct_assoc_natural
    {k M N P M' N' P' : Type u} [Field k]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module k M] [Module k N] [Module k P]
    [Module k M'] [Module k N'] [Module k P']
    (f : M →ₗ[k] M') (g : N →ₗ[k] N') (h : P →ₗ[k] P') :
    (TensorProduct.assoc k M' N' P').toLinearMap.comp
        (TensorProduct.map (TensorProduct.map f g) h) =
      (TensorProduct.map f (TensorProduct.map g h)).comp
        (TensorProduct.assoc k M N P).toLinearMap := by
  ext m n p
  simp

/-- Pullback of multiplying one `(p+1)`-factor block and one `(q+1)`-factor block. -/
def combinedProductLinearMap
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (p q : ℕ) :
    A →ₗ[k] IteratedTensorAlgebra k B p ⊗[k] IteratedTensorAlgebra k B q :=
  (TensorProduct.map (iteratedProductMap f p).toLinearMap
    (iteratedProductMap f q).toLinearMap).comp (Coalgebra.comul (R := k))

/-- A one-factor left block recovers the recursive iterated product map. -/
theorem combinedProductLinearMap_zero_left
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (q : ℕ) :
    combinedProductLinearMap f 0 q = (iteratedProductMap f (q + 1)).toLinearMap := by
  ext a
  change TensorProduct.map f.toLinearMap (iteratedProductMap f q).toLinearMap
      (Coalgebra.comul (R := k) a) =
    tensorAlgHom f (iteratedProductMap f q) (Coalgebra.comul (R := k) a)
  rw [← DFunLike.congr_fun
    (tensorAlgHom_toLinearMap f (iteratedProductMap f q))
      (Coalgebra.comul (R := k) a)]
  rfl

/-- Moving one factor across the tensor associator is exactly bialgebra coassociativity. -/
theorem combinedProductLinearMap_succ_left_assoc
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (p q : ℕ) :
    (TensorProduct.assoc k
      B (IteratedTensorAlgebra k B p) (IteratedTensorAlgebra k B q)).toLinearMap.comp
        (combinedProductLinearMap f (p + 1) q) =
      (TensorProduct.map f.toLinearMap (combinedProductLinearMap f p q)).comp
        (Coalgebra.comul (R := k)) := by
  ext a
  have hcoassoc := DFunLike.congr_fun
    (Coalgebra.coassoc (R := k) (A := A)) a
  have hnat := DFunLike.congr_fun
    (tensorProduct_assoc_natural f.toLinearMap
      (iteratedProductMap f p).toLinearMap
      (iteratedProductMap f q).toLinearMap)
    ((LinearMap.rTensor A (Coalgebra.comul (R := k)))
      (Coalgebra.comul (R := k) a))
  have hsucc : (iteratedProductMap f (p + 1)).toLinearMap =
      (TensorProduct.map f.toLinearMap
        (iteratedProductMap f p).toLinearMap).comp
          (Coalgebra.comul (R := k)) := by
    ext x
    change tensorAlgHom f (iteratedProductMap f p)
        (Coalgebra.comul (R := k) x) =
      TensorProduct.map f.toLinearMap (iteratedProductMap f p).toLinearMap
        (Coalgebra.comul (R := k) x)
    exact DFunLike.congr_fun
      (tensorAlgHom_toLinearMap f (iteratedProductMap f p))
        (Coalgebra.comul (R := k) x)
  have hleftInput : combinedProductLinearMap f (p + 1) q a =
      TensorProduct.map
        (TensorProduct.map f.toLinearMap (iteratedProductMap f p).toLinearMap)
        (iteratedProductMap f q).toLinearMap
        ((LinearMap.rTensor A (Coalgebra.comul (R := k)))
          (Coalgebra.comul (R := k) a)) := by
    rw [combinedProductLinearMap, LinearMap.comp_apply, hsucc]
    change TensorProduct.map
        ((TensorProduct.map f.toLinearMap
          (iteratedProductMap f p).toLinearMap).comp (Coalgebra.comul (R := k)))
        (iteratedProductMap f q).toLinearMap (Coalgebra.comul (R := k) a) = _
    simpa [LinearMap.rTensor] using
      (TensorProduct.map_map
        (TensorProduct.map f.toLinearMap (iteratedProductMap f p).toLinearMap)
        (iteratedProductMap f q).toLinearMap
        (Coalgebra.comul (R := k)) (LinearMap.id (R := k) (M := A))
        (Coalgebra.comul (R := k) a)).symm
  have hnat' :
      (TensorProduct.assoc k
        B (IteratedTensorAlgebra k B p) (IteratedTensorAlgebra k B q))
          (TensorProduct.map
            (TensorProduct.map f.toLinearMap (iteratedProductMap f p).toLinearMap)
            (iteratedProductMap f q).toLinearMap
            ((LinearMap.rTensor A (Coalgebra.comul (R := k)))
              (Coalgebra.comul (R := k) a))) =
        TensorProduct.map f.toLinearMap
          (TensorProduct.map (iteratedProductMap f p).toLinearMap
            (iteratedProductMap f q).toLinearMap)
          ((TensorProduct.assoc k A A A)
            ((LinearMap.rTensor A (Coalgebra.comul (R := k)))
              (Coalgebra.comul (R := k) a))) := by
    simpa [LinearMap.comp_apply] using hnat
  have hcoassoc' :
      (TensorProduct.assoc k A A A)
          ((LinearMap.rTensor A (Coalgebra.comul (R := k)))
            (Coalgebra.comul (R := k) a)) =
        (LinearMap.lTensor A (Coalgebra.comul (R := k)))
          (Coalgebra.comul (R := k) a) := by
    simpa [LinearMap.comp_apply] using hcoassoc
  rw [LinearMap.comp_apply, hleftInput]
  calc
    _ = TensorProduct.map f.toLinearMap
          (TensorProduct.map (iteratedProductMap f p).toLinearMap
            (iteratedProductMap f q).toLinearMap)
          ((TensorProduct.assoc k A A A)
            ((LinearMap.rTensor A (Coalgebra.comul (R := k)))
              (Coalgebra.comul (R := k) a))) := hnat'
    _ = TensorProduct.map f.toLinearMap
          (TensorProduct.map (iteratedProductMap f p).toLinearMap
            (iteratedProductMap f q).toLinearMap)
          ((LinearMap.lTensor A (Coalgebra.comul (R := k)))
            (Coalgebra.comul (R := k) a)) := by rw [hcoassoc']
    _ = (TensorProduct.map f.toLinearMap (combinedProductLinearMap f p q))
          (Coalgebra.comul (R := k) a) := by
      simpa [LinearMap.lTensor, combinedProductLinearMap] using
        (TensorProduct.map_map f.toLinearMap
          (TensorProduct.map (iteratedProductMap f p).toLinearMap
            (iteratedProductMap f q).toLinearMap)
          (LinearMap.id (R := k) (M := A)) (Coalgebra.comul (R := k))
          (Coalgebra.comul (R := k) a))

/-- Multiplying two finite product blocks has the same kernel as one block containing all factors. -/
theorem combinedProductLinearMap_ker
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (p q : ℕ) :
    LinearMap.ker (combinedProductLinearMap f p q) =
      LinearMap.ker (iteratedProductMap f (q + p + 1)).toLinearMap := by
  induction p with
  | zero =>
      rw [combinedProductLinearMap_zero_left]
  | succ p ih =>
      let r := q + p + 1
      have htensor := tensorProduct_map_ker_eq_of_right_ker_eq
        f.toLinearMap (combinedProductLinearMap f p q)
          (iteratedProductMap f r).toLinearMap ih
      ext a
      simp only [LinearMap.mem_ker]
      have hassoc := DFunLike.congr_fun
        (combinedProductLinearMap_succ_left_assoc f p q) a
      have htensorAt := SetLike.ext_iff.mp htensor (Coalgebra.comul (R := k) a)
      change combinedProductLinearMap f (p + 1) q a = 0 ↔
        iteratedProductMap f (q + (p + 1) + 1) a = 0
      have hsucc :
          iteratedProductMap f (r + 1) a =
            TensorProduct.map f.toLinearMap (iteratedProductMap f r).toLinearMap
              (Coalgebra.comul (R := k) a) := by
        change tensorAlgHom f (iteratedProductMap f r)
            (Coalgebra.comul (R := k) a) = _
        exact DFunLike.congr_fun
          (tensorAlgHom_toLinearMap f (iteratedProductMap f r))
            (Coalgebra.comul (R := k) a)
      change combinedProductLinearMap f (p + 1) q a = 0 ↔
        iteratedProductMap f (r + 1) a = 0
      rw [hsucc]
      constructor
      · intro ha
        have hzAssoc :
            (TensorProduct.assoc k
              B (IteratedTensorAlgebra k B p) (IteratedTensorAlgebra k B q))
                (combinedProductLinearMap f (p + 1) q a) = 0 := by
          rw [ha, map_zero]
        rw [show (TensorProduct.assoc k
              B (IteratedTensorAlgebra k B p) (IteratedTensorAlgebra k B q))
                (combinedProductLinearMap f (p + 1) q a) =
              TensorProduct.map f.toLinearMap (combinedProductLinearMap f p q)
                (Coalgebra.comul (R := k) a) by
            simpa [LinearMap.comp_apply] using hassoc] at hzAssoc
        exact htensorAt.mp hzAssoc
      · intro ha
        have hzAssoc :
            TensorProduct.map f.toLinearMap (combinedProductLinearMap f p q)
                (Coalgebra.comul (R := k) a) = 0 := htensorAt.mpr ha
        apply (TensorProduct.assoc k
          B (IteratedTensorAlgebra k B p) (IteratedTensorAlgebra k B q)).injective
        rw [map_zero]
        rw [show (TensorProduct.assoc k
              B (IteratedTensorAlgebra k B p) (IteratedTensorAlgebra k B q))
                (combinedProductLinearMap f (p + 1) q a) =
              TensorProduct.map f.toLinearMap (combinedProductLinearMap f p q)
                (Coalgebra.comul (R := k) a) by
            simpa [LinearMap.comp_apply] using hassoc]
        exact hzAssoc

/-- The stable product-image kernel satisfies the exact quotient-tensor coideal law. -/
theorem iteratedProductKernel_stable_comul_quotient_eq_zero
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (m : ℕ)
    (hstable : iteratedProductKernel f (m + 1) = iteratedProductKernel f m)
    (a : A) (ha : a ∈ iteratedProductKernel f m) :
    TensorProduct.map
      ((iteratedProductKernel f m).restrictScalars k).mkQ
      ((iteratedProductKernel f m).restrictScalars k).mkQ
      (Coalgebra.comul (R := k) a) = 0 := by
  let K : Submodule k A := (iteratedProductKernel f m).restrictScalars k
  let g : A ⧸ K →ₗ[k] IteratedTensorAlgebra k B m :=
    K.liftQ (iteratedProductMap f m).toLinearMap (by
      intro x hx
      exact hx)
  have hK : K = LinearMap.ker (iteratedProductMap f m).toLinearMap := by
    ext x
    change (iteratedProductMap f m x = 0) ↔
      (iteratedProductMap f m x = 0)
    rfl
  have hg : Function.Injective g := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' K (iteratedProductMap f m).toLinearMap hK)
  have hgg : Function.Injective (TensorProduct.map g g) :=
    TensorProduct.map_injective_of_flat_flat _ _ hg hg
  apply hgg
  rw [TensorProduct.map_map]
  have hcomp : g.comp K.mkQ = (iteratedProductMap f m).toLinearMap := by
    ext x
    rfl
  rw [hcomp]
  change combinedProductLinearMap f m m a = 0
  change a ∈ LinearMap.ker (combinedProductLinearMap f m m)
  rw [combinedProductLinearMap_ker]
  change a ∈ iteratedProductKernel f (m + m + 1)
  have hlate := iteratedProductKernel_stable_add f m hstable (m + 1)
  rw [show m + m + 1 = m + (m + 1) by omega, hlate]
  exact ha

end

end GaloisForLFunctions.HTGeometry
