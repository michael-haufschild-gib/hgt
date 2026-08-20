import GaloisForLFunctions.HTGeometry.ABHN.CentralSimpleAzumaya
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of Azumaya algebras

This file supplies the missing central-simple tensor-product theorem over a field.  It identifies
the enveloping algebra of `A ⊗ B` with the tensor product of the two enveloping algebras, and the
endomorphisms of `A ⊗ B` with the tensor product of the two endomorphism algebras.  Therefore a
tensor product of Azumaya algebras is Azumaya; for fields it is central simple.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u

/-- Endomorphisms of the left tensor factor act on a tensor product. -/
noncomputable def tensorProductEnd_left
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] :
    Module.End K A →ₐ[K] Module.End K (A ⊗[K] B) where
  toFun f := LinearMap.rTensor B f
  map_zero' := by
    ext x y
    simp
  map_one' := by
    ext x y
    simp
  map_mul' f g := LinearMap.rTensor_mul B f g
  map_add' f g := by
    ext x y
    simp
  commutes' r := by
    change LinearMap.rTensor B (DistribSMul.toLinearMap K A r) =
      DistribSMul.toLinearMap K (A ⊗[K] B) r
    exact LinearMap.rTensor_smul_action B A r

/-- Endomorphisms of the right tensor factor act on a tensor product. -/
noncomputable def tensorProductEnd_right
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] :
    Module.End K B →ₐ[K] Module.End K (A ⊗[K] B) where
  toFun g := LinearMap.lTensor A g
  map_zero' := by
    ext x y
    simp
  map_one' := by
    ext x y
    simp
  map_mul' f g := LinearMap.lTensor_mul A f g
  map_add' f g := by
    ext x y
    simp
  commutes' r := by
    change LinearMap.lTensor A (DistribSMul.toLinearMap K B r) =
      DistribSMul.toLinearMap K (A ⊗[K] B) r
    exact LinearMap.lTensor_smul_action A B r

/-- The two factorwise endomorphism actions commute. -/
theorem tensorProductEnd_left_right_commute
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (f : Module.End K A) (g : Module.End K B) :
    Commute (tensorProductEnd_left (B := B) f) (tensorProductEnd_right (A := A) g) := by
  change LinearMap.rTensor B f ∘ₗ LinearMap.lTensor A g =
    LinearMap.lTensor A g ∘ₗ LinearMap.rTensor B f
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- The endomorphism tensor product acts on the tensor product of its modules. -/
noncomputable def tensorProductEndAlgHom
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] :
    Module.End K A ⊗[K] Module.End K B →ₐ[K] Module.End K (A ⊗[K] B) :=
  Algebra.TensorProduct.lift (tensorProductEnd_left (B := B))
    (tensorProductEnd_right (A := A))
    (tensorProductEnd_left_right_commute (A := A) (B := B))

/-- On pure endomorphism tensors, the factorwise action is the usual tensor map. -/
theorem tensorProductEndAlgHom_tmul
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (f : Module.End K A) (g : Module.End K B) :
    tensorProductEndAlgHom (A := A) (B := B) (f ⊗ₜ[K] g) =
      TensorProduct.map f g := by
  ext x y
  simp [tensorProductEndAlgHom, tensorProductEnd_left, tensorProductEnd_right]

/-- Matrix-unit endomorphisms of a tensor-product basis are factorwise tensor products. -/
theorem tensorProductEndAlgHom_finBasis_end
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] [FiniteDimensional K A] [FiniteDimensional K B]
    (i k : Fin (Module.finrank K A)) (j l : Fin (Module.finrank K B)) :
    tensorProductEndAlgHom (A := A) (B := B)
        ((Module.finBasis K A).end (i, k) ⊗ₜ[K] (Module.finBasis K B).end (j, l)) =
      ((Module.finBasis K A).tensorProduct (Module.finBasis K B)).end ((i, j), (k, l)) := by
  apply ((Module.finBasis K A).tensorProduct (Module.finBasis K B)).ext
  rintro ⟨i', j'⟩
  conv_lhs => rw [Module.Basis.tensorProduct_apply]
  conv_rhs => rw [Module.Basis.end_apply_apply]
  rw [tensorProductEndAlgHom_tmul, TensorProduct.map_tmul,
    Module.Basis.end_apply_apply]
  simp only [Module.Basis.end_apply_apply, Module.Basis.tensorProduct_apply]
  by_cases hik : k = i'
  · subst i'
    by_cases hjl : l = j'
    · subst j'
      simp
    · simp [hjl]
  · simp [hik]

/-- Every endomorphism of a finite-dimensional tensor product is a sum of factorwise
endomorphisms. -/
theorem tensorProductEndAlgHom_surjective
    {K A B : Type*} [Field K] [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] [FiniteDimensional K A] [FiniteDimensional K B] :
    Function.Surjective (tensorProductEndAlgHom (K := K) (A := A) (B := B)) := by
  let a := Module.finBasis K A
  let b := Module.finBasis K B
  let c : Module.Basis (Fin (Module.finrank K A) × Fin (Module.finrank K B)) K
      (A ⊗[K] B) := a.tensorProduct b
  apply LinearMap.range_eq_top.1
  apply top_unique
  rw [← c.end.span_eq]
  refine Submodule.span_le.2 ?_
  rintro f ⟨⟨⟨i, j⟩, k, l⟩, rfl⟩
  exact ⟨a.end (i, k) ⊗ₜ[K] b.end (j, l),
    tensorProductEndAlgHom_finBasis_end i k j l⟩

/-- The opposite of a tensor product is obtained by reversing its two factors. -/
noncomputable def tensorProductOppositeAlgHom
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B] :
    Bᵐᵒᵖ ⊗[K] Aᵐᵒᵖ →ₐ[K] (A ⊗[K] B)ᵐᵒᵖ :=
  Algebra.TensorProduct.lift
    (AlgHom.op (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B))
    (AlgHom.op (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B))
    (by
      intro b a
      change MulOpposite.op (1 ⊗ₜ[K] b.unop) * MulOpposite.op (a.unop ⊗ₜ[K] 1) =
        MulOpposite.op (a.unop ⊗ₜ[K] 1) * MulOpposite.op (1 ⊗ₜ[K] b.unop)
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul]
      simp)

/-- Formula for reversing a pure tensor into the opposite algebra. -/
theorem tensorProductOppositeAlgHom_tmul
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (b : Bᵐᵒᵖ) (a : Aᵐᵒᵖ) :
    tensorProductOppositeAlgHom (K := K) (A := A) (B := B) (b ⊗ₜ[K] a) =
      MulOpposite.op (a.unop ⊗ₜ[K] b.unop) := by
  change MulOpposite.op (1 ⊗ₜ[K] b.unop) * MulOpposite.op (a.unop ⊗ₜ[K] 1) =
    MulOpposite.op (a.unop ⊗ₜ[K] b.unop)
  rw [← MulOpposite.op_mul]
  simp

/-- The opposite-tensor map is surjective without any finite-dimensionality assumption. -/
theorem tensorProductOppositeAlgHom_surjective
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B] :
    Function.Surjective (tensorProductOppositeAlgHom (K := K) (A := A) (B := B)) := by
  intro x
  have h : ∀ z : A ⊗[K] B, ∃ y,
      tensorProductOppositeAlgHom (K := K) (A := A) (B := B) y = MulOpposite.op z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        refine ⟨0, ?_⟩
        simp [tensorProductOppositeAlgHom]
    | add z z' hz hz' =>
        obtain ⟨y, hy⟩ := hz
        obtain ⟨y', hy'⟩ := hz'
        refine ⟨y + y', ?_⟩
        simp [map_add, hy, hy']
    | tmul a b =>
        refine ⟨MulOpposite.op b ⊗ₜ[K] MulOpposite.op a, ?_⟩
        exact tensorProductOppositeAlgHom_tmul (K := K) (A := A) (B := B)
          (MulOpposite.op b) (MulOpposite.op a)
  simpa using h x.unop

/-- Over a field, reversing factors identifies the opposite tensor product as an algebra
equivalence. -/
theorem tensorProductOppositeAlgHom_bijective
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B] :
    Function.Bijective (tensorProductOppositeAlgHom (K := K) (A := A) (B := B)) := by
  refine ⟨?_, tensorProductOppositeAlgHom_surjective⟩
  change Function.Injective
    (tensorProductOppositeAlgHom (K := K) (A := A) (B := B)).toLinearMap
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    tensorProductOppositeAlgHom_surjective
  calc
    Module.finrank K (Bᵐᵒᵖ ⊗[K] Aᵐᵒᵖ) =
        Module.finrank K Bᵐᵒᵖ * Module.finrank K Aᵐᵒᵖ := Module.finrank_tensorProduct
    _ = Module.finrank K B * Module.finrank K Aᵐᵒᵖ := by
      rw [← (MulOpposite.opLinearEquiv K (M := B)).finrank_eq]
    _ = Module.finrank K B * Module.finrank K A := by
      rw [← (MulOpposite.opLinearEquiv K (M := A)).finrank_eq]
    _ = Module.finrank K A * Module.finrank K B := mul_comm _ _
    _ = Module.finrank K (A ⊗[K] B) := Module.finrank_tensorProduct.symm
    _ = Module.finrank K (A ⊗[K] B)ᵐᵒᵖ := by
      exact (MulOpposite.opLinearEquiv K (M := A ⊗[K] B)).finrank_eq

/-- The algebra equivalence reversing the two factors inside an opposite tensor product. -/
noncomputable def tensorProductOppositeAlgEquiv
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B] :
    Bᵐᵒᵖ ⊗[K] Aᵐᵒᵖ ≃ₐ[K] (A ⊗[K] B)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (tensorProductOppositeAlgHom (K := K) (A := A) (B := B))
    tensorProductOppositeAlgHom_bijective

/-- The enveloping algebra of `A ⊗ B` is the tensor product of the two enveloping algebras,
with its four factors permuted into left-right order. -/
noncomputable def tensorProductEnvelopeAlgEquiv
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B] :
    ((A ⊗[K] B) ⊗[K] (A ⊗[K] B)ᵐᵒᵖ) ≃ₐ[K]
      (A ⊗[K] Aᵐᵒᵖ) ⊗[K] (B ⊗[K] Bᵐᵒᵖ) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
    (tensorProductOppositeAlgEquiv (K := K) (A := A) (B := B)).symm).trans <|
  (Algebra.TensorProduct.assoc K K K A B (Bᵐᵒᵖ ⊗[K] Aᵐᵒᵖ)).trans <|
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
    (Algebra.TensorProduct.assoc K K K B Bᵐᵒᵖ Aᵐᵒᵖ).symm).trans <|
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
    (Algebra.TensorProduct.comm K (B ⊗[K] Bᵐᵒᵖ) Aᵐᵒᵖ)).trans <|
  (Algebra.TensorProduct.assoc K K K A Aᵐᵒᵖ (B ⊗[K] Bᵐᵒᵖ)).symm

/-- Formula for the inverse factor-reversal equivalence on a pure opposite tensor. -/
theorem tensorProductOppositeAlgEquiv_symm_op_tmul
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B] (a : A) (b : B) :
    (tensorProductOppositeAlgEquiv (K := K) (A := A) (B := B)).symm
      (MulOpposite.op (a ⊗ₜ[K] b)) =
        MulOpposite.op b ⊗ₜ[K] MulOpposite.op a := by
  apply (tensorProductOppositeAlgEquiv (K := K) (A := A) (B := B)).injective
  rw [AlgEquiv.apply_symm_apply]
  exact tensorProductOppositeAlgHom_tmul (K := K) (A := A) (B := B)
    (MulOpposite.op b) (MulOpposite.op a) |>.symm

/-- Formula for the enveloping-algebra permutation on four pure factors. -/
theorem tensorProductEnvelopeAlgEquiv_tmul
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B]
    (a a' : A) (b b' : B) :
    tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)
      ((a ⊗ₜ[K] b) ⊗ₜ[K] MulOpposite.op (a' ⊗ₜ[K] b')) =
        (a ⊗ₜ[K] MulOpposite.op a') ⊗ₜ[K] (b ⊗ₜ[K] MulOpposite.op b') := by
  simp [tensorProductEnvelopeAlgEquiv,
    tensorProductOppositeAlgEquiv_symm_op_tmul]

/-- Formula for the inverse enveloping-algebra permutation on four pure factors. -/
theorem tensorProductEnvelopeAlgEquiv_symm_tmul
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B]
    (a : A) (a' : Aᵐᵒᵖ) (b : B) (b' : Bᵐᵒᵖ) :
    (tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)).symm
      ((a ⊗ₜ[K] a') ⊗ₜ[K] (b ⊗ₜ[K] b')) =
        (a ⊗ₜ[K] b) ⊗ₜ[K] MulOpposite.op (a'.unop ⊗ₜ[K] b'.unop) := by
  apply (tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa using tensorProductEnvelopeAlgEquiv_tmul (K := K) (A := A) (B := B)
    a a'.unop b b'.unop |>.symm

/-- The enveloping-algebra permutation intertwines left-right multiplication with the factorwise
endomorphism action. -/
theorem mulLeftRight_tensorProductEnvelopeAlgEquiv_symm_tmul
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B]
    (a : A) (a' : Aᵐᵒᵖ) (b : B) (b' : Bᵐᵒᵖ) :
    AlgHom.mulLeftRight K (A ⊗[K] B)
      ((tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)).symm
        ((a ⊗ₜ[K] a') ⊗ₜ[K] (b ⊗ₜ[K] b'))) =
      tensorProductEndAlgHom (A := A) (B := B)
        (AlgHom.mulLeftRight K A (a ⊗ₜ[K] a') ⊗ₜ[K]
          AlgHom.mulLeftRight K B (b ⊗ₜ[K] b')) := by
  rw [tensorProductEnvelopeAlgEquiv_symm_tmul, tensorProductEndAlgHom_tmul]
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul x y =>
      simp only [AlgHom.mulLeftRight_apply, TensorProduct.map_tmul]
      simp only [MulOpposite.unop_op]
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The left-right action commutes with the enveloping-algebra permutation on arbitrary tensors. -/
theorem mulLeftRight_tensorProductEnvelopeAlgEquiv_symm
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [FiniteDimensional K A] [FiniteDimensional K B]
    (z : (A ⊗[K] Aᵐᵒᵖ) ⊗[K] (B ⊗[K] Bᵐᵒᵖ)) :
    AlgHom.mulLeftRight K (A ⊗[K] B)
      ((tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)).symm z) =
      tensorProductEndAlgHom (A := A) (B := B)
        (Algebra.TensorProduct.map (AlgHom.mulLeftRight K A) (AlgHom.mulLeftRight K B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' =>
          rw [TensorProduct.add_tmul]
          simp only [map_add]
          rw [hx, hx']
      | tmul a a' =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y y' hy hy' =>
              rw [TensorProduct.tmul_add]
              simp only [map_add]
              rw [hy, hy']
          | tmul b b' =>
              simpa only [Algebra.TensorProduct.map_tmul] using
                mulLeftRight_tensorProductEnvelopeAlgEquiv_symm_tmul
                  (K := K) (A := A) (B := B) a a' b b'

/-- Tensor products of Azumaya algebras over a field are Azumaya. -/
theorem isAzumaya_tensorProduct
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    [IsAzumaya K A] [IsAzumaya K B] : IsAzumaya K (A ⊗[K] B) := by
  letI : Nontrivial A := ⟨0, 1, fun h => zero_ne_one <|
    FaithfulSMul.algebraMap_injective K A (by simp [h])⟩
  letI : Nontrivial B := ⟨0, 1, fun h => zero_ne_one <|
    FaithfulSMul.algebraMap_injective K B (by simp [h])⟩
  letI : Nontrivial (A ⊗[K] B) := Function.Injective.nontrivial
    (Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective K A))
  refine { bij := ?_ }
  have hsurj : Function.Surjective (AlgHom.mulLeftRight K (A ⊗[K] B)) := by
    intro f
    obtain ⟨t, ht⟩ := tensorProductEndAlgHom_surjective (K := K) (A := A) (B := B) f
    have hsurjTensor : Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.mulLeftRight K A) (AlgHom.mulLeftRight K B)) :=
      Algebra.TensorProduct.map_surjective (f := AlgHom.mulLeftRight K A)
        (g := AlgHom.mulLeftRight K B)
        (IsAzumaya.bij.2 : Function.Surjective (AlgHom.mulLeftRight K A))
        (IsAzumaya.bij.2 : Function.Surjective (AlgHom.mulLeftRight K B))
    obtain ⟨z, hz⟩ := hsurjTensor t
    refine ⟨(tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)).symm z, ?_⟩
    calc
      AlgHom.mulLeftRight K (A ⊗[K] B)
          ((tensorProductEnvelopeAlgEquiv (K := K) (A := A) (B := B)).symm z) =
          tensorProductEndAlgHom (A := A) (B := B)
            (Algebra.TensorProduct.map (AlgHom.mulLeftRight K A) (AlgHom.mulLeftRight K B) z) :=
        mulLeftRight_tensorProductEnvelopeAlgEquiv_symm z
      _ = tensorProductEndAlgHom (A := A) (B := B) t := congrArg _ hz
      _ = f := ht
  refine ⟨?_, hsurj⟩
  change Function.Injective (AlgHom.mulLeftRight K (A ⊗[K] B)).toLinearMap
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr hsurj
  calc
    Module.finrank K ((A ⊗[K] B) ⊗[K] (A ⊗[K] B)ᵐᵒᵖ) =
        Module.finrank K (A ⊗[K] B) * Module.finrank K (A ⊗[K] B)ᵐᵒᵖ :=
      Module.finrank_tensorProduct
    _ = Module.finrank K (A ⊗[K] B) * Module.finrank K (A ⊗[K] B) := by
      rw [← (MulOpposite.opLinearEquiv K (M := A ⊗[K] B)).finrank_eq]
    _ = Module.finrank K (Module.End K (A ⊗[K] B)) := by
      rw [Module.finrank_linearMap]

/-- Tensor products of finite-dimensional central simple algebras are simple rings. -/
theorem tensorProduct_isSimpleRing {K : Type u} [Field K]
    (A B : CSA.{u, u} K) : IsSimpleRing (A.carrier ⊗[K] B.carrier) := by
  letI : IsAzumaya K A.carrier := csa_isAzumaya A
  letI : IsAzumaya K B.carrier := csa_isAzumaya B
  letI : IsAzumaya K (A.carrier ⊗[K] B.carrier) :=
    isAzumaya_tensorProduct (K := K) (A := A.carrier) (B := B.carrier)
  exact isSimpleRing_of_isAzumaya (K := K) _

/-- The tensor product of two central simple representatives, packaged as a central simple
algebra. -/
noncomputable def tensorProductCSA {K : Type u} [Field K]
    (A B : CSA.{u, u} K) : CSA.{u, u} K where
  carrier := A.carrier ⊗[K] B.carrier
  isCentral := tensorProductAlg_isCentral A B
  isSimple := tensorProduct_isSimpleRing A B
  fin_dim := tensorProductAlg_finiteDimensional A B

/-- Moving a square matrix factor through an arbitrary tensor product. -/
noncomputable def matrixTensorProductAlgEquiv
    {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (n : Type*) [Fintype n] [DecidableEq n] :
    (Matrix n n A) ⊗[K] B ≃ₐ[K] Matrix n n (A ⊗[K] B) :=
  (Algebra.TensorProduct.congr (matrixEquivTensor n K A) (AlgEquiv.refl)).trans <|
  (Algebra.TensorProduct.assoc K K K A (Matrix n n K) B).trans <|
  (Algebra.TensorProduct.congr (AlgEquiv.refl)
    (Algebra.TensorProduct.comm K (Matrix n n K) B)).trans <|
  (Algebra.TensorProduct.assoc K K K A B (Matrix n n K)).symm.trans <|
  (matrixEquivTensor n K (A ⊗[K] B)).symm

/-- Brauer equivalence is stable under tensoring on the right by a central simple algebra. -/
theorem isBrauerEquivalent_tensorProduct_left {K : Type u} [Field K]
    (A B C : CSA.{u, u} K) (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (tensorProductCSA A C) (tensorProductCSA B C) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  refine ⟨(matrixTensorProductAlgEquiv (K := K) (A := A.carrier) (B := C.carrier)
    (Fin n)).symm.trans ?_⟩
  refine (Algebra.TensorProduct.congr e (AlgEquiv.refl)).trans ?_
  exact matrixTensorProductAlgEquiv (K := K) (A := B.carrier) (B := C.carrier) (Fin m)

/-- Tensor-product representatives commute up to algebra equivalence. -/
theorem isBrauerEquivalent_tensorProduct_comm {K : Type u} [Field K]
    (A B : CSA.{u, u} K) :
    IsBrauerEquivalent (tensorProductCSA A B) (tensorProductCSA B A) :=
  isBrauerEquivalent_of_algEquiv _ _ (Algebra.TensorProduct.comm K A.carrier B.carrier)

/-- Brauer equivalence is stable under tensoring on the left by a central simple algebra. -/
theorem isBrauerEquivalent_tensorProduct_right {K : Type u} [Field K]
    (A B C : CSA.{u, u} K) (h : IsBrauerEquivalent B C) :
    IsBrauerEquivalent (tensorProductCSA A B) (tensorProductCSA A C) :=
  (isBrauerEquivalent_tensorProduct_comm A B).trans
    ((isBrauerEquivalent_tensorProduct_left B C A h).trans
      (isBrauerEquivalent_tensorProduct_comm A C).symm)

/-- Tensoring preserves Brauer equivalence in both arguments. -/
theorem isBrauerEquivalent_tensorProduct {K : Type u} [Field K]
    (A A' B B' : CSA.{u, u} K) (hA : IsBrauerEquivalent A A')
    (hB : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (tensorProductCSA A B) (tensorProductCSA A' B') :=
  (isBrauerEquivalent_tensorProduct_left A A' B hA).trans
    (isBrauerEquivalent_tensorProduct_right A' B B' hB)

/-- Tensor-product addition on the Brauer quotient.  It is defined directly on quotient classes
because tensoring respects the matrix-stabilization relation in either argument. -/
noncomputable def brauerTensorAdd (K : Type u) [Field K] :
    BrauerGroup.{u, u} K → BrauerGroup.{u, u} K → BrauerGroup.{u, u} K :=
  Quotient.lift
    (fun A ↦ Quotient.lift
      (fun B ↦ brauerClass (tensorProductCSA A B))
      (by
        intro B B' h
        exact Quotient.sound (isBrauerEquivalent_tensorProduct_right A B B' h)))
    (by
      intro A A' h
      funext x
      refine Quotient.inductionOn x ?_
      intro B
      exact Quotient.sound (isBrauerEquivalent_tensorProduct_left A A' B h))

/-- Tensor-product addition is represented by the tensor product of central simple algebras. -/
theorem brauerTensorAdd_brauerClass (K : Type u) [Field K]
    (A B : CSA.{u, u} K) :
    brauerTensorAdd K (brauerClass A) (brauerClass B) = brauerClass (tensorProductCSA A B) := rfl

/-- Tensor-product addition on the Brauer quotient is commutative. -/
theorem brauerTensorAdd_comm (K : Type u) [Field K]
    (x y : BrauerGroup.{u, u} K) : brauerTensorAdd K x y = brauerTensorAdd K y x := by
  refine Quotient.inductionOn x ?_
  intro A
  refine Quotient.inductionOn y ?_
  intro B
  change brauerTensorAdd K (brauerClass A) (brauerClass B) =
    brauerTensorAdd K (brauerClass B) (brauerClass A)
  rw [brauerTensorAdd_brauerClass, brauerTensorAdd_brauerClass]
  exact brauerClass_eq_of_algEquiv _ _ (Algebra.TensorProduct.comm K A.carrier B.carrier)

/-- The split class is a left identity for tensor-product addition. -/
theorem brauerTensorAdd_split_left (K : Type u) [Field K]
    (x : BrauerGroup.{u, u} K) : brauerTensorAdd K (brauerSplitClass K) x = x := by
  refine Quotient.inductionOn x ?_
  intro A
  change brauerTensorAdd K (brauerClass (scalarCSA K)) (brauerClass A) = brauerClass A
  rw [brauerTensorAdd_brauerClass]
  exact brauerClass_eq_of_algEquiv _ _ (Algebra.TensorProduct.lid K A.carrier)

/-- The split class is a right identity for tensor-product addition. -/
theorem brauerTensorAdd_split_right (K : Type u) [Field K]
    (x : BrauerGroup.{u, u} K) : brauerTensorAdd K x (brauerSplitClass K) = x := by
  rw [brauerTensorAdd_comm]
  exact brauerTensorAdd_split_left K x

/-- Tensor-product addition on the Brauer quotient is associative. -/
theorem brauerTensorAdd_assoc (K : Type u) [Field K]
    (x y z : BrauerGroup.{u, u} K) :
    brauerTensorAdd K (brauerTensorAdd K x y) z =
      brauerTensorAdd K x (brauerTensorAdd K y z) := by
  refine Quotient.inductionOn x ?_
  intro A
  refine Quotient.inductionOn y ?_
  intro B
  refine Quotient.inductionOn z ?_
  intro C
  change brauerTensorAdd K
      (brauerTensorAdd K (brauerClass A) (brauerClass B)) (brauerClass C) =
    brauerTensorAdd K (brauerClass A)
      (brauerTensorAdd K (brauerClass B) (brauerClass C))
  rw [brauerTensorAdd_brauerClass, brauerTensorAdd_brauerClass,
    brauerTensorAdd_brauerClass, brauerTensorAdd_brauerClass]
  exact brauerClass_eq_of_algEquiv _ _
    (Algebra.TensorProduct.assoc K K K A.carrier B.carrier C.carrier)

end GaloisForLFunctions.HTGeometry.ABHN
