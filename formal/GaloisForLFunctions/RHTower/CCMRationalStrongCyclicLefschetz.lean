import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicClassSpaceAction

/-!
# Real-equivariant CCM Lefschetz action on the strong cyclic target

This file proves that the class-space endomorphisms of the exact CCM strong cyclic target are a
literal group action in every degree and commute with the target Real structure.  The result is the
unquotiented categorical Lefschetz action required before descending along the closed restriction
range.

The proofs are tensorial and unconditional: algebra-homomorphism identity/composition are lifted
to every genuine cyclic tensor power; equivariance of one field factor is lifted to the
componentwise cyclic Real structure.  No trace formula or zero-spectrum statement is asserted.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

universe u

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Field := CCMRationalContinuousTraceNormField

/-! ## Generic tensor functoriality -/

/-- Tensor power of the identity algebra homomorphism is the identity. -/
theorem cyclicBarAlgHomDegree_id
    {A : Type u} [Ring A] [Algebra ℂ A]
    (n : ℕ) (x : CyclicBarTensor ℂ A n) :
    cyclicBarAlgHomDegree (AlgHom.id ℂ A) n x = x := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
        cyclicBarAlgHomDegree_tprod]
      rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Tensor powers preserve composition of algebra homomorphisms. -/
theorem cyclicBarAlgHomDegree_comp
    {A B C : Type u}
    [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    [Ring C] [Algebra ℂ C]
    (φ : B →ₐ[ℂ] C) (ψ : A →ₐ[ℂ] B)
    (n : ℕ) (x : CyclicBarTensor ℂ A n) :
    cyclicBarAlgHomDegree (φ.comp ψ) n x =
      cyclicBarAlgHomDegree φ n (cyclicBarAlgHomDegree ψ n x) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod,
        map_smul, map_smul, map_smul,
        cyclicBarAlgHomDegree_tprod,
        cyclicBarAlgHomDegree_tprod,
        cyclicBarAlgHomDegree_tprod]
      rfl
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- An equivariant algebra homomorphism intertwines the componentwise Real structures on every
cyclic tensor power. -/
theorem cyclicBarDegreeKReal_algHom
    {A B : Type u} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (KA : KRealAlgebraStructure A) (KB : KRealAlgebraStructure B)
    (φ : A →ₐ[ℂ] B)
    (hφ : ∀ a, KB.sigma (φ a) = φ (KA.sigma a))
    (n : ℕ) (x : CyclicBarTensor ℂ A n) :
    (cyclicBarDegreeKReal KB n).sigma
        (cyclicBarAlgHomDegree φ n x) =
      cyclicBarAlgHomDegree φ n
        ((cyclicBarDegreeKReal KA n).sigma x) := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff r f =>
      change
        kRealEvenPiTensorSigma
            (fun _ : Fin (n + 1) => KB.toKRealStructure)
            (cyclicBarAlgHomDegree φ n
              (PiTensorProduct.tprodCoeff ℂ r f)) =
          cyclicBarAlgHomDegree φ n
            (kRealEvenPiTensorSigma
              (fun _ : Fin (n + 1) => KA.toKRealStructure)
              (PiTensorProduct.tprodCoeff ℂ r f))
      rw [PiTensorProduct.tprodCoeff_eq_smul_tprod,
        map_smul, map_smulₛₗ, cyclicBarAlgHomDegree_tprod,
        kRealEvenPiTensorSigma_tprod,
        map_smulₛₗ, map_smul, kRealEvenPiTensorSigma_tprod,
        cyclicBarAlgHomDegree_tprod]
      exact congrArg (fun z => (starRingEnd ℂ r) • z)
        (congrArg (PiTensorProduct.tprod ℂ)
          (funext fun i => hφ (f i)))
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-! ## Exact group law on the class-space action -/

/-- Right translation by the identity is the identity algebra homomorphism. -/
theorem ccmRationalContinuousTraceNormFieldRightActionAlgHom_one :
    ccmRationalContinuousTraceNormFieldRightActionAlgHom 1 =
      AlgHom.id ℂ Field := by
  apply AlgHom.ext
  intro F
  change ccmRationalContinuousTraceNormFieldRightAction 1 F = F
  exact ccmRationalContinuousTraceNormFieldRightAction_one F

/-- Composition of right translations is translation by the product. -/
theorem ccmRationalContinuousTraceNormFieldRightActionAlgHom_comp
    (c d : Section) :
    (ccmRationalContinuousTraceNormFieldRightActionAlgHom c).comp
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom d) =
      ccmRationalContinuousTraceNormFieldRightActionAlgHom (c * d) := by
  apply AlgHom.ext
  intro F
  change
    ccmRationalContinuousTraceNormFieldRightAction c
        (ccmRationalContinuousTraceNormFieldRightAction d F) =
      ccmRationalContinuousTraceNormFieldRightAction (c * d) F
  exact ccmRationalContinuousTraceNormFieldRightAction_mul c d F

/-- Identity acts identically on every exact strong cyclic degree. -/
theorem ccmRationalStrongCyclicRightActionDegree_one
    (n : ℕ) (x : ccmRationalStrongCyclicObjectSubmodule (.mk n)) :
    ccmRationalStrongCyclicRightActionDegree 1 n x = x := by
  apply Subtype.ext
  rw [ccmRationalStrongCyclicRightActionDegree_coe,
    ccmRationalContinuousTraceNormFieldRightActionAlgHom_one]
  exact cyclicBarAlgHomDegree_id n x.1

/-- Exact class-space product law in every strong cyclic degree. -/
theorem ccmRationalStrongCyclicRightActionDegree_mul
    (c d : Section) (n : ℕ)
    (x : ccmRationalStrongCyclicObjectSubmodule (.mk n)) :
    ccmRationalStrongCyclicRightActionDegree c n
        (ccmRationalStrongCyclicRightActionDegree d n x) =
      ccmRationalStrongCyclicRightActionDegree (c * d) n x := by
  apply Subtype.ext
  simp only [ccmRationalStrongCyclicRightActionDegree_coe]
  rw [← cyclicBarAlgHomDegree_comp,
    ccmRationalContinuousTraceNormFieldRightActionAlgHom_comp]

/-! ## Real-equivariant Lefschetz action -/

/-- Every class-space right translation is equivariant for field Real conjugation. -/
theorem ccmRationalContinuousTraceNormFieldRightActionAlgHom_real
    (c : Section) (F : Field) :
    ccmRationalContinuousTraceNormFieldReal
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c F) =
      ccmRationalContinuousTraceNormFieldRightActionAlgHom c
        (ccmRationalContinuousTraceNormFieldReal F) :=
  (ccmRationalContinuousTraceNormFieldRightAction_real c F).symm

/-- Class-space translation commutes with the exact Real structure in every strong cyclic degree. -/
theorem ccmRationalStrongCyclicRightActionDegree_real
    (c : Section) (n : ℕ)
    (x : ccmRationalStrongCyclicSimplicial.degree n) :
    (ccmRationalStrongCyclicDegreeKReal n).sigma
        (ccmRationalStrongCyclicRightActionDegree c n x) =
      ccmRationalStrongCyclicRightActionDegree c n
        ((ccmRationalStrongCyclicDegreeKReal n).sigma x) := by
  apply Subtype.ext
  exact cyclicBarDegreeKReal_algHom
    ccmRationalContinuousTraceNormFieldKRealAlgebra
    ccmRationalContinuousTraceNormFieldKRealAlgebra
    (ccmRationalContinuousTraceNormFieldRightActionAlgHom c)
    (ccmRationalContinuousTraceNormFieldRightActionAlgHom_real c) n x.1

/-- **Real-equivariant CCM Lefschetz endomorphism on the exact strong cyclic target.** -/
def ccmRationalStrongCyclicLefschetz (c : Section) :
    CyclicModule.KRealHom ccmRationalStrongCyclicKReal
      ccmRationalStrongCyclicKReal where
  toHom := ccmRationalStrongCyclicRightAction c
  real_naturality := ccmRationalStrongCyclicRightActionDegree_real c

end RHTower
end GaloisForLFunctions
