import GaloisForLFunctions.HTGeometry.ABHN.AzumayaTensorProduct

/-!
# Brauer-group structure from tensor products

The quotient `BrauerGroup K` in Mathlib is presented by finite-dimensional central simple
algebras modulo matrix stabilization.  Tensor products give its addition, while the opposite
algebra gives the inverse.  The substantive inverse calculation is
`A ⊗ Aᵐᵒᵖ ≃ Endₖ(A)`, followed by a choice of finite basis of `A`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Brauer equivalence is preserved by taking opposite algebras. -/
theorem isBrauerEquivalent_oppositeCSA {K : Type u} [Field K]
    (A B : CSA.{u, u} K) (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (oppositeCSA A) (oppositeCSA B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ⟨?_⟩⟩
  exact (AlgEquiv.mopMatrix.trans (AlgEquiv.op e)).trans AlgEquiv.mopMatrix.symm

/-- Opposite algebra on Brauer classes. -/
noncomputable def brauerTensorNeg (K : Type u) [Field K] :
    BrauerGroup.{u, u} K → BrauerGroup.{u, u} K :=
  Quotient.lift (fun A ↦ brauerClass (oppositeCSA A))
    (by
      intro A B h
      exact Quotient.sound (isBrauerEquivalent_oppositeCSA A B h))

/-- Opposite algebra on a represented class. -/
theorem brauerTensorNeg_brauerClass (K : Type u) [Field K] (A : CSA.{u, u} K) :
    brauerTensorNeg K (brauerClass A) = brauerClass (oppositeCSA A) := rfl

/-- A central simple algebra tensored with its opposite represents the split Brauer class. -/
theorem brauerClass_tensorProduct_oppositeCSA_eq_split {K : Type u} [Field K]
    (A : CSA.{u, u} K) :
    brauerClass (tensorProductCSA A (oppositeCSA A)) = brauerSplitClass K := by
  letI : NeZero (Module.finrank K A.carrier) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := A.carrier))⟩
  calc
    brauerClass (tensorProductCSA A (oppositeCSA A)) =
        brauerClass (matrixFinCSA (scalarCSA K) (Module.finrank K A.carrier)) := by
      apply brauerClass_eq_of_algEquiv
      exact (AlgEquiv.ofBijective (AlgHom.mulLeftRight K A.carrier)
        (mulLeftRight_bijective_of_csa A)).trans
        (LinearMap.toMatrixAlgEquiv (Module.finBasis K A.carrier))
    _ = brauerSplitClass K := brauerClass_matrixFinCSA_scalar_eq _

/-- Tensoring a Brauer class with its opposite is split. -/
theorem brauerTensorNeg_add_self (K : Type u) [Field K] (x : BrauerGroup.{u, u} K) :
    brauerTensorAdd K (brauerTensorNeg K x) x = brauerSplitClass K := by
  refine Quotient.inductionOn x ?_
  intro A
  change brauerTensorAdd K (brauerTensorNeg K (brauerClass A)) (brauerClass A) =
    brauerSplitClass K
  rw [brauerTensorNeg_brauerClass, brauerTensorAdd_brauerClass]
  calc
    brauerClass (tensorProductCSA (oppositeCSA A) A) =
        brauerClass (tensorProductCSA A (oppositeCSA A)) :=
      brauerClass_eq_of_algEquiv _ _
        (Algebra.TensorProduct.comm K (oppositeCSA A).carrier A.carrier)
    _ = brauerSplitClass K := brauerClass_tensorProduct_oppositeCSA_eq_split A

/-- The tensor-product operations supply the canonical commutative group structure on the
Brauer quotient. -/
noncomputable instance brauerTensorAddCommGroup (K : Type u) [Field K] :
    AddCommGroup (BrauerGroup.{u, u} K) := by
  let brauerMonoid : AddCommMonoid (BrauerGroup.{u, u} K) :=
    { add := brauerTensorAdd K
      add_assoc := brauerTensorAdd_assoc K
      zero := brauerSplitClass K
      zero_add := brauerTensorAdd_split_left K
      add_zero := brauerTensorAdd_split_right K
      nsmul := fun n x ↦ n.rec (brauerSplitClass K) (fun _ y ↦ brauerTensorAdd K y x)
      nsmul_zero := by intro x; rfl
      nsmul_succ := by intro n x; rfl
      add_comm := brauerTensorAdd_comm K }
  letI : AddCommMonoid (BrauerGroup.{u, u} K) := brauerMonoid
  letI : Neg (BrauerGroup.{u, u} K) := ⟨brauerTensorNeg K⟩
  exact
    { toAddCommMonoid := brauerMonoid
      neg := brauerTensorNeg K
      zsmul := zsmulRec
      neg_add_cancel := brauerTensorNeg_add_self K }

end GaloisForLFunctions.HTGeometry.ABHN
