import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDoubleCentralizer

/-!
# Maximal subfields split finite central division algebras

Let `S` be a maximal commutative subfield of a finite central division algebra `D/K`.  Right
multiplication makes `D` a left `Sᵐᵒᵖ`-module.  The relative enveloping algebra acts by left and
right multiplication, and the double-centralizer dimension theorem upgrades this faithful action
to an algebra equivalence

`D ⊗[K] Sᵐᵒᵖ ≃ₐ[K] Module.End Sᵐᵒᵖ D`.

Thus every maximal commutative subfield is a splitting field, in the concrete endomorphism-algebra
form used in the theory of central simple algebras.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open MulOpposite

noncomputable section

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D] [Algebra.IsCentral K D]
variable (S : Subalgebra K D) [Field S]

/-- The relative enveloping-algebra action is linear for the right `S`-action when `S` is
commutative. -/
theorem relativeEnvelope_smulCommClass_subfield
    (hcommS : IsMulCommutative S) :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    SMulCommClass (D ⊗[K] Sᵐᵒᵖ) Sᵐᵒᵖ D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  refine ⟨?_⟩
  intro r s x
  induction r using TensorProduct.induction_on with
  | zero =>
      change TensorProduct.Algebra.moduleAux (0 : D ⊗[K] Sᵐᵒᵖ) (s • x) =
        s • TensorProduct.Algebra.moduleAux (0 : D ⊗[K] Sᵐᵒᵖ) x
      simp
  | tmul d t =>
      rw [TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def]
      change d * ((x * (s.unop : D)) * (t.unop : D)) =
        (d * (x * (t.unop : D))) * (s.unop : D)
      have hst : (s.unop : D) * (t.unop : D) =
          (t.unop : D) * (s.unop : D) :=
        setLike_mul_comm s.unop.property t.unop.property
      calc
        d * ((x * (s.unop : D)) * (t.unop : D)) =
            d * (x * ((s.unop : D) * (t.unop : D))) := by rw [mul_assoc]
        _ = d * (x * ((t.unop : D) * (s.unop : D))) := by rw [hst]
        _ = (d * (x * (t.unop : D))) * (s.unop : D) := by simp [mul_assoc]
  | add r t hr ht =>
      rw [add_smul, add_smul, hr, ht, smul_add]

/-- Right `S`-scalars commute with base-field scalars on `D`. -/
theorem subalgebraMop_smulCommClass_base :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    SMulCommClass Sᵐᵒᵖ K D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  refine ⟨?_⟩
  intro s k x
  change (k • x) * (s.unop : D) = k • (x * (s.unop : D))
  simp only [Algebra.smul_def]
  rw [mul_assoc]

/-- Faithful left/right multiplication representation of the relative enveloping algebra. -/
noncomputable def relativeSplittingRepresentation
    (hcommS : IsMulCommutative S) :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) Sᵐᵒᵖ D :=
      relativeEnvelope_smulCommClass_subfield K D S hcommS
    letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
      relativeEnvelope_isScalarTower K D S
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    (D ⊗[K] Sᵐᵒᵖ) →ₐ[K] Module.End Sᵐᵒᵖ D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) Sᵐᵒᵖ D :=
    relativeEnvelope_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
    relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  exact AlgHom.mk'
    (Module.toModuleEnd Sᵐᵒᵖ (S := D ⊗[K] Sᵐᵒᵖ) D) (by
      intro k r
      ext x
      change (k • r) • x = k • (r • x)
      rw [smul_assoc])

theorem relativeSplittingRepresentation_apply
    (hcommS : IsMulCommutative S) (r : D ⊗[K] Sᵐᵒᵖ) (x : D) :
    relativeSplittingRepresentation K D S hcommS r x =
      relativeMulLeftRight K D S r x := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) Sᵐᵒᵖ D :=
    relativeEnvelope_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
    relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  rw [relativeMulLeftRight_apply]
  rfl

theorem relativeSplittingRepresentation_injective
    (hcommS : IsMulCommutative S) :
    Function.Injective (relativeSplittingRepresentation K D S hcommS) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) Sᵐᵒᵖ D :=
    relativeEnvelope_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
    relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  intro r t hrt
  apply relativeMulLeftRight_injective K D S
  ext x
  rw [← relativeSplittingRepresentation_apply K D S hcommS,
    ← relativeSplittingRepresentation_apply K D S hcommS]
  exact LinearMap.congr_fun hrt x

/-- A finite-dimensional `K`-space remains finite over its subfield acting on the right. -/
theorem subalgebraMop_finite :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    Module.Finite Sᵐᵒᵖ D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  exact Module.Finite.of_restrictScalars_finite K Sᵐᵒᵖ D

omit [Field S] in
/-- For maximal commutative `S`, the right `S`-dimension of `D` equals `[S : K]`. -/
theorem maximalCommutativeSubfield_mop_finrank
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    Module.finrank Sᵐᵒᵖ D = Module.finrank K S := by
  letI : Field S := hfieldS.toField
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : Module.Finite Sᵐᵒᵖ D := subalgebraMop_finite K D S
  have hsq := maximalCommutativeSubfield_finrank_sq K D S hcommS hfieldS hmaxS
  have hOp : Module.finrank K Sᵐᵒᵖ = Module.finrank K S :=
    (MulOpposite.opLinearEquiv K : S ≃ₗ[K] Sᵐᵒᵖ).finrank_eq.symm
  have htower := Module.finrank_mul_finrank K Sᵐᵒᵖ D
  rw [hOp] at htower
  have hpos : 0 < Module.finrank K S := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    Module.finrank K S * Module.finrank Sᵐᵒᵖ D = Module.finrank K D := htower
    _ = Module.finrank K S * Module.finrank K S := hsq.symm

omit [Field S] in
/-- Source and target of the splitting representation have equal `K`-dimension. -/
theorem relativeSplittingRepresentation_finrank_eq
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass Sᵐᵒᵖ K D := subalgebraMop_smulCommClass_base K D S
    Module.finrank K (D ⊗[K] Sᵐᵒᵖ) =
      Module.finrank K (Module.End Sᵐᵒᵖ D) := by
  letI : Field S := hfieldS.toField
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass Sᵐᵒᵖ K D := subalgebraMop_smulCommClass_base K D S
  letI : Module.Finite Sᵐᵒᵖ D := subalgebraMop_finite K D S
  have hm := maximalCommutativeSubfield_mop_finrank K D S hcommS hfieldS hmaxS
  calc
    Module.finrank K (D ⊗[K] Sᵐᵒᵖ) =
        Module.finrank K D * Module.finrank K Sᵐᵒᵖ := Module.finrank_tensorProduct
    _ = Module.finrank K D * Module.finrank K S := by
      rw [(MulOpposite.opLinearEquiv K : S ≃ₗ[K] Sᵐᵒᵖ).finrank_eq]
    _ = Module.finrank Sᵐᵒᵖ D * Module.finrank K D := by rw [hm, Nat.mul_comm]
    _ = Module.finrank K (Module.End Sᵐᵒᵖ D) := by
      rw [Module.finrank_linearMap Sᵐᵒᵖ K D D]

omit [Field S] in
theorem relativeSplittingRepresentation_surjective
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    Function.Surjective (relativeSplittingRepresentation K D S hcommS) := by
  letI : Field S := hfieldS.toField
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass Sᵐᵒᵖ K D := subalgebraMop_smulCommClass_base K D S
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (relativeSplittingRepresentation_finrank_eq K D S hcommS hfieldS hmaxS)
    (f := (relativeSplittingRepresentation K D S hcommS).toLinearMap)).mp
  exact relativeSplittingRepresentation_injective K D S hcommS

omit [Field S] in
/-- A maximal commutative subfield splits a finite central division algebra: the relative
enveloping algebra is the full endomorphism algebra of `D` over the right `S`-action. -/
noncomputable def maximalCommutativeSubfieldSplittingAlgEquiv
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass Sᵐᵒᵖ K D := subalgebraMop_smulCommClass_base K D S
    (D ⊗[K] Sᵐᵒᵖ) ≃ₐ[K] Module.End Sᵐᵒᵖ D := by
  letI : Field S := hfieldS.toField
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass Sᵐᵒᵖ K D := subalgebraMop_smulCommClass_base K D S
  exact AlgEquiv.ofBijective (relativeSplittingRepresentation K D S hcommS)
    ⟨relativeSplittingRepresentation_injective K D S hcommS,
      relativeSplittingRepresentation_surjective K D S hcommS hfieldS hmaxS⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
