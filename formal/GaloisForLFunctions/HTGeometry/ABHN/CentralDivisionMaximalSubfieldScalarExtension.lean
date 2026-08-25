import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionMaximalSubfieldSplitting
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer

/-!
# Maximal-subfield scalar extension and Brauer splitting

For a maximal commutative subfield `S` of a finite central division algebra `D/K`, right
multiplication makes `D` an `S`-vector space.  The standard scalar extension `S ⊗[K] D` acts on
this space by

`(s ⊗ d) • x = d * x * s`.

The action is faithful because scalar extension of a central simple algebra is simple.  The
double-centralizer dimension formula makes it surjective.  Consequently this file proves the
standard splitting equivalences

`S ⊗[K] D ≃ₐ[S] Module.End S D`

and

`S ⊗[K] D ≃ₐ[S] Matrix (Fin [S : K]) (Fin [S : K]) S`,

then proves that scalar extension sends the Brauer class of `D` to the split class over `S`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open MulOpposite

noncomputable section

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D] [Algebra.IsCentral K D]
variable (S : Subalgebra K D)

def subalgebraRightRingHom (hcommS : IsMulCommutative S) : S →+* Dᵐᵒᵖ :=
  (Subalgebra.val S).toRingHom.toOpposite fun s t =>
    setLike_mul_comm s.property t.property

@[reducible] def subalgebraRightSMul (hcommS : IsMulCommutative S) : SMul S D :=
  (Module.compHom D (subalgebraRightRingHom K D S hcommS)).toSMul

@[reducible] def subalgebraRightModule (hcommS : IsMulCommutative S) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    Module S D := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  exact Module.compHom D (subalgebraRightRingHom K D S hcommS)

theorem subalgebraRight_smul_def (hcommS : IsMulCommutative S) (s : S) (x : D) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    s • x = x * (s : D) := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  rfl

theorem subalgebraRight_isScalarTower (hcommS : IsMulCommutative S) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    IsScalarTower K S D := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  refine ⟨?_⟩
  intro k s x
  change x * ((k • s : S) : D) = k • (x * (s : D))
  rw [Algebra.smul_def, Algebra.smul_def]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  rw [← mul_assoc, (Algebra.commutes k x).symm, mul_assoc]

theorem subalgebraRight_smulCommClass_left (hcommS : IsMulCommutative S) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    SMulCommClass S D D := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  refine ⟨?_⟩
  intro s d x
  change d * x * (s : D) = d * (x * (s : D))
  rw [mul_assoc]

theorem subalgebraRight_isScalarTower_self (hcommS : IsMulCommutative S) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    IsScalarTower S S D := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  refine ⟨?_⟩
  intro s t x
  change x * ((s * t : S) : D) = (x * (t : D)) * (s : D)
  rw [Subalgebra.coe_mul, setLike_mul_comm s.property t.property, mul_assoc]

theorem subalgebraRight_smulCommClass_self (hcommS : IsMulCommutative S) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    SMulCommClass S S D := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  refine ⟨?_⟩
  intro s t x
  change (x * (t : D)) * (s : D) = (x * (s : D)) * (t : D)
  rw [mul_assoc, mul_assoc, setLike_mul_comm t.property s.property]

theorem scalarExtension_smulCommClass_subfield (hcommS : IsMulCommutative S) :
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
    letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
    letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
    SMulCommClass (S ⊗[K] D) S D := by
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  refine ⟨?_⟩
  intro r s x
  induction r using TensorProduct.induction_on with
  | zero =>
      change TensorProduct.Algebra.moduleAux (0 : S ⊗[K] D) (x * (s : D)) =
        TensorProduct.Algebra.moduleAux (0 : S ⊗[K] D) x * (s : D)
      simp
  | tmul t d =>
      rw [TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def]
      change (d * (x * (s : D))) * (t : D) = (d * x) * (t : D) * (s : D)
      have hst : (s : D) * (t : D) = (t : D) * (s : D) :=
        setLike_mul_comm s.property t.property
      simp only [mul_assoc]
      rw [hst]
  | add r t hr ht =>
      rw [add_smul, add_smul, hr, ht]
      change (r • x) * (s : D) + (t • x) * (s : D) =
        (r • x + t • x) * (s : D)
      rw [add_mul]

theorem scalarExtension_isScalarTower_subfield
    (hcommS : IsMulCommutative S) (hfieldS : IsField S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
    letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
    letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
    IsScalarTower S (S ⊗[K] D) D := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  refine ⟨?_⟩
  intro s r x
  induction r using TensorProduct.induction_on with
  | zero =>
      rw [smul_zero]
      change TensorProduct.Algebra.moduleAux (0 : S ⊗[K] D) x =
        TensorProduct.Algebra.moduleAux (0 : S ⊗[K] D) x * (s : D)
      simp
  | tmul t d =>
      rw [TensorProduct.smul_tmul', TensorProduct.Algebra.smul_def,
        TensorProduct.Algebra.smul_def]
      change (d * x) * ((s * t : S) : D) = ((d * x) * (t : D)) * (s : D)
      simp only [Subalgebra.coe_mul, mul_assoc]
      rw [setLike_mul_comm s.property t.property]
  | add r t hr ht =>
      rw [smul_add, add_smul, add_smul, hr, ht]
      change (r • x) * (s : D) + (t • x) * (s : D) =
        (r • x + t • x) * (s : D)
      rw [add_mul]

noncomputable def maximalSubfieldScalarExtensionRepresentation
    (hcommS : IsMulCommutative S) (hfieldS : IsField S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
    letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
    letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
    letI : SMulCommClass (S ⊗[K] D) S D :=
      scalarExtension_smulCommClass_subfield K D S hcommS
    letI : IsScalarTower S (S ⊗[K] D) D :=
      scalarExtension_isScalarTower_subfield K D S hcommS hfieldS
    letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
    letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
    letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
    (S ⊗[K] D) →ₐ[S] Module.End S D := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  letI : SMulCommClass (S ⊗[K] D) S D :=
    scalarExtension_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower S (S ⊗[K] D) D :=
    scalarExtension_isScalarTower_subfield K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
  exact AlgHom.mk'
    (Module.toModuleEnd S (S := S ⊗[K] D) D) (by
      intro s r
      ext x
      change (s • r) • x = s • (r • x)
      exact smul_assoc s r x)

theorem maximalSubfieldScalarExtensionRepresentation_apply
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (r : S ⊗[K] D) (x : D) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
    letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
    letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
    maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS r x = r • x := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  letI : SMulCommClass (S ⊗[K] D) S D :=
    scalarExtension_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower S (S ⊗[K] D) D :=
    scalarExtension_isScalarTower_subfield K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
  rfl

theorem subalgebraRight_finite
    (hcommS : IsMulCommutative S) (hfieldS : IsField S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    Module.Finite S D := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  exact Module.Finite.of_restrictScalars_finite K S D

theorem maximalCommutativeSubfield_right_finrank
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    Module.finrank S D = Module.finrank K S := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : Module.Finite S D := subalgebraRight_finite K D S hcommS hfieldS
  have hsq := maximalCommutativeSubfield_finrank_sq K D S hcommS hfieldS hmaxS
  have htower := Module.finrank_mul_finrank K S D
  have hpos : 0 < Module.finrank K S := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    Module.finrank K S * Module.finrank S D = Module.finrank K D := htower
    _ = Module.finrank K S * Module.finrank K S := hsq.symm

theorem maximalSubfieldScalarExtensionRepresentation_injective
    (hcommS : IsMulCommutative S) (hfieldS : IsField S) :
    letI : Field S := hfieldS.toField
    Function.Injective
      (maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS) := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  letI : SMulCommClass (S ⊗[K] D) S D :=
    scalarExtension_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower S (S ⊗[K] D) D :=
    scalarExtension_isScalarTower_subfield K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
  letI : IsSimpleRing (S ⊗[K] D) :=
    scalarExtension_isSimpleRing (centralDivisionCSA K D)
  exact RingHom.injective _

theorem maximalSubfieldScalarExtensionRepresentation_finrank_eq
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
    letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
    letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
    Module.finrank S (S ⊗[K] D) = Module.finrank S (Module.End S D) := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : Module.Finite S D := subalgebraRight_finite K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
  have hm := maximalCommutativeSubfield_right_finrank K D S hcommS hfieldS hmaxS
  have hsq := maximalCommutativeSubfield_finrank_sq K D S hcommS hfieldS hmaxS
  calc
    Module.finrank S (S ⊗[K] D) = Module.finrank K D := Module.finrank_baseChange
    _ = Module.finrank K S * Module.finrank K S := hsq.symm
    _ = Module.finrank S D * Module.finrank S D := by rw [hm]
    _ = Module.finrank S (Module.End S D) := by rw [Module.finrank_linearMap]

theorem maximalSubfieldScalarExtensionRepresentation_surjective
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    Function.Surjective
      (maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS) := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : Module.Finite S D := subalgebraRight_finite K D S hcommS hfieldS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  letI : SMulCommClass (S ⊗[K] D) S D :=
    scalarExtension_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower S (S ⊗[K] D) D :=
    scalarExtension_isScalarTower_subfield K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Module S (Module.End S D) := LinearMap.module
  letI : Module.Finite S (Module.End S D) := Module.Finite.linearMap S S D D
  let f : (S ⊗[K] D) →ₗ[S] Module.End S D :=
    { toFun := maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS
      map_add' := map_add
        (maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS)
      map_smul' := by
        intro s r
        ext x
        change
          maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS (s • r) x =
            s • maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS r x
        rw [maximalSubfieldScalarExtensionRepresentation_apply,
          maximalSubfieldScalarExtensionRepresentation_apply]
        change (s • r) • x = s • (r • x)
        exact smul_assoc s r x }
  have hf : Function.Injective f :=
    maximalSubfieldScalarExtensionRepresentation_injective K D S hcommS hfieldS
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (maximalSubfieldScalarExtensionRepresentation_finrank_eq
      K D S hcommS hfieldS hmaxS) (f := f)).mp hf

noncomputable def maximalSubfieldScalarExtensionSplittingAlgEquiv
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
    letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
    letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
    (S ⊗[K] D) ≃ₐ[S] Module.End S D := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : IsScalarTower K S D := subalgebraRight_isScalarTower K D S hcommS
  letI : SMulCommClass S D D := subalgebraRight_smulCommClass_left K D S hcommS
  letI : Module (S ⊗[K] D) D := TensorProduct.Algebra.module
  letI : SMulCommClass (S ⊗[K] D) S D :=
    scalarExtension_smulCommClass_subfield K D S hcommS
  letI : IsScalarTower S (S ⊗[K] D) D :=
    scalarExtension_isScalarTower_subfield K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
  exact AlgEquiv.ofBijective
    (maximalSubfieldScalarExtensionRepresentation K D S hcommS hfieldS)
    ⟨maximalSubfieldScalarExtensionRepresentation_injective K D S hcommS hfieldS,
      maximalSubfieldScalarExtensionRepresentation_surjective
        K D S hcommS hfieldS hmaxS⟩

noncomputable def maximalSubfieldScalarExtensionMatrixAlgEquiv
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    letI : SMul S D := subalgebraRightSMul K D S hcommS
    letI : Module S D := subalgebraRightModule K D S hcommS
    S ⊗[K] D ≃ₐ[S] Matrix (Fin (Module.finrank S D)) (Fin (Module.finrank S D)) S := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : Module.Finite S D := subalgebraRight_finite K D S hcommS hfieldS
  letI : IsScalarTower S S D := subalgebraRight_isScalarTower_self K D S hcommS
  letI : SMulCommClass S S D := subalgebraRight_smulCommClass_self K D S hcommS
  letI : Algebra S (Module.End S D) := Module.End.instAlgebra S S D
  exact (maximalSubfieldScalarExtensionSplittingAlgEquiv
    K D S hcommS hfieldS hmaxS).trans
      (LinearMap.toMatrixAlgEquiv (Module.finBasis S D))

theorem scalarExtensionBrauerMap_centralDivisionCSA_eq_split_of_maximalSubfield
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    letI : Field S := hfieldS.toField
    scalarExtensionBrauerMap K S (brauerClass (centralDivisionCSA K D)) =
      brauerSplitClass S := by
  letI : Field S := hfieldS.toField
  letI : SMul S D := subalgebraRightSMul K D S hcommS
  letI : Module S D := subalgebraRightModule K D S hcommS
  letI : Module.Finite S D := subalgebraRight_finite K D S hcommS hfieldS
  letI : NeZero (Module.finrank S D) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := S) (M := D))⟩
  rw [scalarExtensionBrauerMap_brauerClass]
  calc
    brauerClass (scalarExtensionCSA (L := S) (centralDivisionCSA K D)) =
        brauerClass (matrixFinCSA (scalarCSA S) (Module.finrank S D)) :=
      brauerClass_eq_of_algEquiv _ _
        (maximalSubfieldScalarExtensionMatrixAlgEquiv
          K D S hcommS hfieldS hmaxS)
    _ = brauerSplitClass S :=
      brauerClass_matrixFinCSA_scalar_eq (Module.finrank S D)

end

/-- Every nonsplit Brauer class has a nontrivial finite maximal subfield whose scalar extension
splits the class.  The witness also retains the separable seed and self-centralizer data needed
for later local-field refinements. -/
theorem brauerGroup_ne_split_exists_maximalSubfield_scalarExtension_eq_split
    (K : Type u) [Field K] (x : BrauerGroup K) (hx : x ≠ brauerSplitClass K) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D) (y : D)
      (S : Subalgebra K D) (hcommS : IsMulCommutative S) (hfieldS : IsField S),
      x = brauerClass (centralDivisionCSA K D) ∧
        y ∉ (⊥ : Subalgebra K D) ∧ IsSeparable K y ∧
          Algebra.adjoin K ({y} : Set D) ≤ S ∧
            1 < Module.finrank K S ∧
              (∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) ∧
                Subalgebra.centralizer K (S : Set D) = S ∧
                  (letI : Field S := hfieldS.toField
                   scalarExtensionBrauerMap K S x = brauerSplitClass S) := by
  obtain ⟨D, hD, aD, finD, centralD, y, S, hclass, hybase, hysep, hyS,
      hcommS, hfieldS, hdegree, hmaxS, hcentralizer⟩ :=
    brauerGroup_ne_split_exists_maximalCommutativeSubfield K x hx
  refine ⟨D, hD, aD, finD, centralD, y, S, hcommS, hfieldS,
    hclass, hybase, hysep, hyS, hdegree, hmaxS, hcentralizer, ?_⟩
  letI : Field S := hfieldS.toField
  rw [hclass]
  exact scalarExtensionBrauerMap_centralDivisionCSA_eq_split_of_maximalSubfield
    K D S hcommS hfieldS hmaxS

end GaloisForLFunctions.HTGeometry.ABHN
