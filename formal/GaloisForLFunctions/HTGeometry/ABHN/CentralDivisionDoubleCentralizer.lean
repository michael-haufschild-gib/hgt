import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionMaximalSubfield
import GaloisForLFunctions.HTGeometry.ABHN.CentralSimpleAzumaya
import Mathlib.Algebra.Module.Bimodule
import Mathlib.RingTheory.Flat.Basic

/-!
# Double centralizers in finite central division algebras

Let `S` be a commutative subfield of a finite central division algebra `D/K`.  Regard `D` as a
module over the relative enveloping algebra `D ⊗[K] Sᵐᵒᵖ`.  This module is simple, and its
endomorphism division ring is the centralizer `C_D(S)` (with opposite multiplication suppressed
at the level of the underlying `K`-vector space).  Relative Jacobson density then gives the
double-centralizer dimension formula

`[S : K] * [C_D(S) : K] = [D : K]`.

For a maximal commutative subfield, `C_D(S) = S`; hence `[D : K] = [S : K]²`.  This is the
dimension theorem needed before a maximal subfield can be identified as a splitting field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open MulOpposite

noncomputable section

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D]
variable (S : Subalgebra K D) [Field S]

/-- Inclusion of the opposite of a commutative subfield into the opposite division algebra. -/
def subalgebraMopRingHom : Sᵐᵒᵖ →+* Dᵐᵒᵖ :=
  (Subalgebra.val S).toRingHom.op

/-- Right multiplication by `S`, presented as a left `Sᵐᵒᵖ`-module structure on `D`. -/
@[reducible] def subalgebraMopModule : Module Sᵐᵒᵖ D :=
  Module.compHom D (subalgebraMopRingHom K D S)

/-- Base-field scalars associate with the right `S`-action. -/
theorem subalgebraMopIsScalarTower :
    @IsScalarTower K Sᵐᵒᵖ D _ (subalgebraMopModule K D S).toSMul _ := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  refine ⟨?_⟩
  intro k s x
  change x * ((k • s).unop : D) = k • (x * (s.unop : D))
  rw [MulOpposite.unop_smul, Algebra.smul_def, Algebra.smul_def]
  simp only [Subalgebra.coe_mul]
  rw [Subalgebra.coe_algebraMap]
  rw [← mul_assoc, (Algebra.commutes k x).symm, mul_assoc]

/-- Left multiplication by `D` commutes with right multiplication by `S`. -/
theorem subalgebraMopSMulCommClass :
    @SMulCommClass D Sᵐᵒᵖ D _ (subalgebraMopModule K D S).toSMul := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  refine ⟨?_⟩
  intro d s x
  change d * (x * (s.unop : D)) = (d * x) * (s.unop : D)
  rw [mul_assoc]

/-- The base-field action associates with the relative enveloping-algebra action. -/
theorem relativeEnvelope_isScalarTower :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  refine ⟨?_⟩
  intro k ds x
  change TensorProduct.Algebra.moduleAux _ _ =
    _ • TensorProduct.Algebra.moduleAux _ _
  simp

/-- Relative enveloping-algebra scalars commute with base-field scalars. -/
theorem relativeEnvelope_smulCommClass_base :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  refine ⟨?_⟩
  intro ds k x
  change TensorProduct.Algebra.moduleAux _ _ =
    _ • TensorProduct.Algebra.moduleAux _ _
  simp

/-- A division algebra is simple as a module over `D ⊗[K] Sᵐᵒᵖ`: left multiplication alone
already moves any nonzero vector to every other vector. -/
theorem relative_isSimpleModule :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    IsSimpleModule (D ⊗[K] Sᵐᵒᵖ) D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  rw [isSimpleModule_iff]
  apply IsSimpleOrder.of_forall_eq_top
  intro P hP
  obtain ⟨y, hyP, hy⟩ : ∃ y : D, y ∈ P ∧ y ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := SetLike.exists_of_lt
      (bot_lt_iff_ne_bot.mpr hP : ⊥ < P)
    exact ⟨y, hy, by simpa using hy0⟩
  apply top_unique
  intro x hx
  have hmem := P.smul_mem ((x * y⁻¹) ⊗ₜ[K] MulOpposite.op (1 : S)) hyP
  simpa [TensorProduct.Algebra.smul_def, hy] using hmem

/-- The relative enveloping algebra embeds in the full enveloping algebra. -/
def relativeEnvelopeInclusion :
    (D ⊗[K] Sᵐᵒᵖ) →ₐ[K] (D ⊗[K] Dᵐᵒᵖ) :=
  Algebra.TensorProduct.map (AlgHom.id K D) (Subalgebra.val S).op

@[simp] theorem relativeEnvelopeInclusion_tmul (d : D) (s : Sᵐᵒᵖ) :
    relativeEnvelopeInclusion K D S (d ⊗ₜ[K] s) =
      d ⊗ₜ[K] MulOpposite.op (s.unop : D) := rfl

/-- Tensoring an injective subfield inclusion over a field remains injective. -/
theorem relativeEnvelopeInclusion_injective :
    Function.Injective (relativeEnvelopeInclusion K D S) := by
  change Function.Injective
    (LinearMap.lTensor D (Subalgebra.val S).op.toLinearMap)
  apply Module.Flat.lTensor_preserves_injective_linearMap
  intro x y hxy
  apply MulOpposite.unop_injective
  apply Subtype.ext
  exact congrArg MulOpposite.unop hxy

/-- Evaluation at `1` sends a relative bimodule endomorphism into `C_D(S)`. -/
def relativeEndToCentralizer :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    Module.End (D ⊗[K] Sᵐᵒᵖ) D →ₗ[K]
      Subalgebra.centralizer K (S : Set D) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  refine
    { toFun := fun f => ⟨f 1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · rw [Subalgebra.mem_centralizer_iff]
    intro s hs
    let sS : S := ⟨s, hs⟩
    have hleft := f.map_smul (s ⊗ₜ[K] MulOpposite.op (1 : S)) (1 : D)
    have hright := f.map_smul ((1 : D) ⊗ₜ[K] MulOpposite.op sS) (1 : D)
    simp only [TensorProduct.Algebra.smul_def, one_smul] at hright
    change f ((1 : D) * (sS : D)) = f 1 * (sS : D) at hright
    calc
      s * f 1 = f s := by
        simpa [TensorProduct.Algebra.smul_def] using hleft.symm
      _ = f 1 * s := by
        simpa [sS] using hright
  · intro f g
    apply Subtype.ext
    simp
  · intro k f
    apply Subtype.ext
    simp

theorem relativeEndToCentralizer_injective :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    Function.Injective (relativeEndToCentralizer K D S) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  intro f g hfg
  have hfg1 : f 1 = g 1 := congrArg Subtype.val hfg
  ext x
  have hf := f.map_smul (x ⊗ₜ[K] MulOpposite.op (1 : S)) (1 : D)
  have hg := g.map_smul (x ⊗ₜ[K] MulOpposite.op (1 : S)) (1 : D)
  calc
    f x = x * f 1 := by
      simpa [TensorProduct.Algebra.smul_def] using hf
    _ = x * g 1 := by rw [hfg1]
    _ = g x := by
      simpa [TensorProduct.Algebra.smul_def] using hg.symm

theorem relativeEndToCentralizer_surjective :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    Function.Surjective (relativeEndToCentralizer K D S) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  intro c
  let f : Module.End (D ⊗[K] Sᵐᵒᵖ) D :=
    { toFun := fun x => x * (c : D)
      map_add' := fun x y => add_mul x y c
      map_smul' := fun r x => by
        induction r using TensorProduct.induction_on with
        | zero =>
            change TensorProduct.Algebra.moduleAux (0 : D ⊗[K] Sᵐᵒᵖ) x * (c : D) =
              TensorProduct.Algebra.moduleAux (0 : D ⊗[K] Sᵐᵒᵖ) (x * (c : D))
            simp
        | tmul d s =>
            have hsc : (s.unop : D) * (c : D) = (c : D) * (s.unop : D) :=
              c.property (s.unop : D) s.unop.property
            simp only [TensorProduct.Algebra.smul_def]
            change (d * (x * (s.unop : D))) * (c : D) =
              d * ((x * (c : D)) * (s.unop : D))
            calc
              (d * (x * (s.unop : D))) * (c : D) =
                  d * (x * ((s.unop : D) * (c : D))) := by simp [mul_assoc]
              _ = d * (x * ((c : D) * (s.unop : D))) := by rw [hsc]
              _ = d * ((x * (c : D)) * (s.unop : D)) := by rw [mul_assoc]
        | add r t hr ht =>
            simp only [RingHom.id_apply] at hr ht ⊢
            rw [add_smul, add_smul, add_mul, hr, ht] }
  refine ⟨f, ?_⟩
  apply Subtype.ext
  simp [relativeEndToCentralizer, f]

/-- The relative bimodule endomorphism space is the centralizer as a `K`-vector space. -/
noncomputable def relativeEndCentralizerLinearEquiv :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    Module.End (D ⊗[K] Sᵐᵒᵖ) D ≃ₗ[K]
      Subalgebra.centralizer K (S : Set D) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  exact LinearEquiv.ofBijective (relativeEndToCentralizer K D S)
    ⟨relativeEndToCentralizer_injective K D S,
      relativeEndToCentralizer_surjective K D S⟩

variable [Algebra.IsCentral K D]

/-- The relative left-right action, factored through the full CSA enveloping action. -/
def relativeMulLeftRight :
    (D ⊗[K] Sᵐᵒᵖ) →ₐ[K] Module.End K D :=
  (AlgHom.mulLeftRight K D).comp (relativeEnvelopeInclusion K D S)

@[simp] theorem relativeMulLeftRight_tmul_apply
    (d x : D) (s : Sᵐᵒᵖ) :
    relativeMulLeftRight K D S (d ⊗ₜ[K] s) x =
      d * x * (s.unop : D) := by
  simp [relativeMulLeftRight, AlgHom.mulLeftRight_apply]

/-- The relative action agrees with the relative enveloping module structure. -/
theorem relativeMulLeftRight_apply
    (r : D ⊗[K] Sᵐᵒᵖ) (x : D) :
    relativeMulLeftRight K D S r x =
      letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
      letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
      letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
      letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
      r • x := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  induction r using TensorProduct.induction_on with
  | zero =>
      change 0 = TensorProduct.Algebra.moduleAux (0 : D ⊗[K] Sᵐᵒᵖ) x
      simp
  | tmul d s =>
      rw [relativeMulLeftRight_tmul_apply, TensorProduct.Algebra.smul_def]
      change d * x * (s.unop : D) = d * (x * (s.unop : D))
      rw [mul_assoc]
  | add r t hr ht =>
      rw [map_add, LinearMap.add_apply, add_smul, hr, ht]

/-- Injectivity is inherited from the full CSA left-right action. -/
theorem relativeMulLeftRight_injective :
    Function.Injective (relativeMulLeftRight K D S) :=
  (mulLeftRight_bijective_of_csa (centralDivisionCSA K D)).1.comp
    (relativeEnvelopeInclusion_injective K D S)

/-- `D` is finite over its relative bimodule endomorphism division ring. -/
theorem relativeModuleEnd_moduleEnd_finite :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    Module.Finite (Module.End (D ⊗[K] Sᵐᵒᵖ) D) D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
    relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
  letI : Algebra K E := Module.End.instAlgebra K _ _
  letI : IsScalarTower K E D := Module.End.apply_isScalarTower
  exact Module.Finite.of_restrictScalars_finite K E D

/-- Relative Jacobson density is surjective. -/
theorem relativeDensity_surjective :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
    Function.Surjective (Module.toModuleEnd E (S := D ⊗[K] Sᵐᵒᵖ) D) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : IsSimpleModule (D ⊗[K] Sᵐᵒᵖ) D := relative_isSimpleModule K D S
  letI : Module.Finite (Module.End (D ⊗[K] Sᵐᵒᵖ) D) D :=
    relativeModuleEnd_moduleEnd_finite K D S
  exact Module.Finite.toModuleEnd_moduleEnd_surjective

/-- Relative Jacobson density is injective because the relative action embeds in the full CSA
enveloping action. -/
theorem relativeDensity_injective :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
    Function.Injective (Module.toModuleEnd E (S := D ⊗[K] Sᵐᵒᵖ) D) := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  dsimp only
  intro r t hrt
  apply relativeMulLeftRight_injective K D S
  ext x
  rw [relativeMulLeftRight_apply, relativeMulLeftRight_apply]
  exact LinearMap.congr_fun hrt x

/-- The relative density map as a `K`-linear map. -/
noncomputable def relativeDensityLinearMap :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
      relativeEnvelope_isScalarTower K D S
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
    letI : Algebra K E := Module.End.instAlgebra K _ _
    letI : IsScalarTower K E D := Module.End.apply_isScalarTower
    letI : SMulCommClass K E D := Module.End.apply_smulCommClass
    (D ⊗[K] Sᵐᵒᵖ) →ₗ[K] Module.End E D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
    relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
  letI : Algebra K E := Module.End.instAlgebra K _ _
  letI : IsScalarTower K E D := Module.End.apply_isScalarTower
  letI : SMulCommClass K E D := Module.End.apply_smulCommClass
  exact
    { toFun := Module.toModuleEnd E (S := D ⊗[K] Sᵐᵒᵖ) D
      map_add' := (Module.toModuleEnd E D).map_add
      map_smul' := fun k r => by
        ext x
        change (k • r) • x = k • (r • x)
        rw [smul_assoc] }

/-- Relative Jacobson density as a `K`-linear equivalence. -/
noncomputable def relativeDensityLinearEquiv :
    letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
    letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
    letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
    letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
      relativeEnvelope_isScalarTower K D S
    letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
      relativeEnvelope_smulCommClass_base K D S
    let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
    letI : Algebra K E := Module.End.instAlgebra K _ _
    letI : IsScalarTower K E D := Module.End.apply_isScalarTower
    letI : SMulCommClass K E D := Module.End.apply_smulCommClass
    (D ⊗[K] Sᵐᵒᵖ) ≃ₗ[K] Module.End E D := by
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  letI : Module (D ⊗[K] Sᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : IsScalarTower K (D ⊗[K] Sᵐᵒᵖ) D :=
    relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass (D ⊗[K] Sᵐᵒᵖ) K D :=
    relativeEnvelope_smulCommClass_base K D S
  let E := Module.End (D ⊗[K] Sᵐᵒᵖ) D
  letI : Algebra K E := Module.End.instAlgebra K _ _
  letI : IsScalarTower K E D := Module.End.apply_isScalarTower
  letI : SMulCommClass K E D := Module.End.apply_smulCommClass
  exact LinearEquiv.ofBijective (relativeDensityLinearMap K D S)
    ⟨relativeDensity_injective K D S, relativeDensity_surjective K D S⟩

/-- **Double-centralizer dimension formula.** -/
theorem subfield_finrank_mul_centralizer_finrank :
    Module.finrank K S *
        Module.finrank K (Subalgebra.centralizer K (S : Set D)) =
      Module.finrank K D := by
  classical
  letI : Module Sᵐᵒᵖ D := subalgebraMopModule K D S
  letI : IsScalarTower K Sᵐᵒᵖ D := subalgebraMopIsScalarTower K D S
  letI : SMulCommClass D Sᵐᵒᵖ D := subalgebraMopSMulCommClass K D S
  let R := D ⊗[K] Sᵐᵒᵖ
  letI : Module R D := TensorProduct.Algebra.module
  letI : IsScalarTower K R D := relativeEnvelope_isScalarTower K D S
  letI : SMulCommClass R K D := relativeEnvelope_smulCommClass_base K D S
  letI : IsSimpleModule R D := relative_isSimpleModule K D S
  let E := Module.End R D
  letI : Algebra K E := Module.End.instAlgebra K _ _
  letI : IsScalarTower K E D := Module.End.apply_isScalarTower
  letI : SMulCommClass K E D := Module.End.apply_smulCommClass
  letI : DivisionRing E := Module.End.instDivisionRing
  letI : Module.Finite E D := relativeModuleEnd_moduleEnd_finite K D S
  letI : Module.Finite K E := Module.Finite.equiv
    (relativeEndCentralizerLinearEquiv K D S).symm
  have hE : Module.finrank K E =
      Module.finrank K (Subalgebra.centralizer K (S : Set D)) :=
    (relativeEndCentralizerLinearEquiv K D S).finrank_eq
  have hR : Module.finrank K R =
      Module.finrank K D * Module.finrank K S := by
    have hOp : Module.finrank K Sᵐᵒᵖ = Module.finrank K S :=
      (MulOpposite.opLinearEquiv K : S ≃ₗ[K] Sᵐᵒᵖ).finrank_eq.symm
    dsimp only [R]
    rw [Module.finrank_tensorProduct, hOp]
  have hDensity : Module.finrank K R =
      Module.finrank K (Module.End E D) :=
    (relativeDensityLinearEquiv K D S).finrank_eq
  have hEndK : Module.finrank K (Module.End E D) =
      Module.finrank E D * Module.finrank K D := by
    simpa using Module.finrank_linearMap E K D D
  have hD : Module.finrank K E * Module.finrank E D = Module.finrank K D :=
    Module.finrank_mul_finrank K E D
  have hmain : Module.finrank K D * Module.finrank K S =
      Module.finrank E D * Module.finrank K D := by
    calc
      Module.finrank K D * Module.finrank K S = Module.finrank K R := hR.symm
      _ = Module.finrank K (Module.End E D) := hDensity
      _ = Module.finrank E D * Module.finrank K D := hEndK
  have hcancel :
      Module.finrank K D * Module.finrank K S =
        Module.finrank K D * Module.finrank E D := by
    calc
      Module.finrank K D * Module.finrank K S =
          Module.finrank E D * Module.finrank K D := hmain
      _ = Module.finrank K D * Module.finrank E D := Nat.mul_comm _ _
  have hpositive : 0 < Module.finrank K D := Module.finrank_pos
  have hS : Module.finrank K S = Module.finrank E D :=
    Nat.eq_of_mul_eq_mul_left hpositive hcancel
  calc
    Module.finrank K S *
        Module.finrank K (Subalgebra.centralizer K (S : Set D)) =
        Module.finrank K (Subalgebra.centralizer K (S : Set D)) *
          Module.finrank K S := Nat.mul_comm _ _
    _ = Module.finrank K E * Module.finrank E D := by rw [← hE, hS]
    _ = Module.finrank K D := hD

omit [Field S] in
/-- A maximal commutative subfield has degree equal to the degree of the division algebra. -/
theorem maximalCommutativeSubfield_finrank_sq
    (hcommS : IsMulCommutative S) (hfieldS : IsField S)
    (hmaxS : ∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) :
    Module.finrank K S * Module.finrank K S = Module.finrank K D := by
  letI : Field S := hfieldS.toField
  have hdim := subfield_finrank_mul_centralizer_finrank K D S
  rw [maximalCommutativeSubalgebra_centralizer_eq K D S hcommS hmaxS] at hdim
  exact hdim

/-- Every nonsplit Brauer class has a central division representative with a nontrivial maximal
commutative subfield of the exact square-root dimension. -/
theorem brauerGroup_ne_split_exists_maximalCommutativeSubfield_finrank_sq
    (x : BrauerGroup K) (hx : x ≠ brauerSplitClass K) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D) (y : D)
      (S : Subalgebra K D),
      x = brauerClass (centralDivisionCSA K D) ∧
        y ∉ (⊥ : Subalgebra K D) ∧ IsSeparable K y ∧
          Algebra.adjoin K ({y} : Set D) ≤ S ∧ IsMulCommutative S ∧ IsField S ∧
            1 < Module.finrank K S ∧
              (∀ T : Subalgebra K D, S ≤ T → IsMulCommutative T → T = S) ∧
                Subalgebra.centralizer K (S : Set D) = S ∧
                  Module.finrank K S * Module.finrank K S = Module.finrank K D := by
  obtain ⟨D, hD, aD, finD, centralD, y, S, hclass, hybase, hysep, hyS,
      hcommS, hfieldS, hdegree, hmaxS, hcentralizer⟩ :=
    brauerGroup_ne_split_exists_maximalCommutativeSubfield K x hx
  have hsq := maximalCommutativeSubfield_finrank_sq K D S hcommS hfieldS hmaxS
  exact ⟨D, hD, aD, finD, centralD, y, S, hclass, hybase, hysep, hyS,
    hcommS, hfieldS, hdegree, hmaxS, hcentralizer, hsq⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
