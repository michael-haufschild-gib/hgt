import GaloisForLFunctions.HTGeometry.ABHN.TensorProduct
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Central simple algebras are Azumaya

This is the density-theorem bridge from the central-simple presentation used by
`BrauerGroup` to Mathlib's Azumaya presentation.  It is the algebraic input
needed to prove that central simplicity survives scalar extension and tensor
product.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open MulOpposite

universe u v

/-- A central simple algebra is simple as a bimodule over its enveloping algebra. -/
theorem isSimpleModule_tensorProduct_mop {K : Type u} [Field K] (A : CSA.{u, v} K) :
    letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
    IsSimpleModule (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := by
  letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
  rw [isSimpleModule_iff]
  apply IsSimpleOrder.of_forall_eq_top
  intro P hP
  let I : TwoSidedIdeal A.carrier := TwoSidedIdeal.mk' (P : Set A.carrier)
    P.zero_mem (fun hx hy => P.add_mem hx hy) (fun hx => P.neg_mem hx)
    (fun {x y} hy => by
      have h := P.smul_mem (x ⊗ₜ[K] MulOpposite.op (1 : A.carrier)) hy
      simpa [TensorProduct.Algebra.smul_def] using h)
    (fun {x y} hx => by
      have h := P.smul_mem ((1 : A.carrier) ⊗ₜ[K] MulOpposite.op y) hx
      simpa [TensorProduct.Algebra.smul_def] using h)
  have hI : I ≠ ⊥ := by
    intro h
    apply hP
    ext x
    have hmem : x ∈ I ↔ x ∈ P := by simp [I]
    rw [h] at hmem
    simpa using hmem.symm
  have hItop : I = ⊤ := (eq_bot_or_eq_top I).resolve_left hI
  apply top_unique
  intro x hx
  have : x ∈ I := hItop.symm ▸ trivial
  simpa [I] using this

/-- Every bimodule endomorphism of a central simple algebra is scalar. -/
theorem tensorProductMop_end_eq_scalar {K : Type u} [Field K] (A : CSA.{u, v} K) :
    letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
    ∀ f : Module.End (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier,
      ∃ k : K, ∀ x : A.carrier, f x = k • x := by
  letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
  intro f
  have hfcentral : f 1 ∈ Subalgebra.center K A.carrier := by
    rw [Subalgebra.mem_center_iff]
    intro a
    calc
      a * f 1 = (a ⊗ₜ[K] MulOpposite.op (1 : A.carrier)) • f 1 := by
        simp [TensorProduct.Algebra.smul_def]
      _ = f ((a ⊗ₜ[K] MulOpposite.op (1 : A.carrier)) • 1) := (f.map_smul _ _).symm
      _ = f a := by simp [TensorProduct.Algebra.smul_def]
      _ = f (((1 : A.carrier) ⊗ₜ[K] MulOpposite.op a) • 1) := by
        congr 1
        simp [TensorProduct.Algebra.smul_def]
      _ = ((1 : A.carrier) ⊗ₜ[K] MulOpposite.op a) • f 1 := f.map_smul _ _
      _ = f 1 * a := by simp [TensorProduct.Algebra.smul_def]
  obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp hfcentral
  refine ⟨k, ?_⟩
  intro x
  calc
    f x = f (((1 : A.carrier) ⊗ₜ[K] MulOpposite.op x) • 1) := by
      congr 1
      simp [TensorProduct.Algebra.smul_def]
    _ = ((1 : A.carrier) ⊗ₜ[K] MulOpposite.op x) • f 1 := f.map_smul _ _
    _ = f 1 * x := by simp [TensorProduct.Algebra.smul_def]
    _ = (algebraMap K A.carrier k) * x := by rw [hk]
    _ = k • x := (Algebra.smul_def k x).symm

/-- The underlying module is finite over its bimodule endomorphism ring. -/
theorem tensorProductMop_moduleEnd_finite {K : Type u} [Field K] (A : CSA.{u, v} K) :
    letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
    Module.Finite (Module.End (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier) A.carrier := by
  letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
  let E := Module.End (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier
  letI : IsScalarTower K (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := {
    smul_assoc := fun k ab a => by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  letI : SMulCommClass (A.carrier ⊗[K] A.carrierᵐᵒᵖ) K A.carrier := {
    smul_comm := fun ab k a => by
      change TensorProduct.Algebra.moduleAux _ _ = _ • TensorProduct.Algebra.moduleAux _ _
      simp }
  letI : Algebra K E := Module.End.instAlgebra K _ _
  letI : IsScalarTower K E A.carrier := Module.End.apply_isScalarTower
  exact Module.Finite.of_restrictScalars_finite K E A.carrier

/-- The regular action of the enveloping algebra agrees definitionally with `mulLeftRight`. -/
private theorem mulLeftRight_eq_toModuleEnd {K : Type u} [Field K] (A : CSA.{u, v} K)
    (r : A.carrier ⊗[K] A.carrierᵐᵒᵖ) (x : A.carrier) :
    AlgHom.mulLeftRight K A.carrier r x =
      letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
      let E := Module.End (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier
      (Module.toModuleEnd E (S := A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier r) x := by
  rfl

/-- Finite-dimensional Jacobson density makes the left-right action surjective. -/
theorem mulLeftRight_surjective_of_csa {K : Type u} [Field K] (A : CSA.{u, v} K) :
    Function.Surjective (AlgHom.mulLeftRight K A.carrier) := by
  letI : Module (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier := TensorProduct.Algebra.module
  letI : IsSimpleModule (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier :=
    isSimpleModule_tensorProduct_mop A
  letI : Module.Finite (Module.End (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier) A.carrier :=
    tensorProductMop_moduleEnd_finite A
  let E := Module.End (A.carrier ⊗[K] A.carrierᵐᵒᵖ) A.carrier
  intro f
  let f' : Module.End E A.carrier := {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun e x => by
      change f (e x) = e (f x)
      obtain ⟨k, hk⟩ := tensorProductMop_end_eq_scalar A e
      rw [hk x, hk (f x), f.map_smul] }
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective
    (R := A.carrier ⊗[K] A.carrierᵐᵒᵖ) (M := A.carrier) f'
  refine ⟨r, ?_⟩
  ext x
  change (AlgHom.mulLeftRight K A.carrier r) x = f x
  rw [mulLeftRight_eq_toModuleEnd A r x]
  exact LinearMap.congr_fun hr x

/-- The left-right action of a finite-dimensional central simple algebra is bijective. -/
theorem mulLeftRight_bijective_of_csa {K : Type u} [Field K] (A : CSA.{u, v} K) :
    Function.Bijective (AlgHom.mulLeftRight K A.carrier) := by
  refine ⟨?_, mulLeftRight_surjective_of_csa A⟩
  change Function.Injective (AlgHom.mulLeftRight K A.carrier).toLinearMap
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    (mulLeftRight_surjective_of_csa A)
  calc
    Module.finrank K (A.carrier ⊗[K] A.carrierᵐᵒᵖ) =
        Module.finrank K A.carrier * Module.finrank K A.carrierᵐᵒᵖ :=
      Module.finrank_tensorProduct
    _ = Module.finrank K A.carrier * Module.finrank K A.carrier := by
      rw [(opLinearEquiv K).finrank_eq]
    _ = Module.finrank K (Module.End K A.carrier) := by
      rw [Module.finrank_linearMap]

/-- Every finite-dimensional central simple algebra is Azumaya over its field. -/
theorem csa_isAzumaya {K : Type u} [Field K] (A : CSA.{u, v} K) :
    IsAzumaya K A.carrier where
  bij := mulLeftRight_bijective_of_csa A

/-- Over a field, an Azumaya algebra is a simple ring. -/
theorem isSimpleRing_of_isAzumaya {K : Type u} [Field K] (A : Type v) [Ring A] [Algebra K A]
    [IsAzumaya K A] : IsSimpleRing A := by
  letI : Nontrivial A := ⟨0, 1, fun h => zero_ne_one <|
    (FaithfulSMul.algebraMap_injective K A <| by simp [h])⟩
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  obtain ⟨x, hxI, hx⟩ : ∃ x : A, x ∈ I ∧ x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
    exact ⟨x, hx, by simpa using hx0⟩
  let g : K →ₗ[K] A := LinearMap.toSpanSingleton K A x
  obtain ⟨f, hf⟩ := g.exists_leftInverse_of_injective
    (by simpa [g] using LinearMap.ker_toSpanSingleton (R := K) hx)
  let h : Module.End K A := (LinearMap.toSpanSingleton K A 1).comp f
  have hxone : h x = 1 := by
    change f x • (1 : A) = 1
    rw [← LinearMap.toSpanSingleton_apply_one K A x]
    have hf' := LinearMap.congr_fun hf 1
    change f (g 1) = 1 at hf'
    rw [hf']
    simp
  obtain ⟨r, hr⟩ := IsAzumaya.bij (R := K) (A := A) |>.2 h
  have himage : ∀ r : A ⊗[K] Aᵐᵒᵖ, AlgHom.mulLeftRight K A r x ∈ I := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [AlgHom.mulLeftRight_apply]
        simpa only [mul_assoc] using
          I.mul_mem_left a (x * b.unop) (I.mul_mem_right x b.unop hxI)
    | add r s hr hs => simpa using I.add_mem hr hs
  have h_one : (1 : A) ∈ I := by
    rw [← hxone, ← hr]
    exact himage r
  exact (I.one_mem_iff).mp h_one

end GaloisForLFunctions.HTGeometry.ABHN
