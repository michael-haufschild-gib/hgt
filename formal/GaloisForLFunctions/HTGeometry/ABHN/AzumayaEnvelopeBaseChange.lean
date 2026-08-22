import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaTensorProduct

/-!
# The enveloping algebra under scalar extension

This file upgrades the canonical enveloping-algebra base-change map to a
linear equivalence.  Its input and output are the source and target of the
left-right maps used in the Azumaya criterion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension

open scoped TensorProduct

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Ring A] [Algebra R A]

local notation "C" => S ⊗[R] A
local notation "E" => A ⊗[R] Aᵐᵒᵖ
local notation "P" => C ⊗[S] Cᵐᵒᵖ

/-- As an `R`-algebra, scalar extension commutes with forming the opposite algebra. -/
noncomputable def baseChangeOppositeAlgEquivR : S ⊗[R] Aᵐᵒᵖ ≃ₐ[R] Cᵐᵒᵖ :=
  (Algebra.TensorProduct.comm R S Aᵐᵒᵖ).trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Aᵐᵒᵖ ≃ₐ[R] Aᵐᵒᵖ)
      (AlgEquiv.toOpposite R S)).trans <|
    tensorProductOppositeAlgEquiv (K := R) (A := S) (B := A)

theorem baseChangeOppositeAlgEquivR_tmul (s : S) (a : Aᵐᵒᵖ) :
    baseChangeOppositeAlgEquivR (R := R) (S := S) (A := A) (s ⊗ₜ[R] a) =
      MulOpposite.op (s ⊗ₜ[R] a.unop) := by
  simp [baseChangeOppositeAlgEquivR, tensorProductOppositeAlgEquiv,
    tensorProductOppositeAlgHom_tmul]

/-- Scalar extension commutes with forming the opposite algebra as an `S`-algebra. -/
noncomputable def baseChangeOppositeAlgEquiv : S ⊗[R] Aᵐᵒᵖ ≃ₐ[S] Cᵐᵒᵖ where
  __ := baseChangeOppositeAlgEquivR (R := R) (S := S) (A := A)
  commutes' s := by
    change baseChangeOppositeAlgEquivR (R := R) (S := S) (A := A)
      (s ⊗ₜ[R] (1 : Aᵐᵒᵖ)) = MulOpposite.op (s ⊗ₜ[R] (1 : A))
    rw [baseChangeOppositeAlgEquivR_tmul]
    simp

theorem baseChangeOppositeAlgEquiv_tmul (s : S) (a : Aᵐᵒᵖ) :
    baseChangeOppositeAlgEquiv (R := R) (S := S) (A := A) (s ⊗ₜ[R] a) =
      MulOpposite.op (s ⊗ₜ[R] a.unop) := by
  change baseChangeOppositeAlgEquivR (R := R) (S := S) (A := A) (s ⊗ₜ[R] a) = _
  exact baseChangeOppositeAlgEquivR_tmul (R := R) (S := S) (A := A) s a

/-- The linear equivalence between scalar extension of an enveloping algebra and the enveloping
algebra of the scalar extension. -/
noncomputable def envelopeBaseChangeLinearEquiv : S ⊗[R] E ≃ₗ[S] P :=
  (Algebra.TensorProduct.assoc R R S S A Aᵐᵒᵖ).symm.toLinearEquiv.trans <|
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S C Aᵐᵒᵖ).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[S] C)
      (baseChangeOppositeAlgEquiv (R := R) (S := S) (A := A))).toLinearEquiv

theorem envelopeBaseChangeLinearEquiv_tmul (s : S) (a : A) (b : Aᵐᵒᵖ) :
    envelopeBaseChangeLinearEquiv (R := R) (S := S) (A := A) (s ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      (s • (1 ⊗ₜ[R] a)) ⊗ₜ[S] MulOpposite.op (1 ⊗ₜ[R] b.unop) := by
  simp [envelopeBaseChangeLinearEquiv, baseChangeOppositeAlgEquiv_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, TensorProduct.smul_tmul']

/-- The canonical enveloping-algebra base-change map is bijective. -/
theorem envelopeBaseChangeMap_bijective :
    Function.Bijective (envelopeBaseChangeMap (R := R) (S := S) (A := A)) := by
  let e := envelopeBaseChangeLinearEquiv (R := R) (S := S) (A := A)
  have hmap : (envelopeBaseChangeMap (R := R) (S := S) (A := A)).toLinearMap =
      e.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul s z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
      | tmul a b =>
        exact (envelopeBaseChangeMap_tmul (R := R) (S := S) (A := A) s a b).trans
          (envelopeBaseChangeLinearEquiv_tmul s a b).symm
  change Function.Bijective (envelopeBaseChangeMap (R := R) (S := S) (A := A)).toLinearMap
  rw [hmap]
  exact e.bijective

/-- Scalar extension through a tower cancels even when the right-hand algebra is
noncommutative.  Mathlib's algebra-level cancellation equivalence requires a commutative
right-hand factor; this is the corresponding closed proof for arbitrary algebras. -/
noncomputable def cancelBaseChangeNoncommutative
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    T ⊗[S] (S ⊗[R] A) ≃ₐ[T] T ⊗[R] A :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T A)
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun t t' x y ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x₁ x₂ hx₁ hx₂ =>
        rw [add_mul, TensorProduct.tmul_add, map_add, hx₁, hx₂,
          TensorProduct.tmul_add, map_add, add_mul]
      | tmul s a =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y₁ y₂ hy₁ hy₂ =>
          rw [mul_add, TensorProduct.tmul_add, map_add, hy₁, hy₂,
            TensorProduct.tmul_add, map_add, mul_add]
        | tmul s' a' =>
          simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            smul_smul, mul_comm]))

theorem cancelBaseChangeNoncommutative_tmul
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (t : T) (s : S) (a : A) :
    cancelBaseChangeNoncommutative (R := R) (S := S) (A := A) (T := T)
      (t ⊗ₜ[S] (s ⊗ₜ[R] a)) = (s • t) ⊗ₜ[R] a := by
  simp [cancelBaseChangeNoncommutative,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

/-- For a finite free faithful algebra, bijectivity of the base-changed left-right map gives an
Azumaya algebra after scalar extension. -/
theorem isAzumaya_scalarExtension_of_mulLeftRight_baseChange_bijective
    [Module.Finite R A] [Module.Free R A] [FaithfulSMul R A]
    (hbase : Function.Bijective ((AlgHom.mulLeftRight R A).toLinearMap.baseChange S)) :
    IsAzumaya S (S ⊗[R] A) := by
  let C' := S ⊗[R] A
  let f := (AlgHom.mulLeftRight R A).toLinearMap.baseChange S
  let g := LinearMap.tensorProductEnd R S A
  let h := AlgHom.mulLeftRight S C'
  let q := envelopeBaseChangeMap (R := R) (S := S) (A := A)
  have hg : Function.Bijective g :=
    tensorProductEnd_bijective_of_projective (R := R) (S := S) (M := A)
  have hcomp : Function.Bijective (h ∘ q) := by
    rw [show h ∘ q = g ∘ f from funext fun t =>
      mulLeftRight_envelopeBaseChangeMap (R := R) (S := S) (A := A) t]
    exact hg.comp hbase
  have hq : Function.Bijective q :=
    envelopeBaseChangeMap_bijective (R := R) (S := S) (A := A)
  letI : Module.FaithfullyFlat R A := faithfullyFlat_of_finite_projective_faithful
  letI : Module.FaithfullyFlat S C' := inferInstance
  letI : FaithfulSMul S C' := faithfullyFlat_faithfulSMul
  exact { bij := ⟨fun x y hxy => by
    obtain ⟨u, hu⟩ := hq.2 x
    obtain ⟨v, hv⟩ := hq.2 y
    calc
      x = q u := hu.symm
      _ = q v := congrArg q (hcomp.1 (by
        change h (q u) = h (q v)
        simpa only [hu, hv] using hxy))
      _ = y := hv,
    fun y => by
      obtain ⟨u, hu⟩ := hcomp.2 y
      exact ⟨q u, by simpa [Function.comp_apply] using hu⟩⟩ }

end GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
