import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The dual coalgebra of a finite free algebra

If `A` is a commutative `R`-algebra that is finite and free as an `R`-module, then its linear dual
`A' = Hom_R(A, R)` carries a coalgebra structure dual to the multiplication of `A`:

* comultiplication `Δ' = (dualDistribEquiv)⁻¹ ∘ (multiplication)^t`, characterised by
  `⟨Δ' f, a ⊗ b⟩ = f (a * b)`;
* counit `ε' f = f 1`.

This file constructs the structure and proves the coalgebra axioms, giving
`DualCoalgebra.instCoalgebra`.  Together with the convolution algebra structure that mathlib
already puts on `A' = A →ₗ[R] R` when `A` is a coalgebra, this is the first half of **Cartier
duality**, which Section 3 of Suzuki, *Duality invariance of Faltings heights, Hodge line bundles
and global periods* (arXiv:2504.04993) uses throughout (Propositions 3.1–3.3).

mathlib has `TensorProduct.dualDistribEquiv` and the convolution algebra, but no dual coalgebra.
-/

namespace GaloisForLFunctions.HTGeometry.DualCoalgebra

open TensorProduct Module

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The comparison `A' ⊗ A' ≃ (A ⊗ A)'`. -/
noncomputable abbrev T2 : Dual R A ⊗[R] Dual R A ≃ₗ[R] Dual R (A ⊗[R] A) :=
  TensorProduct.dualDistribEquiv R A A

/-- The comparison `A' ⊗ (A' ⊗ A') ≃ (A ⊗ (A ⊗ A))'`. -/
noncomputable abbrev T3 :
    Dual R A ⊗[R] (Dual R A ⊗[R] Dual R A) ≃ₗ[R] Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr (LinearEquiv.refl R (Dual R A)) (T2 R A)) ≪≫ₗ
    TensorProduct.dualDistribEquiv R A (A ⊗[R] A)

/-- The comparison `(A' ⊗ A') ⊗ A' ≃ ((A ⊗ A) ⊗ A)'`. -/
noncomputable abbrev T3L :
    (Dual R A ⊗[R] Dual R A) ⊗[R] Dual R A ≃ₗ[R] Dual R ((A ⊗[R] A) ⊗[R] A) :=
  (TensorProduct.congr (T2 R A) (LinearEquiv.refl R (Dual R A))) ≪≫ₗ
    TensorProduct.dualDistribEquiv R (A ⊗[R] A) A

variable {R A}

theorem T2_tmul (φ ψ : Dual R A) (a b : A) :
    T2 R A (φ ⊗ₜ[R] ψ) (a ⊗ₜ[R] b) = φ a * ψ b := by
  simp [TensorProduct.dualDistrib_apply]

theorem T3_tmul (φ : Dual R A) (u : Dual R A ⊗[R] Dual R A) (a : A) (x : A ⊗[R] A) :
    T3 R A (φ ⊗ₜ[R] u) (a ⊗ₜ[R] x) = φ a * T2 R A u x := by
  simp [TensorProduct.dualDistrib_apply]

theorem T3L_tmul (u : Dual R A ⊗[R] Dual R A) (ψ : Dual R A) (x : A ⊗[R] A) (c : A) :
    T3L R A (u ⊗ₜ[R] ψ) (x ⊗ₜ[R] c) = T2 R A u x * ψ c := by
  simp [TensorProduct.dualDistrib_apply]

variable (R A)

/-- The comultiplication of the dual coalgebra, dual to the multiplication of `A`. -/
noncomputable def dualComul : Dual R A →ₗ[R] Dual R A ⊗[R] Dual R A :=
  (T2 R A).symm.toLinearMap ∘ₗ (Module.Dual.transpose (LinearMap.mul' R A))

/-- The counit of the dual coalgebra: evaluation at `1`. -/
noncomputable def dualCounit : Dual R A →ₗ[R] R := LinearMap.applyₗ (1 : A)

variable {R A}

@[simp] theorem dualCounit_apply (f : Dual R A) : dualCounit R A f = f 1 := rfl

/-- The defining property of the dual comultiplication. -/
@[simp] theorem T2_dualComul (f : Dual R A) (a b : A) :
    T2 R A (dualComul R A f) (a ⊗ₜ[R] b) = f (a * b) := by
  rw [dualComul]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl


/-! ### The coalgebra axioms -/

theorem lid_rTensor_dualCounit (u : Dual R A ⊗[R] Dual R A) (a : A) :
    (TensorProduct.lid R (Dual R A))
        (LinearMap.rTensor (Dual R A) (dualCounit R A) u) a
      = T2 R A u ((1 : A) ⊗ₜ[R] a) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, T2_tmul]
      simp [dualCounit_apply, smul_eq_mul]
  | add x y hx hy =>
      rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply]

theorem rid_lTensor_dualCounit (u : Dual R A ⊗[R] Dual R A) (a : A) :
    (TensorProduct.rid R (Dual R A))
        (LinearMap.lTensor (Dual R A) (dualCounit R A) u) a
      = T2 R A u (a ⊗ₜ[R] (1 : A)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, T2_tmul]
      simp [dualCounit_apply, smul_eq_mul, mul_comm]
  | add x y hx hy =>
      rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply]

theorem T3_assoc (v : (Dual R A ⊗[R] Dual R A) ⊗[R] Dual R A) (a b c : A) :
    T3 R A (TensorProduct.assoc R (Dual R A) (Dual R A) (Dual R A) v) (a ⊗ₜ[R] (b ⊗ₜ[R] c))
      = T3L R A v ((a ⊗ₜ[R] b) ⊗ₜ[R] c) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]
  | tmul w ψ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, LinearMap.add_apply, hx, hy,
          map_add, LinearMap.add_apply]
      | tmul φ χ =>
          rw [TensorProduct.assoc_tmul, T3_tmul, T3L_tmul, T2_tmul, T2_tmul]
          ring

theorem T3L_rTensor_dualComul (u : Dual R A ⊗[R] Dual R A) (a b c : A) :
    T3L R A (LinearMap.rTensor (Dual R A) (dualComul R A) u) ((a ⊗ₜ[R] b) ⊗ₜ[R] c)
      = T2 R A u ((a * b) ⊗ₜ[R] c) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ => rw [LinearMap.rTensor_tmul, T3L_tmul, T2_dualComul, T2_tmul]
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]

theorem T3_lTensor_dualComul (u : Dual R A ⊗[R] Dual R A) (a b c : A) :
    T3 R A (LinearMap.lTensor (Dual R A) (dualComul R A) u) (a ⊗ₜ[R] (b ⊗ₜ[R] c))
      = T2 R A u (a ⊗ₜ[R] (b * c)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ => rw [LinearMap.lTensor_tmul, T3_tmul, T2_dualComul, T2_tmul]
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]

variable (R A)

/-- **Coassociativity of the dual comultiplication.** -/
theorem dual_coassoc :
    (TensorProduct.assoc R (Dual R A) (Dual R A) (Dual R A)).toLinearMap ∘ₗ
        LinearMap.rTensor (Dual R A) (dualComul R A) ∘ₗ dualComul R A
      = LinearMap.lTensor (Dual R A) (dualComul R A) ∘ₗ dualComul R A := by
  ext f
  refine (T3 R A).injective ?_
  refine TensorProduct.ext' fun a x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
      show T3 R A ((TensorProduct.assoc R (Dual R A) (Dual R A) (Dual R A))
          (LinearMap.rTensor (Dual R A) (dualComul R A) (dualComul R A f)))
            (a ⊗ₜ[R] (b ⊗ₜ[R] c))
        = T3 R A (LinearMap.lTensor (Dual R A) (dualComul R A) (dualComul R A f))
            (a ⊗ₜ[R] (b ⊗ₜ[R] c))
      rw [T3_assoc, T3L_rTensor_dualComul, T3_lTensor_dualComul, T2_dualComul, T2_dualComul,
        mul_assoc]
  | add p q hp hq => rw [TensorProduct.tmul_add, map_add, map_add, hp, hq]

/-- **Counit axiom (left).** -/
theorem dual_rTensor_counit_comp_comul :
    LinearMap.rTensor (Dual R A) (dualCounit R A) ∘ₗ dualComul R A
      = TensorProduct.mk R R (Dual R A) 1 := by
  ext f
  refine (TensorProduct.lid R (Dual R A)).injective ?_
  refine LinearMap.ext fun a => ?_
  show (TensorProduct.lid R (Dual R A))
      (LinearMap.rTensor (Dual R A) (dualCounit R A) (dualComul R A f)) a = _
  rw [lid_rTensor_dualCounit, T2_dualComul, one_mul]
  simp

/-- **Counit axiom (right).** -/
theorem dual_lTensor_counit_comp_comul :
    LinearMap.lTensor (Dual R A) (dualCounit R A) ∘ₗ dualComul R A
      = (TensorProduct.mk R (Dual R A) R).flip 1 := by
  ext f
  refine (TensorProduct.rid R (Dual R A)).injective ?_
  refine LinearMap.ext fun a => ?_
  show (TensorProduct.rid R (Dual R A))
      (LinearMap.lTensor (Dual R A) (dualCounit R A) (dualComul R A f)) a = _
  rw [rid_lTensor_dualCounit, T2_dualComul, mul_one]
  simp


/-- **The dual coalgebra of a finite free commutative algebra.**

This is deliberately *not* a global instance: `Module.Dual R A` already carries mathlib's
convolution algebra structure whenever `A` is a coalgebra, and a global coalgebra instance on every
linear dual would perturb instance search across the corpus.  Use `letI := dualCoalgebra R A`. -/
@[reducible] noncomputable def dualCoalgebra : Coalgebra R (Dual R A) where
  comul := dualComul R A
  counit := dualCounit R A
  coassoc := dual_coassoc R A
  rTensor_counit_comp_comul := dual_rTensor_counit_comp_comul R A
  lTensor_counit_comp_comul := dual_lTensor_counit_comp_comul R A

end GaloisForLFunctions.HTGeometry.DualCoalgebra
