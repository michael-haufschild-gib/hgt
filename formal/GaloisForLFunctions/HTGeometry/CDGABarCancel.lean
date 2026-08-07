import GaloisForLFunctions.HTGeometry.CDGABarHead

/-!
# The two bracketings of three adjacent bar factors cancel

Multiplying the first two of three adjacent shifted factors and then the result with the third, and
multiplying the last two and then the first with the result, are the two ways a bar differential can
reach the same target from three factors.  Weighted by the sign the tail of the bar differential
contributes, they cancel — this is the algebraic content of `d² = 0`, isolated from the bookkeeping
of the double sum over splits.

* `HTGeometry.barMulFirstTwo`, `HTGeometry.barMulLastTwo` : the two composites.
* `HTGeometry.barMul_cancel` : they cancel.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  {W : Type u} [AddCommGroup W] [Module R W]

/-- **Multiply the first two of three adjacent shifted factors, then the result with the third.** -/
noncomputable def barMulFirstTwo {p q r m n : ℕ} (h₁ : p + q + 1 = m) (h₂ : m + r + 1 = n) :
    TensorProduct R (barShiftFamily ε p)
        (TensorProduct R (barShiftFamily ε q) (TensorProduct R (barShiftFamily ε r) W))
      →ₗ[R] TensorProduct R (barShiftFamily ε n) W :=
  (TensorProduct.map (augIdealShiftMulOfTensor ε h₂) (LinearMap.id (R := R) (M := W))).comp
    (((TensorProduct.assoc R (barShiftFamily ε m) (barShiftFamily ε r) W).symm.toLinearMap).comp
      ((TensorProduct.map (augIdealShiftMulOfTensor ε h₁)
          (LinearMap.id (R := R) (M := TensorProduct R (barShiftFamily ε r) W))).comp
        ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q)
          (TensorProduct R (barShiftFamily ε r) W)).symm.toLinearMap)))

@[simp] theorem barMulFirstTwo_tmul {p q r m n : ℕ} (h₁ : p + q + 1 = m) (h₂ : m + r + 1 = n)
    (x : barShiftFamily ε p) (y : barShiftFamily ε q) (z : barShiftFamily ε r) (t : W) :
    barMulFirstTwo ε (W := W) h₁ h₂ (x ⊗ₜ[R] (y ⊗ₜ[R] (z ⊗ₜ[R] t)))
      = augIdealShiftMulOf ε h₂ (augIdealShiftMulOf ε h₁ x y) z ⊗ₜ[R] t := rfl

/-- **Multiply the last two of three adjacent shifted factors, then the first with the result.** -/
noncomputable def barMulLastTwo {p q r m' n : ℕ} (h₃ : q + r + 1 = m') (h₄ : p + m' + 1 = n) :
    TensorProduct R (barShiftFamily ε p)
        (TensorProduct R (barShiftFamily ε q) (TensorProduct R (barShiftFamily ε r) W))
      →ₗ[R] TensorProduct R (barShiftFamily ε n) W :=
  (TensorProduct.map (augIdealShiftMulOfTensor ε h₄) (LinearMap.id (R := R) (M := W))).comp
    (((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε m') W).symm.toLinearMap).comp
      (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
        ((TensorProduct.map (augIdealShiftMulOfTensor ε h₃) (LinearMap.id (R := R) (M := W))).comp
          ((TensorProduct.assoc R (barShiftFamily ε q) (barShiftFamily ε r) W).symm.toLinearMap))))

@[simp] theorem barMulLastTwo_tmul {p q r m' n : ℕ} (h₃ : q + r + 1 = m') (h₄ : p + m' + 1 = n)
    (x : barShiftFamily ε p) (y : barShiftFamily ε q) (z : barShiftFamily ε r) (t : W) :
    barMulLastTwo ε (W := W) h₃ h₄ (x ⊗ₜ[R] (y ⊗ₜ[R] (z ⊗ₜ[R] t)))
      = augIdealShiftMulOf ε h₄ x (augIdealShiftMulOf ε h₃ y z) ⊗ₜ[R] t := rfl

/-- **The two bracketings cancel**, once the second is weighted by the sign the tail of the bar
differential contributes.  On a triple tensor this is the signed associativity of the shifted
product; the general case follows because both sides are linear. -/
theorem barMul_cancel {p q r m m' n : ℕ} (h₁ : p + q + 1 = m) (h₂ : m + r + 1 = n)
    (h₃ : q + r + 1 = m') (h₄ : p + m' + 1 = n)
    (T : TensorProduct R (barShiftFamily ε p)
      (TensorProduct R (barShiftFamily ε q) (TensorProduct R (barShiftFamily ε r) W))) :
    barMulFirstTwo ε h₁ h₂ T + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ T = 0 := by
  induction T using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero, add_zero]
  | add T T' hT hT' =>
      rw [map_add, map_add, smul_add]
      calc barMulFirstTwo ε h₁ h₂ T + barMulFirstTwo ε h₁ h₂ T'
            + (((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ T
              + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ T')
          = (barMulFirstTwo ε h₁ h₂ T + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ T)
            + (barMulFirstTwo ε h₁ h₂ T' + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ T') := by abel
        _ = 0 := by rw [hT, hT', add_zero]
  | tmul x S =>
      induction S using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero, add_zero]
      | add S S' hS hS' =>
          rw [TensorProduct.tmul_add, map_add, map_add, smul_add]
          calc barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] S) + barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] S')
                + (((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] S)
                  + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] S'))
              = (barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] S)
                  + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] S))
                + (barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] S')
                  + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] S')) := by abel
            _ = 0 := by rw [hS, hS', add_zero]
      | tmul y U =>
          induction U using TensorProduct.induction_on with
          | zero =>
              rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, map_zero, map_zero, smul_zero,
                add_zero]
          | add U U' hU hU' =>
              rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, smul_add]
              calc barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] (y ⊗ₜ[R] U))
                    + barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] (y ⊗ₜ[R] U'))
                    + (((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] (y ⊗ₜ[R] U))
                      + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] (y ⊗ₜ[R] U')))
                  = (barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] (y ⊗ₜ[R] U))
                      + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] (y ⊗ₜ[R] U)))
                    + (barMulFirstTwo ε h₁ h₂ (x ⊗ₜ[R] (y ⊗ₜ[R] U'))
                      + ((-1 : R)) ^ p • barMulLastTwo ε h₃ h₄ (x ⊗ₜ[R] (y ⊗ₜ[R] U'))) := by abel
                _ = 0 := by rw [hU, hU', add_zero]
          | tmul z t =>
              rw [barMulFirstTwo_tmul, barMulLastTwo_tmul, TensorProduct.smul_tmul',
                ← TensorProduct.add_tmul, augIdealShiftMulOf_cancel ε h₁ h₂ h₃ h₄ x y z,
                TensorProduct.zero_tmul]

end GaloisForLFunctions.HTGeometry
