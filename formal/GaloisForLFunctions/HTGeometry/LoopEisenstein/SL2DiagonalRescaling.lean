import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2RootSplittings

/-!
# Rescaling the two root directions of SL₂

Conjugation by a general-linear diagonal rescales the upper and lower
entries inversely. The resulting injective homomorphism preserves the
diagonal torus and provides the odd-degree shift needed for the affine
simple rank-one subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {K : Type*} [Field K]

/-- Rescale the upper entry by `u` and the lower entry by `u⁻¹`. -/
def sl2Rescale (u : Kˣ) : SL2 K →* SL2 K where
  toFun g := ⟨!![g 0 0, (u : K) * g 0 1;
    ((u⁻¹ : Kˣ) : K) * g 1 0, g 1 1], by
      rw [Matrix.det_fin_two]
      change g 0 0 * g 1 1 - ((u : K) * g 0 1) * (((u⁻¹ : Kˣ) : K) * g 1 0) = 1
      have hd := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two] at hd
      have hu : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
      linear_combination hd - (g 0 1 * g 1 0) * hu⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, Units.val_inv_eq_inv_val, u.ne_zero,
        mul_add, mul_left_comm, mul_assoc]

@[simp] theorem coe_sl2Rescale (u : Kˣ) (g : SL2 K) :
    (sl2Rescale u g : Matrix (Fin 2) (Fin 2) K) =
      !![g 0 0, (u : K) * g 0 1; ((u⁻¹ : Kˣ) : K) * g 1 0, g 1 1] := rfl

theorem sl2Rescale_inverse (u : Kˣ) (g : SL2 K) : sl2Rescale u⁻¹ (sl2Rescale u g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Rescale, Units.val_inv_eq_inv_val, u.ne_zero]

theorem sl2Rescale_injective (u : Kˣ) : Function.Injective (sl2Rescale u) := by
  intro g h he
  have h' := congrArg (sl2Rescale u⁻¹) he
  rw [sl2Rescale_inverse, sl2Rescale_inverse] at h'
  exact h'

@[simp] theorem sl2Rescale_upper (u : Kˣ) (s : K) :
    sl2Rescale u (sl2Upper s) = sl2Upper ((u : K) * s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Rescale, sl2Upper]

@[simp] theorem sl2Rescale_lower (u : Kˣ) (s : K) :
    sl2Rescale u (sl2Lower s) = sl2Lower (((u⁻¹ : Kˣ) : K) * s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Rescale, sl2Lower]

@[simp] theorem sl2Rescale_diagonal (u a : Kˣ) :
    sl2Rescale u (sl2Diagonal a) = sl2Diagonal a := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Rescale, sl2Diagonal]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
