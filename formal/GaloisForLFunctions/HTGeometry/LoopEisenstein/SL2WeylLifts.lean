import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2RootSplittings

/-!
# Weyl words and relative coroots in the symbol extension

The lower Weyl word `L(t) U(-t⁻¹) L(t)` is the zero-coordinate lift of
`[[0,-t⁻¹],[t,0]]`. Comparing the words at `ab` and `b` exposes precisely
the central symbol `{a,b}` and the diagonal matrix `diag(a⁻¹,a)`.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

open Matrix

noncomputable section

variable {K A : Type*} [Field K] [AddCommGroup A]

/-- The Weyl matrix associated with the lower root subgroup. -/
def sl2WeylLower (a : Kˣ) : SL2 K :=
  ⟨!![0, -((a⁻¹ : Kˣ) : K); (a : K), 0], by
    simp [Matrix.det_fin_two, Units.val_inv_eq_inv_val, a.ne_zero]⟩

theorem sl2Lower_upper_lower (a : Kˣ) :
    sl2Lower (a : K) * sl2Upper (-((a⁻¹ : Kˣ) : K)) * sl2Lower (a : K) =
      sl2WeylLower a := by
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, sl2Upper, sl2WeylLower, SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, a.ne_zero]

theorem sl2WeylLower_neg_mul (a : Kˣ) : sl2WeylLower (-a) * sl2WeylLower a = 1 := by
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Units.val_inv_eq_inv_val, a.ne_zero]

@[simp] theorem sl2WeylLower_inv (a : Kˣ) : (sl2WeylLower a)⁻¹ = sl2WeylLower (-a) := by
  calc
    (sl2WeylLower a)⁻¹ = 1 * (sl2WeylLower a)⁻¹ := by rw [one_mul]
    _ = (sl2WeylLower (-a) * sl2WeylLower a) * (sl2WeylLower a)⁻¹ := by
      rw [sl2WeylLower_neg_mul]
    _ = sl2WeylLower (-a) := by group

theorem sl2WeylLower_relative (a b : Kˣ) :
    sl2WeylLower (a * b) * sl2WeylLower (-b) = sl2Diagonal a⁻¹ := by
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2WeylLower, sl2Diagonal, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Units.val_inv_eq_inv_val, b.ne_zero, mul_comm]

@[simp] theorem kubotaUnit_weylLower (a : Kˣ) : kubotaUnit (sl2WeylLower a) = a := by
  apply Units.ext
  simp [kubotaX, sl2WeylLower, a.ne_zero]

private theorem kubotaUnit_lower_mul_upper (a : Kˣ) (s : K) :
    kubotaUnit (sl2Lower (a : K) * sl2Upper s) = a := by
  apply Units.ext
  simp [kubotaX, sl2Lower, sl2Upper, SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, a.ne_zero]

private theorem cocycle_lower_mul_upper (a : Kˣ) (s : K) :
    kubotaCocycle (sl2Lower (a : K)) (sl2Upper s) = 0 := by
  simp only [kubotaCocycle, kubotaUnit_lower_mul_upper, kubotaUnit_lower_unit,
    kubotaUnit_upper, div_eq_mul_inv, mul_inv_cancel, inv_one, mul_one,
    milnorSym2_one_left]

private theorem cocycle_lower_upper_lower (a : Kˣ) :
    kubotaCocycle (sl2Lower (a : K) * sl2Upper (-((a⁻¹ : Kˣ) : K)))
      (sl2Lower (a : K)) = 0 := by
  simp only [kubotaCocycle, sl2Lower_upper_lower, kubotaUnit_weylLower,
    kubotaUnit_lower_mul_upper, kubotaUnit_lower_unit, div_eq_mul_inv,
    mul_inv_cancel, milnorSym2_one_left]

private theorem cocycle_weylLower_neg_mul (a : Kˣ) :
    kubotaCocycle (sl2WeylLower (-a)) (sl2WeylLower a) = 0 := by
  rw [kubotaCocycle, sl2WeylLower_neg_mul, kubotaUnit_one,
    kubotaUnit_weylLower, kubotaUnit_weylLower]
  simp only [div_eq_mul_inv, one_mul, milnorSym2_inv_left, milnorSym2_inv_right, neg_neg]
  rw [milnorSym2_antisymm, milnorSym2_neg_self, neg_zero]

/-- The relative Weyl word has exactly the Milnor-symbol defect. -/
theorem kubotaCocycle_weylLower_relative (a b : Kˣ) :
    kubotaCocycle (sl2WeylLower (a * b)) (sl2WeylLower (-b)) = milnorSym2 K a b := by
  rw [kubotaCocycle, sl2WeylLower_relative, kubotaUnit_diagonal, inv_inv,
    kubotaUnit_weylLower, kubotaUnit_weylLower,
    show a / (a * b) = b⁻¹ by simp [div_eq_mul_inv, mul_comm]]
  simp only [div_eq_mul_inv, milnorSym2_mul_right, milnorSym2_inv_left,
    milnorSym2_inv_right, milnorSym2_neg_self, neg_zero, add_zero]
  exact (milnorSym2_antisymm a b).symm

namespace SL2SymbolExtension

variable (τ : MilnorKDeg K 2 →+ A)

/-- The Weyl lift with its canonical zero central coordinate. -/
def weylLower (a : Kˣ) : SL2SymbolExtension τ := sectionOf τ (sl2WeylLower a)

/-- The Weyl lift is the actual product of the three canonical root elements. -/
theorem weylLower_eq_rootWord (a : Kˣ) :
    weylLower τ a = lowerRoot τ (Multiplicative.ofAdd (a : K)) *
      upperRoot τ (Multiplicative.ofAdd (-((a⁻¹ : Kˣ) : K))) *
        lowerRoot τ (Multiplicative.ofAdd (a : K)) := by
  apply SL2SymbolExtension.ext
  · exact (sl2Lower_upper_lower a).symm
  · change 0 = (0 + 0 + τ (kubotaCocycle (sl2Lower (a : K))
        (sl2Upper (-((a⁻¹ : Kˣ) : K))))) + 0 +
      τ (kubotaCocycle (sl2Lower (a : K) * sl2Upper (-((a⁻¹ : Kˣ) : K)))
        (sl2Lower (a : K)))
    rw [cocycle_lower_mul_upper, cocycle_lower_upper_lower, map_zero]
    simp only [add_zero]

@[simp] theorem weylLower_inv (a : Kˣ) : (weylLower τ a)⁻¹ = weylLower τ (-a) := by
  apply SL2SymbolExtension.ext
  · exact sl2WeylLower_inv a
  · change -0 - τ (kubotaCocycle (sl2WeylLower a)⁻¹ (sl2WeylLower a)) = 0
    rw [sl2WeylLower_inv, cocycle_weylLower_neg_mul, map_zero, neg_zero, sub_zero]

/-- Comparing two Weyl words produces the central symbol and the finite coroot. -/
theorem weylLower_relative (a b : Kˣ) :
    weylLower τ (a * b) * (weylLower τ b)⁻¹ =
      centralEmbedding τ (Multiplicative.ofAdd (τ (milnorSym2 K a b))) *
        sectionOf τ (sl2Diagonal a⁻¹) := by
  rw [weylLower_inv]
  apply SL2SymbolExtension.ext
  · change sl2WeylLower (a * b) * sl2WeylLower (-b) = 1 * sl2Diagonal a⁻¹
    rw [one_mul, sl2WeylLower_relative]
  · change 0 + 0 + τ (kubotaCocycle (sl2WeylLower (a * b)) (sl2WeylLower (-b))) =
      τ (milnorSym2 K a b) + 0 + τ (kubotaCocycle 1 (sl2Diagonal a⁻¹))
    rw [kubotaCocycle_weylLower_relative, kubotaCocycle_one_left, map_zero,
      zero_add, zero_add, add_zero, add_zero]

end SL2SymbolExtension

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
