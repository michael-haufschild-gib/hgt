import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2SymbolExtension

/-!
# Root splittings and the torus defect

Both additive root subgroups lift to the Kubota extension. On the diagonal
torus, the zero-coordinate section has defect `-{a,b}`. The lower-root proof
uses the Steinberg relation at `s/(s+t)`, including the separate opposite-pair
case when `s+t=0`.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

open Matrix

noncomputable section

variable {K A : Type*} [Field K] [AddCommGroup A]

/-- The positive finite-root matrix. -/
def sl2Upper (s : K) : SL2 K :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The negative finite-root matrix. -/
def sl2Lower (s : K) : SL2 K :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

/-- The coroot diagonal matrix attached to a field unit. -/
def sl2Diagonal (a : Kˣ) : SL2 K :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_fin_two, Units.val_inv_eq_inv_val, a.ne_zero]⟩

@[simp] theorem sl2Upper_zero : sl2Upper (0 : K) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper]

@[simp] theorem sl2Lower_zero : sl2Lower (0 : K) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lower]

theorem sl2Upper_add (s t : K) : sl2Upper (s + t) = sl2Upper s * sl2Upper t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

theorem sl2Lower_add (s t : K) : sl2Lower (s + t) = sl2Lower s * sl2Lower t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Diagonal_mul (a b : Kˣ) :
    sl2Diagonal (a * b) = sl2Diagonal a * sl2Diagonal b := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diagonal, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

@[simp] theorem kubotaUnit_upper (s : K) : kubotaUnit (sl2Upper s) = 1 := by
  apply Units.ext
  simp [kubotaX, sl2Upper]

@[simp] theorem kubotaUnit_lower_unit (a : Kˣ) : kubotaUnit (sl2Lower (a : K)) = a := by
  apply Units.ext
  simp [kubotaX, sl2Lower, a.ne_zero]

@[simp] theorem kubotaUnit_diagonal (a : Kˣ) : kubotaUnit (sl2Diagonal a) = a⁻¹ := by
  apply Units.ext
  simp [kubotaX, sl2Diagonal]

@[simp] theorem kubotaCocycle_upper (s t : K) :
    kubotaCocycle (sl2Upper s) (sl2Upper t) = 0 := by
  simp only [kubotaCocycle, ← sl2Upper_add, kubotaUnit_upper, div_one,
    milnorSym2_one_left]

private theorem symbol_add_eq_one (a b : Kˣ) (h : (a : K) + (b : K) = 1) :
    milnorSym2 K a b = 0 := by
  have ha : (a : K) ≠ 1 := by
    intro ha
    apply b.ne_zero
    linear_combination h - ha
  have hb : b = oneSubUnit ha := by
    apply Units.ext
    change (b : K) = 1 - (a : K)
    linear_combination h
  rw [hb, milnorSym2_steinberg]

@[simp] theorem kubotaCocycle_lower (s t : K) :
    kubotaCocycle (sl2Lower s) (sl2Lower t) = 0 := by
  by_cases hs : s = 0
  · rw [hs, sl2Lower_zero, kubotaCocycle_one_left]
  by_cases ht : t = 0
  · rw [ht, sl2Lower_zero, kubotaCocycle_one_right]
  let a := Units.mk0 s hs
  let b := Units.mk0 t ht
  have ha : kubotaUnit (sl2Lower s) = a := kubotaUnit_lower_unit a
  have hb : kubotaUnit (sl2Lower t) = b := kubotaUnit_lower_unit b
  rw [kubotaCocycle, ← sl2Lower_add, ha, hb]
  by_cases hst : s + t = 0
  · have hab : b = -a := by
      apply Units.ext
      change t = -s
      linear_combination hst
    rw [hst, sl2Lower_zero, kubotaUnit_one, div_eq_mul_inv, div_eq_mul_inv,
      one_mul, one_mul, milnorSym2_inv_left, milnorSym2_inv_right,
      neg_neg, hab, milnorSym2_neg_self]
  · let c := Units.mk0 (s + t) hst
    have hc : kubotaUnit (sl2Lower (s + t)) = c := kubotaUnit_lower_unit c
    rw [hc, show c / a = (a / c)⁻¹ by simp [div_eq_mul_inv],
      show c / b = (b / c)⁻¹ by simp [div_eq_mul_inv],
      milnorSym2_inv_left, milnorSym2_inv_right, neg_neg]
    apply symbol_add_eq_one
    simp only [Units.val_div_eq_div_val]
    change s / (s + t) + t / (s + t) = 1
    rw [← add_div]
    exact div_self hst

/-- The coroot section has the inverse Milnor-symbol defect. -/
theorem kubotaCocycle_diagonal (a b : Kˣ) :
    kubotaCocycle (sl2Diagonal a) (sl2Diagonal b) = -milnorSym2 K a b := by
  rw [kubotaCocycle, ← sl2Diagonal_mul, kubotaUnit_diagonal,
    kubotaUnit_diagonal, kubotaUnit_diagonal,
    show (a * b)⁻¹ / a⁻¹ = b⁻¹ by
      simp [div_eq_mul_inv, mul_comm],
    show (a * b)⁻¹ / b⁻¹ = a⁻¹ by
      simp [div_eq_mul_inv, mul_comm],
    milnorSym2_inv_left, milnorSym2_inv_right, neg_neg, milnorSym2_antisymm]

namespace SL2SymbolExtension

variable (τ : MilnorKDeg K 2 →+ A)

/-- The upper root subgroup splits by the zero-coordinate section. -/
def upperRoot : Multiplicative K →* SL2SymbolExtension τ where
  toFun s := sectionOf τ (sl2Upper s.toAdd)
  map_one' := by
    apply SL2SymbolExtension.ext
    · exact sl2Upper_zero
    · rfl
  map_mul' s t := by
    apply SL2SymbolExtension.ext
    · exact sl2Upper_add _ _
    · change 0 = 0 + 0 + τ (kubotaCocycle (sl2Upper s.toAdd) (sl2Upper t.toAdd))
      rw [kubotaCocycle_upper, map_zero, zero_add, zero_add]

/-- The lower root subgroup splits by the zero-coordinate section. -/
def lowerRoot : Multiplicative K →* SL2SymbolExtension τ where
  toFun s := sectionOf τ (sl2Lower s.toAdd)
  map_one' := by
    apply SL2SymbolExtension.ext
    · exact sl2Lower_zero
    · rfl
  map_mul' s t := by
    apply SL2SymbolExtension.ext
    · exact sl2Lower_add _ _
    · change 0 = 0 + 0 + τ (kubotaCocycle (sl2Lower s.toAdd) (sl2Lower t.toAdd))
      rw [kubotaCocycle_lower, map_zero, zero_add, zero_add]

theorem upperRoot_injective : Function.Injective (upperRoot τ) := by
  intro s t h
  exact Multiplicative.toAdd.injective
    (congrArg (fun g : SL2SymbolExtension τ => g.base 0 1) h)

theorem lowerRoot_injective : Function.Injective (lowerRoot τ) := by
  intro s t h
  exact Multiplicative.toAdd.injective
    (congrArg (fun g : SL2SymbolExtension τ => g.base 1 0) h)

/-- The diagonal section's product records the central symbol exactly. -/
theorem diagonal_section_mul (a b : Kˣ) :
    sectionOf τ (sl2Diagonal a) * sectionOf τ (sl2Diagonal b) =
      centralEmbedding τ (Multiplicative.ofAdd (-τ (milnorSym2 K a b))) *
        sectionOf τ (sl2Diagonal (a * b)) := by
  apply SL2SymbolExtension.ext
  · change sl2Diagonal a * sl2Diagonal b = 1 * sl2Diagonal (a * b)
    rw [one_mul, sl2Diagonal_mul]
  · change 0 + 0 + τ (kubotaCocycle (sl2Diagonal a) (sl2Diagonal b)) =
      -τ (milnorSym2 K a b) + 0 + τ (kubotaCocycle 1 (sl2Diagonal (a * b)))
    rw [kubotaCocycle_diagonal, map_neg, kubotaCocycle_one_left, map_zero,
      zero_add, zero_add, add_zero, add_zero]

/-- The torus commutator is twice the inverse symbol, as required by the
rank-one coroot pairing. -/
theorem diagonal_section_commutator (a b : Kˣ) :
    sectionOf τ (sl2Diagonal a) * sectionOf τ (sl2Diagonal b) *
      (sectionOf τ (sl2Diagonal a))⁻¹ * (sectionOf τ (sl2Diagonal b))⁻¹ =
      centralEmbedding τ
        (Multiplicative.ofAdd (-τ (milnorSym2 K a b) - τ (milnorSym2 K a b))) := by
  have hswap : sectionOf τ (sl2Diagonal a) * sectionOf τ (sl2Diagonal b) =
      centralEmbedding τ
        (Multiplicative.ofAdd (-τ (milnorSym2 K a b) - τ (milnorSym2 K a b))) *
          (sectionOf τ (sl2Diagonal b) * sectionOf τ (sl2Diagonal a)) := by
    apply SL2SymbolExtension.ext
    · change sl2Diagonal a * sl2Diagonal b = 1 * (sl2Diagonal b * sl2Diagonal a)
      rw [one_mul, ← sl2Diagonal_mul, ← sl2Diagonal_mul, mul_comm a b]
    · change 0 + 0 + τ (kubotaCocycle (sl2Diagonal a) (sl2Diagonal b)) =
        (-τ (milnorSym2 K a b) - τ (milnorSym2 K a b)) +
          (0 + 0 + τ (kubotaCocycle (sl2Diagonal b) (sl2Diagonal a))) +
            τ (kubotaCocycle 1 (sl2Diagonal b * sl2Diagonal a))
      rw [kubotaCocycle_diagonal, kubotaCocycle_diagonal,
        milnorSym2_antisymm b a, neg_neg, map_neg, kubotaCocycle_one_left, map_zero]
      abel
  rw [hswap]
  group

end SL2SymbolExtension

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
