import GaloisForLFunctions.HTGeometry.WittGradedPieces

/-!
# The graded product on Milnor `K`-theory

The objects of the fundamental cartesian square are graded rings, not just graded abelian groups.
This file supplies the product on Milnor `K`-theory in the presentation by symbols of a fixed
length: concatenation of symbols, descended through both relation subgroups.

The comparison with the Witt ring is multiplicative for it: the `n`-fold Pfister form of a
concatenation is the product of the two Pfister forms.

* `milnorSymbolAppend`, `milnorMul`, `milnorMul_class` : the product `K_m^M × K_n^M → K_{m+n}^M`.
* `milnorMul_one_right` : the empty symbol is a right unit.
* `pfisterList_append`, `milnorGradedMap_mul_class` : multiplicativity of the comparison map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section MilnorGradedRing

variable (F : Type*) [Field F]

/-- Concatenation of symbols, which is the product of Milnor `K`-theory. -/
def milnorSymbolAppend {m n : ℕ} (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n) :
    MilnorSymbolDeg F (m + n) :=
  ⟨s.val ++ t.val, by rw [List.length_append, s.property, t.property]⟩

@[simp]
theorem milnorSymbolAppend_val {m n : ℕ} (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n) :
    (milnorSymbolAppend F s t).val = s.val ++ t.val := rfl

/-- Left multiplication by a fixed symbol, before descending in the second variable. -/
def milnorMulRightLift (m n : ℕ) (s : MilnorSymbolDeg F m) :
    FreeAbelianGroup (MilnorSymbolDeg F n) →+ MilnorKDeg F (m + n) :=
  FreeAbelianGroup.lift fun t => milnorClassDeg F (m + n) (milnorSymbolAppend F s t)

@[simp]
theorem milnorMulRightLift_of (m n : ℕ) (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n) :
    milnorMulRightLift F m n s (FreeAbelianGroup.of t) =
      milnorClassDeg F (m + n) (milnorSymbolAppend F s t) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The relations survive a prefix**: prepending a fixed list to a multilinearity or Steinberg
relation is again a relation, at the shifted slot. -/
theorem milnorMulRightLift_ker (m n : ℕ) (s : MilnorSymbolDeg F m) :
    milnorRelSubgroupDeg F n ≤ (milnorMulRightLift F m n s).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · show milnorMulRightLift F m n s _ = 0
    rw [map_sub, map_sub, milnorMulRightLift_of, milnorMulRightLift_of, milnorMulRightLift_of,
      sub_sub, sub_eq_zero]
    exact milnorClassDeg_mul_of_eq F a b (s.val ++ l₁) l₂
      (List.append_assoc s.val l₁ ((a * b) :: l₂)).symm
      (List.append_assoc s.val l₁ (a :: l₂)).symm
      (List.append_assoc s.val l₁ (b :: l₂)).symm _ _ _
  · show milnorMulRightLift F m n s _ = 0
    rw [milnorMulRightLift_of]
    exact milnorClassDeg_steinberg_of_eq F ha (s.val ++ l₁) l₂
      (List.append_assoc s.val l₁ (a :: oneSubUnit ha :: l₂)).symm _

/-- Left multiplication by a fixed symbol. -/
def milnorMulRight (m n : ℕ) (s : MilnorSymbolDeg F m) :
    MilnorKDeg F n →+ MilnorKDeg F (m + n) :=
  QuotientAddGroup.lift _ (milnorMulRightLift F m n s) (milnorMulRightLift_ker F m n s)

@[simp]
theorem milnorMulRight_class (m n : ℕ) (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n) :
    milnorMulRight F m n s (milnorClassDeg F n t) =
      milnorClassDeg F (m + n) (milnorSymbolAppend F s t) := by
  show milnorMulRightLift F m n s (FreeAbelianGroup.of t) = _
  rw [milnorMulRightLift_of]

/-- The product on formal sums in the first variable. -/
def milnorMulLift (m n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg F m) →+ (MilnorKDeg F n →+ MilnorKDeg F (m + n)) :=
  FreeAbelianGroup.lift (milnorMulRight F m n)

/-- **The relations survive a suffix**: appending a fixed list to a multilinearity or Steinberg
relation is again a relation, at the same slot. -/
theorem milnorMulLift_ker (m n : ℕ) :
    milnorRelSubgroupDeg F m ≤ (milnorMulLift F m n).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · show milnorMulLift F m n _ = 0
    rw [map_sub, map_sub, milnorMulLift, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
    refine milnorKDeg_hom_ext F fun t => ?_
    rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, AddMonoidHom.zero_apply,
      milnorMulRight_class, milnorMulRight_class, milnorMulRight_class, sub_sub, sub_eq_zero]
    exact milnorClassDeg_mul_of_eq F a b l₁ (l₂ ++ t.val)
      (List.append_assoc l₁ ((a * b) :: l₂) t.val)
      (List.append_assoc l₁ (a :: l₂) t.val)
      (List.append_assoc l₁ (b :: l₂) t.val) _ _ _
  · show milnorMulLift F m n _ = 0
    rw [milnorMulLift, FreeAbelianGroup.lift_apply_of]
    refine milnorKDeg_hom_ext F fun t => ?_
    rw [AddMonoidHom.zero_apply, milnorMulRight_class]
    exact milnorClassDeg_steinberg_of_eq F ha l₁ (l₂ ++ t.val)
      (List.append_assoc l₁ (a :: oneSubUnit ha :: l₂) t.val) _

/-- **The product of Milnor `K`-theory**, `K_m^M(F) × K_n^M(F) → K_{m+n}^M(F)`, induced by
concatenation of symbols. -/
def milnorMul (m n : ℕ) : MilnorKDeg F m →+ (MilnorKDeg F n →+ MilnorKDeg F (m + n)) :=
  QuotientAddGroup.lift _ (milnorMulLift F m n) (milnorMulLift_ker F m n)

@[simp]
theorem milnorMul_class (m n : ℕ) (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n) :
    milnorMul F m n (milnorClassDeg F m s) (milnorClassDeg F n t) =
      milnorClassDeg F (m + n) (milnorSymbolAppend F s t) := by
  show milnorMulRight F m n s (milnorClassDeg F n t) = _
  rw [milnorMulRight_class]

/-- **The empty symbol is a right unit** for the product. -/
theorem milnorMul_one_right (n : ℕ) (s : MilnorSymbolDeg F n) :
    milnorMul F n 0 (milnorClassDeg F n s) (milnorClassDeg F 0 ⟨[], rfl⟩) =
      milnorClassDeg F n s := by
  rw [milnorMul_class]
  exact milnorClassDeg_congr F _ _ (List.append_nil _)

/-! ### Multiplicativity of the comparison with the Witt ring -/

/-- **The Pfister form of a concatenation is the product of the Pfister forms.** -/
theorem pfisterList_append : ∀ l₁ l₂ : List Fˣ,
    pfisterList F (l₁ ++ l₂) = pfisterList F l₁ * pfisterList F l₂
  | [], l₂ => by rw [List.nil_append, pfisterList_nil, one_mul]
  | a :: l, l₂ => by
    rw [List.cons_append, pfisterList_cons, pfisterList_cons, pfisterList_append l l₂, mul_assoc]

/-- **The comparison map is multiplicative**: the product of two Milnor classes goes to the product
of their Pfister forms. -/
theorem milnorGradedMap_mul_class (m n : ℕ) (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n) :
    wittGradedVal F (m + n) (milnorGradedMap F (m + n)
        (milnorMul F m n (milnorClassDeg F m s) (milnorClassDeg F n t))) =
      Ideal.Quotient.mk (fundamentalIdeal F ^ (m + n + 1))
        (pfisterList F s.val * pfisterList F t.val) := by
  rw [milnorMul_class, milnorGradedMap_class, pfisterGraded_val, milnorSymbolAppend_val,
    pfisterList_append]

end MilnorGradedRing

section AdjacentSlots

variable (F : Type*) [Field F]

/-- The class of the symbol `l₁ ++ x :: y :: l₂`, the shape in which the two-slot relations of
Milnor `K`-theory are stated. -/
def milnorPairClass (l₁ l₂ : List Fˣ) (x y : Fˣ) : MilnorKDeg F ((l₁ ++ l₂).length + 2) :=
  milnorClassDeg F _ ⟨l₁ ++ x :: y :: l₂, by rw [length_middle, length_middle]⟩

variable {F}

/-- **Multilinearity in the first of two adjacent slots.** -/
theorem milnorPairClass_mul_left (l₁ l₂ : List Fˣ) (a b y : Fˣ) :
    milnorPairClass F l₁ l₂ (a * b) y =
      milnorPairClass F l₁ l₂ a y + milnorPairClass F l₁ l₂ b y :=
  milnorClassDeg_mul_of_eq F a b l₁ (y :: l₂) rfl rfl rfl _ _ _

/-- **Multilinearity in the second of two adjacent slots.** -/
theorem milnorPairClass_mul_right (l₁ l₂ : List Fˣ) (x a b : Fˣ) :
    milnorPairClass F l₁ l₂ x (a * b) =
      milnorPairClass F l₁ l₂ x a + milnorPairClass F l₁ l₂ x b :=
  milnorClassDeg_mul_of_eq F a b (l₁ ++ [x]) l₂
    (List.append_assoc l₁ [x] ((a * b) :: l₂)).symm
    (List.append_assoc l₁ [x] (a :: l₂)).symm
    (List.append_assoc l₁ [x] (b :: l₂)).symm _ _ _

/-- **The Steinberg relation at two adjacent slots.** -/
theorem milnorPairClass_steinberg (l₁ l₂ : List Fˣ) {a : Fˣ} (ha : (a : F) ≠ 1) :
    milnorPairClass F l₁ l₂ a (oneSubUnit ha) = 0 :=
  milnorClassDeg_steinberg_of_eq F ha l₁ l₂ rfl _

/-- **A unit entry kills the class.** -/
theorem milnorPairClass_one_left (l₁ l₂ : List Fˣ) (y : Fˣ) :
    milnorPairClass F l₁ l₂ 1 y = 0 := by
  have h := milnorPairClass_mul_left l₁ l₂ (1 : Fˣ) 1 y
  rw [one_mul] at h
  have h2 : (0 : MilnorKDeg F ((l₁ ++ l₂).length + 2)) + milnorPairClass F l₁ l₂ 1 y =
      milnorPairClass F l₁ l₂ 1 y + milnorPairClass F l₁ l₂ 1 y := by
    rw [zero_add]
    exact h
  exact (add_right_cancel h2).symm

theorem milnorPairClass_one_right (l₁ l₂ : List Fˣ) (x : Fˣ) :
    milnorPairClass F l₁ l₂ x 1 = 0 := by
  have h := milnorPairClass_mul_right l₁ l₂ x (1 : Fˣ) 1
  rw [one_mul] at h
  have h2 : (0 : MilnorKDeg F ((l₁ ++ l₂).length + 2)) + milnorPairClass F l₁ l₂ x 1 =
      milnorPairClass F l₁ l₂ x 1 + milnorPairClass F l₁ l₂ x 1 := by
    rw [zero_add]
    exact h
  exact (add_right_cancel h2).symm

theorem milnorPairClass_inv_left (l₁ l₂ : List Fˣ) (a y : Fˣ) :
    milnorPairClass F l₁ l₂ a⁻¹ y = -milnorPairClass F l₁ l₂ a y := by
  have h := milnorPairClass_mul_left l₁ l₂ a a⁻¹ y
  rw [mul_inv_cancel, milnorPairClass_one_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **`{a, -a} = 0` at two adjacent slots.**  The unit identity `(-a)(1 - a⁻¹) = 1 - a` turns the
entry `-a` into a difference of two Steinberg entries, and both resulting classes vanish. -/
theorem milnorPairClass_neg_self (l₁ l₂ : List Fˣ) (a : Fˣ) :
    milnorPairClass F l₁ l₂ a (-a) = 0 := by
  by_cases ha : (a : F) = 1
  · have h1 : a = 1 := Units.ext ha
    rw [h1, milnorPairClass_one_left]
  · have hainv : ((a⁻¹ : Fˣ) : F) ≠ 1 := fun h =>
      ha (congrArg Units.val (inv_eq_one.mp (Units.ext h)))
    have hane : (a : F) ≠ 0 := a.ne_zero
    have hunit : (-a : Fˣ) * oneSubUnit hainv = oneSubUnit ha := by
      refine Units.ext ?_
      rw [Units.val_mul, oneSubUnit_val, oneSubUnit_val, Units.val_neg,
        Units.val_inv_eq_inv_val, mul_sub, mul_one, neg_mul, mul_inv_cancel₀ hane]
      ring
    have hsecond : milnorPairClass F l₁ l₂ a (oneSubUnit hainv) = 0 := by
      have h := milnorPairClass_inv_left l₁ l₂ a (oneSubUnit hainv)
      rw [milnorPairClass_steinberg l₁ l₂ hainv] at h
      exact neg_eq_zero.1 h.symm
    have hexp := milnorPairClass_mul_right l₁ l₂ a (-a) (oneSubUnit hainv)
    rw [hunit, milnorPairClass_steinberg l₁ l₂ ha, hsecond, add_zero] at hexp
    exact hexp.symm

/-- **Anticommutativity at two adjacent slots**: transposing two neighbouring entries of a Milnor
symbol negates its class. -/
theorem milnorPairClass_anticomm (l₁ l₂ : List Fˣ) (x y : Fˣ) :
    milnorPairClass F l₁ l₂ x y = -milnorPairClass F l₁ l₂ y x := by
  have hab := milnorPairClass_neg_self l₁ l₂ (x * y)
  have hnegab : (-(x * y) : Fˣ) = (-x) * y := by
    refine Units.ext ?_
    simp
  have hnegba : (-(x * y) : Fˣ) = x * (-y) := by
    refine Units.ext ?_
    simp
  rw [milnorPairClass_mul_left] at hab
  have hx : milnorPairClass F l₁ l₂ x (-(x * y)) = milnorPairClass F l₁ l₂ x y := by
    rw [hnegab, milnorPairClass_mul_right, milnorPairClass_neg_self, zero_add]
  have hy : milnorPairClass F l₁ l₂ y (-(x * y)) = milnorPairClass F l₁ l₂ y x := by
    rw [hnegba, milnorPairClass_mul_right, milnorPairClass_neg_self, add_zero]
  rw [hx, hy] at hab
  exact eq_neg_of_add_eq_zero_left hab

end AdjacentSlots

end

end GaloisForLFunctions.HTGeometry
