import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Extension memory beyond endpoint defects

Two law events can have identical kernel and cokernel types and middle objects of identical finite
size while carrying inequivalent composition memory.  The split event on `(ZMod 2)²` admits an
additive section and has zero section carry.  The cyclic event on `ZMod 4` has the same endpoints,
is exact, admits no additive section, has nonzero binary carry, and turns one closed base period
into nonzero lifted holonomy.

This is the exact finite obstruction to treating an ordered kernel--cokernel pair, or its positive
size, as a complete constitutive invariant.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Common kernel and cokernel object of both constitutive events. -/
abbrev ConstitutiveBit := ZMod 2

/-- Middle object of the nonsplit constitutive event. -/
abbrev ConstitutiveCarryMiddle := ZMod 4

/-- Middle object of the split constitutive event. -/
abbrev ConstitutiveSplitMiddle := ConstitutiveBit × ConstitutiveBit

/-! ## Split event -/

/-- Inclusion of the common kernel into the split middle object. -/
def constitutiveSplitInclusion : ConstitutiveBit →+ ConstitutiveSplitMiddle where
  toFun a := (a, 0)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Quotient of the split middle object onto the common cokernel. -/
def constitutiveSplitQuotient : ConstitutiveSplitMiddle →+ ConstitutiveBit where
  toFun x := x.2
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Canonical additive section of the split event. -/
def constitutiveSplitSection : ConstitutiveBit →+ ConstitutiveSplitMiddle where
  toFun b := (0, b)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem constitutiveSplitQuotient_splitInclusion (a : ConstitutiveBit) :
    constitutiveSplitQuotient (constitutiveSplitInclusion a) = 0 := rfl

@[simp] theorem constitutiveSplitQuotient_splitSection (b : ConstitutiveBit) :
    constitutiveSplitQuotient (constitutiveSplitSection b) = b := rfl

/-- The split kernel inclusion is injective. -/
theorem constitutiveSplitInclusion_injective :
    Function.Injective constitutiveSplitInclusion := by
  intro a b h
  exact congrArg Prod.fst h

/-- The split quotient is surjective. -/
theorem constitutiveSplitQuotient_surjective :
    Function.Surjective constitutiveSplitQuotient :=
  fun b ↦ ⟨constitutiveSplitSection b, rfl⟩

/-- Exactness of the split event, stated pointwise. -/
theorem constitutiveSplitQuotient_eq_zero_iff (x : ConstitutiveSplitMiddle) :
    constitutiveSplitQuotient x = 0 ↔
      ∃ a : ConstitutiveBit, constitutiveSplitInclusion a = x := by
  constructor
  · intro hx
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · change (0 : ConstitutiveBit) = x.2
      exact hx.symm
  · rintro ⟨a, rfl⟩
    rfl

/-- The split event has an additive right section. -/
theorem constitutiveSplit_has_additiveSection :
    ∃ s : ConstitutiveBit →+ ConstitutiveSplitMiddle,
      constitutiveSplitQuotient.comp s = AddMonoidHom.id ConstitutiveBit := by
  refine ⟨constitutiveSplitSection, ?_⟩
  ext b
  rfl

/-- Additivity makes every canonical section carry in the split event vanish. -/
theorem constitutiveSplitCarry_eq_zero (a b : ConstitutiveBit) :
    constitutiveSplitSection a + constitutiveSplitSection b -
        constitutiveSplitSection (a + b) = constitutiveSplitInclusion 0 := by
  change (0, a) + (0, b) - (0, a + b) = (0, 0)
  ext <;> simp

/-! ## Nonsplit event -/

/-- Quotient `ZMod 4 → ZMod 2`. -/
def constitutiveCarryQuotient : ConstitutiveCarryMiddle →+ ConstitutiveBit :=
  (ZMod.castHom (by omega : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

/-- Inclusion `ZMod 2 → ZMod 4`, sending the generator to `2`. -/
def constitutiveCarryInclusion : ConstitutiveBit →+ ConstitutiveCarryMiddle :=
  ZMod.lift 2 ⟨
    (Int.castAddHom (ZMod 4)) + (Int.castAddHom (ZMod 4)),
    by
      norm_num
      exact ZMod.natCast_self 4⟩

/-- Canonical binary-digit set section of the nonsplit quotient. -/
def constitutiveCarrySection (a : ConstitutiveBit) : ConstitutiveCarryMiddle :=
  (a.val : ZMod 4)

@[simp] theorem constitutiveCarryQuotient_natCast (n : ℕ) :
    constitutiveCarryQuotient (n : ConstitutiveCarryMiddle) = (n : ConstitutiveBit) := by
  simp [constitutiveCarryQuotient]

@[simp] theorem constitutiveCarryQuotient_eq_val (x : ConstitutiveCarryMiddle) :
    constitutiveCarryQuotient x = (x.val : ConstitutiveBit) := by
  change (ZMod.cast x : ConstitutiveBit) = (x.val : ConstitutiveBit)
  exact ZMod.cast_eq_val x

@[simp] theorem constitutiveCarryInclusion_zero : constitutiveCarryInclusion 0 = 0 := by
  simp

@[simp] theorem constitutiveCarryInclusion_intCast (m : ℤ) :
    constitutiveCarryInclusion (m : ConstitutiveBit) =
      ((2 * m : ℤ) : ConstitutiveCarryMiddle) := by
  rw [constitutiveCarryInclusion, ZMod.lift_coe]
  change (m : ConstitutiveCarryMiddle) + (m : ConstitutiveCarryMiddle) =
    ((2 * m : ℤ) : ConstitutiveCarryMiddle)
  rw [Int.cast_mul, Int.cast_ofNat]
  exact (two_mul (m : ConstitutiveCarryMiddle)).symm

@[simp] theorem constitutiveCarryInclusion_one : constitutiveCarryInclusion 1 = 2 := by
  simpa using constitutiveCarryInclusion_intCast 1

@[simp] theorem constitutiveCarryQuotient_section (a : ConstitutiveBit) :
    constitutiveCarryQuotient (constitutiveCarrySection a) = a := by
  rw [constitutiveCarrySection, constitutiveCarryQuotient_natCast, ZMod.natCast_zmod_val]

/-- The nonsplit kernel inclusion is injective. -/
theorem constitutiveCarryInclusion_injective :
    Function.Injective constitutiveCarryInclusion := by
  change Function.Injective (ZMod.lift 2 _)
  rw [ZMod.lift_injective]
  intro m hm
  change (m : ZMod 4) + (m : ZMod 4) = 0 at hm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd m 2).2
  have hm' : ((2 * m : ℤ) : ZMod 4) = 0 := by
    simpa [two_mul, Int.cast_add] using hm
  have hmdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * m) 4).1 hm'
  omega

/-- The nonsplit quotient is surjective. -/
theorem constitutiveCarryQuotient_surjective :
    Function.Surjective constitutiveCarryQuotient :=
  fun a ↦ ⟨constitutiveCarrySection a, constitutiveCarryQuotient_section a⟩

/-- Exactness of the nonsplit event, stated pointwise. -/
theorem constitutiveCarryQuotient_eq_zero_iff (x : ConstitutiveCarryMiddle) :
    constitutiveCarryQuotient x = 0 ↔
      ∃ a : ConstitutiveBit, constitutiveCarryInclusion a = x := by
  constructor
  · intro hx
    have hmod : x.val % 2 = 0 := by
      have hx' : (x.val : ConstitutiveBit) = 0 := by
        simpa only [constitutiveCarryQuotient_eq_val] using hx
      exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff x.val 2).1 hx')
    have hlt := ZMod.val_lt x
    have hcases : x.val = 0 ∨ x.val = 2 := by omega
    rcases hcases with hzero | htwo
    · refine ⟨0, ?_⟩
      rw [constitutiveCarryInclusion_zero]
      exact (ZMod.val_eq_zero x).mp hzero |>.symm
    · refine ⟨1, ?_⟩
      rw [constitutiveCarryInclusion_one, ← ZMod.natCast_zmod_val x, htwo]
      rfl
  · rintro ⟨a, rfl⟩
    have hlt := ZMod.val_lt a
    have hcases : a.val = 0 ∨ a.val = 1 := by omega
    rcases hcases with hzero | hone
    · have ha : a = 0 := (ZMod.val_eq_zero a).mp hzero
      subst a
      simp
    · have ha : a = 1 := (ZMod.val_eq_one (by omega) a).mp hone
      subst a
      simp

/-- No additive right section of `ZMod 4 → ZMod 2` exists. -/
theorem constitutiveCarry_no_additiveSection :
    ¬ ∃ s : ConstitutiveBit →+ ConstitutiveCarryMiddle,
      constitutiveCarryQuotient.comp s = AddMonoidHom.id ConstitutiveBit := by
  rintro ⟨s, hs⟩
  have hq : constitutiveCarryQuotient (s 1) = 1 := by
    exact DFunLike.congr_fun hs 1
  have hdouble : s 1 + s 1 = 0 := by
    calc
      s 1 + s 1 = s (1 + 1) := (s.map_add 1 1).symm
      _ = s 0 := by
        rw [show (1 : ConstitutiveBit) + 1 = 0 by
          change (2 : ConstitutiveBit) = 0
          exact ZMod.natCast_self 2]
      _ = 0 := s.map_zero
  have hmod : (s 1).val % 2 = 1 := by
    have hq' : ((s 1).val : ConstitutiveBit) = 1 := by
      simpa only [constitutiveCarryQuotient_eq_val] using hq
    exact (ZMod.natCast_eq_natCast_iff' (s 1).val 1 2).1 hq'
  have hdiv : 4 ∣ (s 1).val + (s 1).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    exact hdouble
  have hlt := ZMod.val_lt (s 1)
  omega

/-- Canonical binary carry is nonzero on the pair `(1,1)`. -/
theorem constitutiveCarry_one_one :
    constitutiveCarrySection 1 + constitutiveCarrySection 1 -
        constitutiveCarrySection (1 + 1) = constitutiveCarryInclusion 1 := by
  have hone : (1 : ConstitutiveBit) + 1 = 0 := by
    change (2 : ConstitutiveBit) = 0
    exact ZMod.natCast_self 2
  rw [hone]
  change (1 : ConstitutiveCarryMiddle) + 1 - 0 = constitutiveCarryInclusion 1
  rw [constitutiveCarryInclusion_one, sub_zero]
  rfl

/-! ## Identical size and different lifted history -/

/-- Both middle objects have four elements. -/
theorem constitutiveSplitMiddle_card : Fintype.card ConstitutiveSplitMiddle = 4 := by
  simp [ConstitutiveSplitMiddle, ConstitutiveBit]

/-- The nonsplit middle object also has four elements. -/
theorem constitutiveCarryMiddle_card : Fintype.card ConstitutiveCarryMiddle = 4 := by
  exact ZMod.card 4

/-- Common periodic base history. -/
def constitutiveBaseHistory (n : ℕ) : ConstitutiveBit := n

/-- Closed lift of the base history through the split section. -/
def constitutiveSplitHistory (n : ℕ) : ConstitutiveSplitMiddle :=
  (0, constitutiveBaseHistory n)

/-- Canonical open lift of the base history through `ZMod 4`. -/
def constitutiveCarryHistory (n : ℕ) : ConstitutiveCarryMiddle := n

/-- Base observation closes after two steps. -/
theorem constitutiveBaseHistory_period_two (n : ℕ) :
    constitutiveBaseHistory (n + 2) = constitutiveBaseHistory n := by
  change ((n + 2 : ℕ) : ConstitutiveBit) = (n : ConstitutiveBit)
  rw [Nat.cast_add]
  change (n : ConstitutiveBit) + (2 : ConstitutiveBit) = (n : ConstitutiveBit)
  rw [show (2 : ConstitutiveBit) = 0 from ZMod.natCast_self 2, add_zero]

/-- The split lift closes with the base period. -/
theorem constitutiveSplitHistory_period_two (n : ℕ) :
    constitutiveSplitHistory (n + 2) = constitutiveSplitHistory n := by
  simp [constitutiveSplitHistory, constitutiveBaseHistory_period_two]

/-- One closed base period creates the nonzero kernel increment `2` in the nonsplit lift. -/
theorem constitutiveCarryHistory_period_increment (n : ℕ) :
    constitutiveCarryHistory (n + 2) =
      constitutiveCarryHistory n + constitutiveCarryInclusion 1 := by
  change ((n + 2 : ℕ) : ConstitutiveCarryMiddle) =
    (n : ConstitutiveCarryMiddle) + constitutiveCarryInclusion 1
  rw [Nat.cast_add, constitutiveCarryInclusion_one]
  change (n : ConstitutiveCarryMiddle) + (2 : ConstitutiveCarryMiddle) =
    (n : ConstitutiveCarryMiddle) + (2 : ConstitutiveCarryMiddle)
  rfl

/-- The period increment is genuinely nonzero. -/
theorem constitutiveCarryHistory_increment_ne_zero : constitutiveCarryInclusion 1 ≠ 0 := by
  intro h
  have htwo : (2 : ZMod 4) = 0 := by simpa using h
  have hdiv : (4 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 4).mp htwo
  omega

/-- The canonical nonsplit lift closes only after two base periods. -/
theorem constitutiveCarryHistory_period_four (n : ℕ) :
    constitutiveCarryHistory (n + 4) = constitutiveCarryHistory n := by
  change ((n + 4 : ℕ) : ConstitutiveCarryMiddle) = (n : ConstitutiveCarryMiddle)
  rw [Nat.cast_add]
  change (n : ConstitutiveCarryMiddle) + (4 : ConstitutiveCarryMiddle) =
    (n : ConstitutiveCarryMiddle)
  rw [show (4 : ConstitutiveCarryMiddle) = 0 from ZMod.natCast_self 4, add_zero]

/-- **Same-defect extension-memory theorem.**  Identical endpoint types and identical middle size
do not reconstruct a law event: one exact event splits with zero carry and a closed lift, while the
other exact event is nonsplit with nonzero carry and nonzero holonomy after one observed period. -/
theorem constitutiveSameDefect_split_nonsplit_carry_holonomy :
    (∃ s : ConstitutiveBit →+ ConstitutiveSplitMiddle,
        constitutiveSplitQuotient.comp s = AddMonoidHom.id ConstitutiveBit) ∧
      (¬ ∃ s : ConstitutiveBit →+ ConstitutiveCarryMiddle,
        constitutiveCarryQuotient.comp s = AddMonoidHom.id ConstitutiveBit) ∧
      (∀ a b : ConstitutiveBit,
        constitutiveSplitSection a + constitutiveSplitSection b -
          constitutiveSplitSection (a + b) = constitutiveSplitInclusion 0) ∧
      (constitutiveCarrySection 1 + constitutiveCarrySection 1 -
        constitutiveCarrySection (1 + 1) = constitutiveCarryInclusion 1) ∧
      (∀ n : ℕ, constitutiveBaseHistory (n + 2) = constitutiveBaseHistory n) ∧
      (∀ n : ℕ, constitutiveSplitHistory (n + 2) = constitutiveSplitHistory n) ∧
      (∀ n : ℕ, constitutiveCarryHistory (n + 2) =
        constitutiveCarryHistory n + constitutiveCarryInclusion 1) ∧
      constitutiveCarryInclusion 1 ≠ 0 ∧
      (∀ n : ℕ, constitutiveCarryHistory (n + 4) = constitutiveCarryHistory n) := by
  exact ⟨constitutiveSplit_has_additiveSection, constitutiveCarry_no_additiveSection,
    constitutiveSplitCarry_eq_zero, constitutiveCarry_one_one,
    constitutiveBaseHistory_period_two, constitutiveSplitHistory_period_two,
    constitutiveCarryHistory_period_increment, constitutiveCarryHistory_increment_ne_zero,
    constitutiveCarryHistory_period_four⟩

end GaloisForLFunctions.HTGeometry
