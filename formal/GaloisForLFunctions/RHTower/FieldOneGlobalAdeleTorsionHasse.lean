/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.RHTower.FieldOneGlobalAdeleCharacterKernelQuotient

/-!
# Finite-layer Hasse exactness inside rational global adeles

For every torsion order `n`, restrict the rational global-adele class group to classes whose
descended standard additive character is killed by `n`.  Character-neutral classes inject into
this preimage, the restricted character is exact and surjective onto circle `n`-torsion, and the
corresponding quotient is that torsion target.  This is a finite-layer ABHN-shaped sequence inside
genuine adelic character theory, retaining the full `ℝ/ℤ` target outside finite layers.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The subgroup of the additive circle killed by `n`. -/
def unitAddCircleNTorsion (n : ℕ) : AddSubgroup UnitAddCircle where
  carrier := {x | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change n • x = 0 at hx
    change n • y = 0 at hy
    change n • (x + y) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change n • x = 0 at hx
    change n • (-x) = 0
    simpa using congrArg Neg.neg hx

/-- Global adele classes whose descended additive character is `n`-torsion. -/
def fieldOneGlobalAdeleClassNTorsionPreimage (n : ℕ) :
    AddSubgroup FieldOneGlobalAdeleAdditiveClassGroup :=
  (unitAddCircleNTorsion n).comap fieldOneGlobalAdeleClassCharacter

/-- Restriction of the global adelic character to its `n`-torsion preimage and target. -/
def fieldOneGlobalAdeleClassNTorsionCharacter (n : ℕ) :
    fieldOneGlobalAdeleClassNTorsionPreimage n →+ unitAddCircleNTorsion n where
  toFun x := ⟨fieldOneGlobalAdeleClassCharacter x.1, x.2⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero fieldOneGlobalAdeleClassCharacter
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add fieldOneGlobalAdeleClassCharacter x.1 y.1

/-- Include character-neutral global adele classes in every finite torsion preimage. -/
def fieldOneGlobalAdeleZeroSumToNTorsionPreimage (n : ℕ) :
    fieldOneGlobalAdeleClassCharacter.ker →+
      fieldOneGlobalAdeleClassNTorsionPreimage n where
  toFun x := ⟨x.1, by
    change n • fieldOneGlobalAdeleClassCharacter x.1 = 0
    rw [x.2, nsmul_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The zero-sum inclusion into the `n`-torsion adelic layer is injective. -/
theorem fieldOneGlobalAdeleZeroSumToNTorsionPreimage_injective (n : ℕ) :
    Function.Injective (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n) := by
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg Subtype.val hxy
  exact hval

/-- The `n`-torsion adelic character is surjective. -/
theorem fieldOneGlobalAdeleClassNTorsionCharacter_surjective (n : ℕ) :
    Function.Surjective (fieldOneGlobalAdeleClassNTorsionCharacter n) := by
  intro y
  obtain ⟨x, hx⟩ := fieldOneGlobalAdeleClassCharacter_surjective y.1
  let x' : fieldOneGlobalAdeleClassNTorsionPreimage n := ⟨x, by
    change n • fieldOneGlobalAdeleClassCharacter x = 0
    rw [hx]
    exact y.2⟩
  refine ⟨x', Subtype.ext ?_⟩
  exact hx

/-- Character-neutral classes, the `n`-torsion preimage, and circle `n`-torsion are exact. -/
theorem fieldOneGlobalAdeleClassNTorsionHasse_exact (n : ℕ) :
    Function.Exact
      (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n)
      (fieldOneGlobalAdeleClassNTorsionCharacter n) := by
  intro x
  constructor
  · intro hx
    have hchar : fieldOneGlobalAdeleClassCharacter x.1 = 0 :=
      congrArg Subtype.val hx
    exact ⟨⟨x.1, hchar⟩, Subtype.ext rfl⟩
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    have hval : y.1 = x.1 := congrArg Subtype.val hy
    change fieldOneGlobalAdeleClassCharacter x.1 = 0
    rw [← hval]
    exact y.2

/-- Full finite-layer adelic Hasse exactness for every torsion order. -/
theorem fieldOneGlobalAdeleClassNTorsionHasseSequence (n : ℕ) :
    Function.Injective (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n) ∧
      Function.Exact
        (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n)
        (fieldOneGlobalAdeleClassNTorsionCharacter n) ∧
      Function.Surjective (fieldOneGlobalAdeleClassNTorsionCharacter n) :=
  ⟨fieldOneGlobalAdeleZeroSumToNTorsionPreimage_injective n,
    fieldOneGlobalAdeleClassNTorsionHasse_exact n,
    fieldOneGlobalAdeleClassNTorsionCharacter_surjective n⟩

/-- The quotient of the `n`-torsion adelic layer by character-neutral classes is its circle
torsion target. -/
noncomputable def fieldOneGlobalAdeleClassNTorsionHasseQuotientEquiv (n : ℕ) :
    fieldOneGlobalAdeleClassNTorsionPreimage n ⧸
        (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n).range ≃+
      unitAddCircleNTorsion n := by
  have hker : (fieldOneGlobalAdeleClassNTorsionCharacter n).ker =
      (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n).range := by
    have hexact := fieldOneGlobalAdeleClassNTorsionHasse_exact n
    rw [AddMonoidHom.exact_iff] at hexact
    exact hexact
  exact (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (fieldOneGlobalAdeleClassNTorsionCharacter n)
      (fieldOneGlobalAdeleClassNTorsionCharacter_surjective n))

/-- Hasse realization criterion inside a finite torsion adelic layer. -/
theorem fieldOneGlobalAdeleClassNTorsion_character_eq_zero_iff_exists_zeroSum
    (n : ℕ) (x : fieldOneGlobalAdeleClassNTorsionPreimage n) :
    fieldOneGlobalAdeleClassNTorsionCharacter n x = 0 ↔
      ∃ y : fieldOneGlobalAdeleClassCharacter.ker,
        fieldOneGlobalAdeleZeroSumToNTorsionPreimage n y = x :=
  fieldOneGlobalAdeleClassNTorsionHasse_exact n x

end
end GaloisForLFunctions.RHTower
