import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Two product readings recover an unordered pair

The products `ab` and `(a+1)(b+1)` recover both elementary symmetric
functions of `a,b`. Consequently their simultaneous collision count on
a finite set of size `N` is exactly `2N²-N`. This is exact algebra;
reduction of logarithmic phases modulo a period loses this information.
-/

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Finset

/-- The two product readings before and after translation by one. -/
def pairSignature (a b : ℕ) : ℕ × ℕ := (a * b, (a + 1) * (b + 1))

/-- The common fibres of two translated product readings are precisely permutations. -/
theorem pairSignature_eq_iff (a b c d : ℕ) :
    pairSignature a b = pairSignature c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have hp : a * b = c * d := congrArg Prod.fst h
    have hq : (a + 1) * (b + 1) = (c + 1) * (d + 1) := congrArg Prod.snd h
    have hs : a + b = c + d := by nlinarith only [hp, hq]
    have hp' : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hp
    have hs' : (a : ℤ) + b = (c : ℤ) + d := by exact_mod_cast hs
    have hz : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
      nlinarith only [hp', hs']
    rcases mul_eq_zero.mp hz with hac | had
    · have hac' : a = c := by exact_mod_cast sub_eq_zero.mp hac
      exact Or.inl ⟨hac', by omega⟩
    · have had' : a = d := by exact_mod_cast sub_eq_zero.mp had
      exact Or.inr ⟨had', by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp only [pairSignature, mul_comm]

/-- The ordered-pair fibre of a signature inside a finite set. -/
def pairFibre (A : Finset ℕ) (a b : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => pairSignature p.1 p.2 = pairSignature a b

theorem pairFibre_eq (A : Finset ℕ) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    pairFibre A a b = {(a, b), (b, a)} := by
  ext ⟨c, d⟩
  simp only [pairFibre, mem_filter, mem_product, pairSignature_eq_iff,
    mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · exact fun h => h.2
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨ha, hb⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨hb, ha⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- The repeated pair is counted once; every other fibre has two elements. -/
theorem card_pairFibre (A : Finset ℕ) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    (pairFibre A a b).card + (if a = b then 1 else 0) = 2 := by
  rw [pairFibre_eq A ha hb]
  by_cases h : a = b
  · simp [h]
  · have hp : (a, b) ≠ (b, a) := fun he => h (congrArg Prod.fst he)
    simp [h, hp]

/-- Number of simultaneous product collisions, with all four variables in `A`. -/
def mixedCollisionCount (A : Finset ℕ) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, (pairFibre A a b).card

/-- Exact mixed collision law, including the empty set. -/
theorem mixedCollisionCount_add_card (A : Finset ℕ) :
    mixedCollisionCount A + A.card = 2 * A.card ^ 2 := by
  have hf : ∀ a ∈ A, (∑ b ∈ A, (pairFibre A a b).card) + 1 = 2 * A.card := by
    intro a ha
    have h := sum_congr rfl fun b hb => card_pairFibre A ha hb
    simpa only [sum_add_distrib, sum_ite_eq, if_pos ha, sum_const,
      smul_eq_mul, mul_comm] using h
  have h := sum_congr rfl fun a ha => hf a ha
  simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one,
    mixedCollisionCount, pow_two, ← mul_assoc, mul_comm A.card 2] using h

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
