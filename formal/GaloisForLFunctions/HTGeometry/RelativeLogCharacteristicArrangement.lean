import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Relative logarithmic characteristic arrangements

The squarefree degree-`r` translation annihilator of the generic order-`r` multiple elliptic
Gamma source has one generator for every coface of `Fin (r + 1)`.  Pulling its characteristic
boundary back through the coordinatewise exponential clock map replaces the translation
coordinate `t_j - 1` by `exp (lambda_j) - 1`.

This module computes that pullback without assuming any special-function theorem: all coface
products vanish exactly when two distinct clock coordinates are resonant.  Consequently the
logarithmic characteristic boundary is a periodic codimension-two arrangement, invariant under
every deck translation and under clock reflection.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every coface product of a point in `F^(r+1)` vanishes.  These are the point equations of the
squarefree degree-`r` Veronese ideal on `r+1` coordinates. -/
def CofaceProductsVanish {F : Type*} [Field F]
    (r : ℕ) (x : Fin (r + 1) → F) : Prop :=
  ∀ i : Fin (r + 1), ∏ j ∈ Finset.univ.erase i, x j = 0

/-- **Pair-sheet theorem.**  On `r+1` coordinates, all squarefree coface products vanish exactly
when at least two distinct coordinates vanish.  Thus the characteristic boundary of the
degree-`r` squarefree Veronese ideal is a union of codimension-two coordinate sheets. -/
theorem cofaceProductsVanish_iff_exists_pair_zero
    {F : Type*} [Field F] (r : ℕ) (x : Fin (r + 1) → F) :
    CofaceProductsVanish r x ↔
      ∃ a b : Fin (r + 1), a ≠ b ∧ x a = 0 ∧ x b = 0 := by
  constructor
  · intro h
    let i : Fin (r + 1) := ⟨0, Nat.succ_pos r⟩
    have hi := h i
    rw [Finset.prod_eq_zero_iff] at hi
    obtain ⟨a, ha, hxa⟩ := hi
    have ha' := h a
    rw [Finset.prod_eq_zero_iff] at ha'
    obtain ⟨b, hb, hxb⟩ := ha'
    exact ⟨a, b, (Finset.mem_erase.mp hb).1.symm, hxa, hxb⟩
  · rintro ⟨a, b, hab, hxa, hxb⟩ i
    by_cases hia : i = a
    · subst i
      exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩) hxb
    · exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨Ne.symm hia, Finset.mem_univ a⟩) hxa

/-- Coordinatewise exponential clock character. -/
def logarithmicClockCharacter {r : ℕ} (lambda : Fin (r + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  fun j ↦ Complex.exp (lambda j)

/-- The pullback of the squarefree Veronese characteristic boundary through the exponential
clock character. -/
def MultipleGammaLogCharacteristicBoundary
    (r : ℕ) (lambda : Fin (r + 1) → ℂ) : Prop :=
  CofaceProductsVanish r (fun j ↦ logarithmicClockCharacter lambda j - 1)

/-- **Relative logarithmic characteristic arrangement.**  A clock lies on the pulled-back
multiple-Gamma characteristic boundary exactly when two distinct clock coordinates exponentiate
to the unit translation character. -/
theorem multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair
    (r : ℕ) (lambda : Fin (r + 1) → ℂ) :
    MultipleGammaLogCharacteristicBoundary r lambda ↔
      ∃ a b : Fin (r + 1), a ≠ b ∧
        Complex.exp (lambda a) = 1 ∧ Complex.exp (lambda b) = 1 := by
  rw [MultipleGammaLogCharacteristicBoundary,
    cofaceProductsVanish_iff_exists_pair_zero]
  simp only [logarithmicClockCharacter, sub_eq_zero]

theorem exp_neg_eq_one_iff (z : ℂ) :
    Complex.exp (-z) = 1 ↔ Complex.exp z = 1 := by
  simp [Complex.exp_neg]

/-- Reflection preserves the complete logarithmic characteristic arrangement. -/
theorem multipleGammaLogCharacteristicBoundary_neg_iff
    (r : ℕ) (lambda : Fin (r + 1) → ℂ) :
    MultipleGammaLogCharacteristicBoundary r (-lambda) ↔
      MultipleGammaLogCharacteristicBoundary r lambda := by
  rw [multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair,
    multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair]
  simp only [Pi.neg_apply, exp_neg_eq_one_iff]

/-- A coordinatewise deck displacement is invisible to the algebraic translation character. -/
theorem logarithmicClockCharacter_add_deck
    {r : ℕ} (lambda deck : Fin (r + 1) → ℂ)
    (hdeck : ∀ j, Complex.exp (deck j) = 1) :
    logarithmicClockCharacter (lambda + deck) =
      logarithmicClockCharacter lambda := by
  funext j
  simp [logarithmicClockCharacter, Complex.exp_add, hdeck]

/-- **Deck blindness and positive lift law.**  Every coordinatewise logarithmic deck translation
preserves the relative characteristic boundary.  Hence an invariant which factors only through
the algebraic translation character cannot recover the deck label; an orientation-sensitive
realization must retain the logarithmic lift. -/
theorem multipleGammaLogCharacteristicBoundary_add_deck_iff
    (r : ℕ) (lambda deck : Fin (r + 1) → ℂ)
    (hdeck : ∀ j, Complex.exp (deck j) = 1) :
    MultipleGammaLogCharacteristicBoundary r (lambda + deck) ↔
      MultipleGammaLogCharacteristicBoundary r lambda := by
  rw [multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair,
    multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair]
  simp only [Pi.add_apply, Complex.exp_add, hdeck, mul_one]

end

end GaloisForLFunctions.HTGeometry
