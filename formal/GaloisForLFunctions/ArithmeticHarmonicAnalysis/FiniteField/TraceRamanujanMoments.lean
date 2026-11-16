import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldTraceCharacters
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ramanujan moments of finite-field trace characters

The unit spectrum of a nontrivial finite-field character has one value
`q - 1` and `q - 1` copies of `-1`. Trace pullback preserves nontriviality,
so every extension field has the same moment formula with its own cardinality.
The trivial-character branch is retained explicitly.
-/

open Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- The additive character sum over the unit residues of a finite field. -/
def finiteFieldRamanujanSum (ψ : AddChar F ℂ) (g : F) : ℂ :=
  ∑ u ∈ (univ : Finset F).erase 0, ψ (u * g)

/-- The full spectrum, including the trivial character. -/
theorem finiteFieldRamanujanSum_value (ψ : AddChar F ℂ) (g : F) :
    finiteFieldRamanujanSum ψ g =
      if g = 0 ∨ ψ = 1 then (Fintype.card F : ℂ) - 1 else -1 := by
  by_cases hg : g = 0
  · subst g
    simp [finiteFieldRamanujanSum, card_erase_of_mem, Nat.cast_sub Fintype.card_pos]
  by_cases hψ : ψ = 1
  · subst ψ
    simp [finiteFieldRamanujanSum, card_erase_of_mem, Nat.cast_sub Fintype.card_pos]
  rw [if_neg (not_or.mpr ⟨hg, hψ⟩)]
  have hs : (∑ u : F, ψ (u * g)) = 0 := by
    simpa only [if_neg hg, Nat.cast_zero] using
      AddChar.sum_mulShift (ψ := ψ) g (AddChar.IsPrimitive.of_ne_one hψ)
  have hsplit := sum_erase_add (s := (univ : Finset F))
    (f := fun u => ψ (u * g)) (mem_univ 0)
  rw [hs] at hsplit
  simp only [zero_mul, AddChar.map_zero_eq_one] at hsplit
  change (∑ u ∈ (univ : Finset F).erase 0, ψ (u * g)) = -1
  linear_combination hsplit

/-- Every finite-field moment is explicit, with no nontriviality premise. -/
theorem sum_finiteFieldRamanujanSum_pow (ψ : AddChar F ℂ) (k : ℕ) :
    (∑ g : F, finiteFieldRamanujanSum ψ g ^ k) =
      if ψ = 1 then (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) ^ k
      else ((Fintype.card F : ℂ) - 1) ^ k +
        ((Fintype.card F : ℂ) - 1) * (-1) ^ k := by
  by_cases hψ : ψ = 1
  · simp [finiteFieldRamanujanSum_value, hψ]
  rw [if_neg hψ]
  have hsplit := sum_erase_add (s := (univ : Finset F))
    (f := fun g => finiteFieldRamanujanSum ψ g ^ k) (mem_univ 0)
  have he : (∑ g ∈ (univ : Finset F).erase 0, finiteFieldRamanujanSum ψ g ^ k) =
      ((Fintype.card F : ℂ) - 1) * (-1) ^ k := by
    rw [sum_congr rfl (fun g hg => by
      rw [finiteFieldRamanujanSum_value, if_neg (not_or.mpr ⟨(mem_erase.mp hg).1, hψ⟩)]),
      sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ 0),
      card_univ, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  rw [he, finiteFieldRamanujanSum_value, if_pos (Or.inl rfl)] at hsplit
  exact hsplit.symm.trans (add_comm _ _)

/-- Trace pullback of the standard prime-field character has the exact local moment formula. -/
theorem sum_traceRamanujanSum_pow (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) F] (k : ℕ) :
    (∑ g : F, finiteFieldRamanujanSum
      (finiteFieldTraceCharacter (L := F) (ZMod.stdAddChar (N := p))) g ^ k) =
      ((Fintype.card F : ℂ) - 1) ^ k +
        ((Fintype.card F : ℂ) - 1) * (-1) ^ k := by
  have hp : (ZMod.stdAddChar (N := p)) ≠ 1 := by
    simpa using (ZMod.isPrimitive_stdAddChar p) (a := 1) one_ne_zero
  rw [sum_finiteFieldRamanujanSum_pow,
    if_neg ((finiteFieldTraceCharacter_ne_one_iff _).mpr hp)]

/-- The cubic trace-character moment depends only on the extension field's cardinality. -/
theorem sum_traceRamanujanSum_cube (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) F] :
    (∑ g : F, finiteFieldRamanujanSum
      (finiteFieldTraceCharacter (L := F) (ZMod.stdAddChar (N := p))) g ^ 3) =
      (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) *
        ((Fintype.card F : ℂ) - 2) := by
  rw [sum_traceRamanujanSum_pow]
  ring

#print axioms finiteFieldRamanujanSum_value
#print axioms sum_finiteFieldRamanujanSum_pow
#print axioms sum_traceRamanujanSum_pow
#print axioms sum_traceRamanujanSum_cube

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
