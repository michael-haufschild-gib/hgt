import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Stadlmann Harman five-factor multiplicities

Proposition 2 of arXiv:2608.31126 bounds the two exceptional five-prime corrections by `4` and
`20`, giving the lower-bound constant `c₂ = 24` away from the final empty-correction regime.
This file formalizes the exact finite choice spaces used in that argument.
-/

namespace RHTower.Sieve.StadlmannHarmanMultiplicity

noncomputable section

/-- A five-element factor set with one distinguished smallest factor. -/
structure MarkedFiveFactorSet (α : Type*) [DecidableEq α] where
  factors : Finset α
  card_factors : factors.card = 5
  smallest : α
  smallest_mem : smallest ∈ factors

/-- In the first correction, `p₄` is fixed as smallest and `p₅` is one of four remaining factors. -/
abbrev firstCorrectionChoices {α : Type*} [DecidableEq α]
    (D : MarkedFiveFactorSet α) : Type _ :=
  ↥(D.factors.erase D.smallest)

/-- The first exceptional correction has exactly four combinatorial choices. -/
theorem card_firstCorrectionChoices {α : Type*} [DecidableEq α]
    (D : MarkedFiveFactorSet α) :
    Fintype.card (firstCorrectionChoices D) = 4 := by
  rw [Fintype.card_coe]
  simp [Finset.card_erase_of_mem D.smallest_mem, D.card_factors]

/-- In the second correction, choose the unordered `{p₂,p₃,p₄}` triple and one of the two
orders of `p₂,p₄` above the distinguished `p₃`; the remaining pair has forced order `p₆>p₅`. -/
abbrev secondCorrectionChoices {α : Type*} [DecidableEq α]
    (D : MarkedFiveFactorSet α) : Type _ :=
  ↥(D.factors.powersetCard 3) × Bool

/-- The second exceptional correction has exactly `choose(5,3)·2 = 20` combinatorial choices. -/
theorem card_secondCorrectionChoices {α : Type*} [DecidableEq α]
    (D : MarkedFiveFactorSet α) :
    Fintype.card (secondCorrectionChoices D) = 20 := by
  simp [secondCorrectionChoices, Fintype.card_coe, Finset.card_powersetCard,
    D.card_factors, Nat.choose]

/-- Disjoint union of the two negative-correction choice spaces. -/
abbrev combinedCorrectionChoices {α : Type*} [DecidableEq α]
    (D : MarkedFiveFactorSet α) : Type _ :=
  firstCorrectionChoices D ⊕ secondCorrectionChoices D

/-- Exact finite origin of Proposition 2's fallback constant `c₂ = 24`. -/
theorem card_combinedCorrectionChoices {α : Type*} [DecidableEq α]
    (D : MarkedFiveFactorSet α) :
    Fintype.card (combinedCorrectionChoices D) = 24 := by
  rw [Fintype.card_sum, card_firstCorrectionChoices, card_secondCorrectionChoices]

end

end RHTower.Sieve.StadlmannHarmanMultiplicity
