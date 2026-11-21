import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.HostThickExists

/-! Order bounds in the two-power unit quotient and Bernoulli subset weights. -/

namespace WindowedLandauTheory.RankGapBounds.LocalQuadraticParts

open Finset

abbrev Hgrp (e : ℕ) := (ZMod (4 * 2 ^ e))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * 2 ^ e))ˣ)

def hOf (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Hgrp e :=
  QuotientGroup.mk (ZMod.unitOfCoprime l hl)

def OrdersIff : Prop :=
  ∀ (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), j ≤ e →
    ((hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1))

def OrdersBound : Prop :=
  ∀ (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), 1 ≤ J → 1 < l →
    orderOf (hOf e l hl) ≤ J → (4 * 2 ^ e : ℝ) / J - 1 ≤ l

def OrdersSumSq : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ^ 2 ≤ C * J ^ 2 * Real.log (2 ^ e) / ((2 : ℝ) ^ e) ^ 2

def OrdersSumY : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ (l : ℝ) ≤ Y ∧
      ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e

noncomputable abbrev wt {α : Type*} [Fintype α] (δ : ℝ) (T : Finset α) : ℝ :=
  WindowedLandauTheory.FrobeniusOrbits.bern δ T

end WindowedLandauTheory.RankGapBounds.LocalQuadraticParts
