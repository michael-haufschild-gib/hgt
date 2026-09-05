import Mathlib

/-!
# All-order joint cumulants for hard exclusion

This module supplies the set-partition infrastructure missing from the earlier
first/second/third factorial-cumulant files.  A hard-exclusion moment family has
arbitrary singleton means and zero moments on every set of at least two labels.
Its joint cumulant is therefore the single contribution of the discrete
partition, at every order.
-/

open scoped BigOperators

noncomputable section

namespace HTGeometry

/-- Certified moment family for mutually exclusive labelled events. -/
structure HardExclusionMomentFamily (ι : Type*) [DecidableEq ι] where
  mean : ι → ℝ
  moment : Finset ι → ℝ
  moment_singleton : ∀ i, moment {i} = mean i
  moment_nonsingleton : ∀ s, 2 ≤ s.card → moment s = 0

namespace HardExclusionMomentFamily

/-- Classical joint cumulant written by Möbius inversion on set partitions. -/
def jointCumulant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : HardExclusionMomentFamily ι) (s : Finset ι) : ℝ :=
  ∑ P : Finpartition s,
    (-1 : ℝ) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial *
      ∏ B ∈ P.parts, M.moment B

private theorem exists_large_part_of_ne_bot
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Finset ι} (P : Finpartition s) (hne : P ≠ ⊥) :
    ∃ B ∈ P.parts, 2 ≤ B.card := by
  by_contra hlarge
  push Not at hlarge
  have hsmall : ∀ B ∈ P.parts, B.card ≤ 1 := by
    intro B hB
    have hnot := hlarge B hB
    omega
  have heq : P = (⊥ : Finpartition s) := by
    ext B
    constructor
    · intro hB
      have hnonempty := P.nonempty_of_mem_parts hB
      have hcardPos : 0 < B.card := Finset.card_pos.mpr hnonempty
      have hcardLe := hsmall B hB
      have hcard : B.card = 1 := by omega
      obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hcard
      rw [Finpartition.mem_bot_iff]
      exact ⟨b, P.le hB (Finset.mem_singleton_self b), rfl⟩
    · intro hB
      rw [Finpartition.mem_bot_iff] at hB
      obtain ⟨b, hb, rfl⟩ := hB
      obtain ⟨B, hBP, hbB⟩ := P.exists_mem hb
      have hnonempty : B.Nonempty := ⟨b, hbB⟩
      have hcardPos : 0 < B.card := Finset.card_pos.mpr hnonempty
      have hcardLe := hsmall B hBP
      have hcard : B.card = 1 := by omega
      obtain ⟨c, hBc⟩ := Finset.card_eq_one.mp hcard
      have hbc : b = c := by
        rw [hBc] at hbB
        simpa using hbB
      simpa [hBc, hbc] using hBP
  exact hne heq

/-- All-order hard-exclusion law:
`κ(s)=(-1)^(|s|-1)(|s|-1)! ∏ᵢ pᵢ` for every nonempty label set. -/
theorem jointCumulant_eq_discrete
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : HardExclusionMomentFamily ι) (s : Finset ι) :
    M.jointCumulant s =
      (-1 : ℝ) ^ (s.card - 1) * (s.card - 1).factorial *
        ∏ i ∈ s, M.mean i := by
  classical
  unfold jointCumulant
  rw [Finset.sum_eq_single (⊥ : Finpartition s)]
  · rw [Finpartition.card_bot, Finpartition.parts_bot]
    simp [M.moment_singleton]
  · intro P hP hne
    obtain ⟨B, hB, hBcard⟩ := exists_large_part_of_ne_bot P hne
    have hmoment : M.moment B = 0 := M.moment_nonsingleton B hBcard
    have hprod : (∏ C ∈ P.parts, M.moment C) = 0 := by
      exact Finset.prod_eq_zero hB hmoment
    simp [hprod]
  · simp

end HardExclusionMomentFamily

end HTGeometry
