import GaloisForLFunctions.HTGeometry.CDGABarHead

/-!
# Hasse classification of shifted bar-degree splits

The head of a bar differential uses shifted decompositions `a + a' + 1 = c`.  Forgetting the shift
embeds these into ordinary decompositions `a + b = c`.  This file identifies the exact image:
precisely those ordinary decompositions with positive right component.  Every such local degree
packet has one unique shifted global split.

This supplies bar, Hochschild, and CDGA constructions with a reusable boundary-safe split chart;
the excluded right-zero face is now explicit rather than hidden in arithmetic side conditions.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Ordinary degree decompositions whose right component is positive. -/
abbrev PositiveBarDecomposition (c : ℕ) :=
  {ab : {ab : ℕ × ℕ // ab.1 + ab.2 = c} // 0 < ab.1.2}

/-- A shifted bar split gives an ordinary split with positive right component. -/
def barSplitPositiveEmbed {c : ℕ} (p : BarSplit c) : PositiveBarDecomposition c :=
  ⟨barSplitEmbed p, Nat.zero_lt_succ _⟩

/-- Remove the mandatory right-hand successor from a positive ordinary decomposition. -/
def positiveBarDecompositionToSplit {c : ℕ}
    (q : PositiveBarDecomposition c) : BarSplit c := by
  have hb : 0 < q.1.1.2 := q.2
  have hsum : q.1.1.1 + q.1.1.2 = c := q.1.2
  exact ⟨(q.1.1.1, q.1.1.2 - 1), by omega⟩

/-- Shifted bar splits are exactly ordinary decompositions with positive right component. -/
def barSplitPositiveEquiv (c : ℕ) : BarSplit c ≃ PositiveBarDecomposition c where
  toFun := barSplitPositiveEmbed
  invFun := positiveBarDecompositionToSplit
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp [barSplitPositiveEmbed, positiveBarDecompositionToSplit, barSplitEmbed]
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp [barSplitPositiveEmbed, positiveBarDecompositionToSplit, barSplitEmbed]
      omega

/-- Exact image criterion for the shifted bar-split embedding. -/
theorem mem_range_barSplitEmbed_iff_right_pos
    {c : ℕ} (q : {ab : ℕ × ℕ // ab.1 + ab.2 = c}) :
    q ∈ Set.range (barSplitEmbed (c := c)) ↔ 0 < q.1.2 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact Nat.zero_lt_succ _
  · intro hq
    let qpos : PositiveBarDecomposition c := ⟨q, hq⟩
    refine ⟨(barSplitPositiveEquiv c).symm qpos, ?_⟩
    exact congrArg Subtype.val ((barSplitPositiveEquiv c).apply_symm_apply qpos)

/-- Every positive ordinary degree decomposition has one unique shifted bar split. -/
theorem barSplit_hasse_existsUnique_of_right_pos
    {c : ℕ} (q : {ab : ℕ × ℕ // ab.1 + ab.2 = c}) (hq : 0 < q.1.2) :
    ∃! p : BarSplit c, barSplitEmbed p = q := by
  obtain ⟨p, hp⟩ := (mem_range_barSplitEmbed_iff_right_pos q).2 hq
  refine ⟨p, hp, ?_⟩
  intro r hr
  exact barSplitEmbed_injective (hr.trans hp.symm)

end GaloisForLFunctions.HTGeometry
