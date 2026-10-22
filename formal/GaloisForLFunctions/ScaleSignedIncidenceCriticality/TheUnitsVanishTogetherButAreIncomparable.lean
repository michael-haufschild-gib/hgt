import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightFaceUnitIsTheFirstOffLineHorizon

/-!
# The zero-side units vanish together but are incomparable

The field measures the same face in three units: the width, the scale datum (equivalently the
visibility frequency) and the horizon frequency. Each has its own floor, and it is natural to ask
whether one of them is the "right" one. Neither is, and this module says precisely why.

* **They vanish together.** Width zero, an empty failure set and horizon frequency zero are the same
  condition (`theUnitsVanishTogether`), so as *criteria* the three units are interchangeable: each
  one is RH for `ζ`'s configuration.
* **They are incomparable as quantities.** The depth-`¼` off-line lattice has width `¼` and horizon
  frequency `1`; the on-line lattice with a depth-`½` pair inserted at ordinate `10` has width `½`
  and horizon frequency `1/11` (`exists_incomparable_pair`). So one configuration is shallower and
  nearer, the other deeper and further, and no inequality between the units holds in either
  direction.

This is why the programme's floors must each name their unit, and why a result in one unit does not
transfer to another: `TheTwoByTwoTableOfUnits` is a table and not a chain. It also fixes the
practical rule: a mechanism should be priced in the unit built from the data it actually reads — a
divisor in the horizon unit, a certificate in the frequency unit, and only the criterion itself in
the width unit, where every bounded reading is vacuous.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The three units vanish together -/

/-- **The criteria coincide.** -/
theorem theUnitsVanishTogether (Z : TemperedZeroConfig) :
    (width Z = 0 ↔ failureApertures Z = ∅) ∧ (width Z = 0 ↔ horizonFrequency Z = 0) :=
  ⟨(failureApertures_eq_empty_iff_width_eq_zero Z).symm,
    (horizonFrequency_eq_zero_iff Z).symm⟩

/-! ### 2. The quantities are incomparable -/

/-- An off-line lattice carries an off-line zero at ordinate `0`, so its horizon frequency is `1`. -/
theorem horizonFrequency_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    horizonFrequency (offLineLattice hL hδ hδ') = 1 := by
  have hmem : (0 : ℝ) ∈ offLineHeights (offLineLattice hL hδ hδ') := by
    refine ⟨verticalLatticePoint L δ 0, Or.inl ⟨0, rfl⟩, ?_, ?_⟩
    · simp only [verticalLatticePoint]
      intro hc
      exact absurd (by linarith : δ = 0) (ne_of_gt hδ)
    · simp [verticalLatticePoint]
  refine le_antisymm ?_ ?_
  · refine Real.sSup_le ?_ (by norm_num)
    rintro x ⟨h, ⟨ρ, -, -, rfl⟩, rfl⟩
    rw [inv_le_one_iff₀]
    exact Or.inr (by linarith [abs_nonneg ρ.im])
  · have hle : ((1 : ℝ) + 0)⁻¹ ≤ horizonFrequency (offLineLattice hL hδ hδ') :=
      le_csSup (bddAbove_horizonFrequency_image _) ⟨0, hmem, rfl⟩
    simpa using hle

/-- **A pair of incomparable configurations.** One is shallower and nearer, the other deeper and
further: neither unit dominates the other. -/
theorem exists_incomparable_pair {L : ℝ} (hL : 0 < L) :
    ∃ Z W : TemperedZeroConfig,
      width Z < width W ∧ horizonFrequency W < horizonFrequency Z := by
  refine ⟨offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num),
    latticeWithPairAt hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl 10, ?_, ?_⟩
  · rw [width_offLineLattice hL (by norm_num) (by norm_num)]
    have hge := depth_le_width_latticeWithPairAt hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl 10
    linarith
  · rw [horizonFrequency_offLineLattice hL (by norm_num) (by norm_num),
      horizonFrequency_latticeWithPairAt hL (by norm_num) le_rfl 10,
      show |(10 : ℝ)| = 10 by norm_num]
    norm_num

/-! ### 3. Table, not chain -/

/-- **The units form a table, not a chain.** They vanish together, so each is a criterion; but they
are pairwise incomparable as quantities, so a floor proved in one unit says nothing in another. -/
theorem theUnitsAreATableNotAChain {L : ℝ} (hL : 0 < L) :
    (∀ Z : TemperedZeroConfig,
        (width Z = 0 ↔ failureApertures Z = ∅) ∧ (width Z = 0 ↔ horizonFrequency Z = 0)) ∧
      ∃ Z W : TemperedZeroConfig,
        width Z < width W ∧ horizonFrequency W < horizonFrequency Z :=
  ⟨theUnitsVanishTogether, exists_incomparable_pair hL⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
