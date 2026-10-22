import GaloisForLFunctions.ScaleSignedIncidenceCriticality.StructuralFlagReadingsCannotResolveCriticality

/-!
# The temperedness face has a unit, and it is the Ramanujan threshold

The temperedness face was stated as vacuity: a reading of the structural flags resolves criticality
of the shifted pair only if RH fails. It had no number, and unlike the other faces its number is
not `½`.

The datum is the shift `a` of `L_a(s) = ζ(s−a)ζ(s+a)` inside the window `|a| ≤ ¼` where the flag
list is consistent; the invariant is the shift magnitude `|a|`, which is the off-line depth the pair
carries; the reading is the flag list. All four flags hold throughout the window with the proofs
of `ζ` itself (`structuralFlags_eq`), so the reading is constant there
(`flagsReading_const`) and

`resolutionLimit shiftMagnitude flagsReading = ¼`  (`resolutionLimit_shiftMagnitude_flagsReading`),

attained at `a = ¼`. A method using only nonnegative Dirichlet coefficients, a nonnegative von
Mangoldt weight supported on prime powers, the functional equation and polynomial vertical growth
certifies the bound `β` on the depth exactly when `β ≥ ¼`
(`certifies_shiftMagnitude_flagsReading_iff`), and in particular cannot exclude the `¼`-shift,
where Hardy's theorem supplies zeros off the line (`not_pairZerosOnLine_quarter`).

So the unit of this face is `¼`, and `¼` is the Ramanujan threshold: it is the largest shift at
which the flag list stays consistent, and the flag that is missing from the list is exactly the
Ramanujan ceiling. The programme's recurring `½` is the depth bound of the zero side; the
temperedness face contributes a different number, fixed by a different arithmetic input, and
`theTemperednessFaceUnit` records the pair `(structural flags, ¼)`.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. The data and the unit -/

/-- The shifts inside the window where the flag list is consistent. -/
def TemperedShift : Type := {a : ℝ // |a| ≤ 1 / 4}

/-- The unit: the shift magnitude, which is the off-line depth of the pair `ζ(s−a)ζ(s+a)`. -/
def shiftMagnitude (a : TemperedShift) : ℝ := |a.1|

theorem shiftMagnitude_nonneg (a : TemperedShift) : 0 ≤ shiftMagnitude a := abs_nonneg _

theorem shiftMagnitude_le_quarter (a : TemperedShift) : shiftMagnitude a ≤ 1 / 4 := a.2

theorem bddAbove_shiftMagnitude_image (s : Set TemperedShift) :
    BddAbove (shiftMagnitude '' s) :=
  ⟨1 / 4, by rintro x ⟨a, -, rfl⟩; exact shiftMagnitude_le_quarter a⟩

/-! ### 2. The flag reading is constant on the window -/

/-- The flag list read on the window. -/
def flagsReading (a : TemperedShift) : Prop × Prop × Prop × Prop := structuralFlags a.1

/-- **The flags are blind on the whole window.** -/
theorem flagsReading_const (a b : TemperedShift) : flagsReading a = flagsReading b := by
  rw [flagsReading, flagsReading, structuralFlags_eq a.2, structuralFlags_eq b.2]

theorem shadow_flagsReading (a : TemperedShift) : shadow flagsReading a = univ :=
  Set.eq_univ_of_forall fun b => flagsReading_const b a

/-! ### 3. The unit of the face -/

/-- **The temperedness unit is `¼`.** The flag list certifies no bound on the depth of the shifted
pair below the Ramanujan threshold, and `¼` is attained. -/
theorem resolutionLimit_shiftMagnitude_flagsReading (a₀ : TemperedShift) :
    resolutionLimit shiftMagnitude flagsReading a₀ = 1 / 4 := by
  refine le_antisymm (csSup_le (shadow_image_nonempty shiftMagnitude flagsReading a₀) ?_) ?_
  · rintro x ⟨b, -, rfl⟩
    exact shiftMagnitude_le_quarter b
  · set q : TemperedShift := ⟨1 / 4, by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]⟩
      with hq
    have hmem : q ∈ shadow flagsReading a₀ := flagsReading_const q a₀
    have hval : shiftMagnitude q = 1 / 4 := by
      simp only [hq, shiftMagnitude]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    exact hval ▸ le_csSup (bddAbove_shiftMagnitude_image _) ⟨q, hmem, rfl⟩

/-- A flag-reading method certifies the bound `β` on the depth exactly when `β ≥ ¼`. -/
theorem certifies_shiftMagnitude_flagsReading_iff (a₀ : TemperedShift) {β : ℝ} :
    Certifies shiftMagnitude flagsReading a₀ β ↔ 1 / 4 ≤ β := by
  rw [certifies_iff_resolutionLimit_le (bddAbove_shiftMagnitude_image _),
    resolutionLimit_shiftMagnitude_flagsReading a₀]

/-- **The temperedness face's entry.** The pair `(structural flags, ¼)`: the reading is constant on
the consistency window, its limit for the depth is exactly the Ramanujan threshold, and the datum
attaining it is the `¼`-shift whose zeros Hardy's theorem puts off the line. -/
theorem theTemperednessFaceUnit (a₀ : TemperedShift) :
    (∀ a b : TemperedShift, flagsReading a = flagsReading b) ∧
      resolutionLimit shiftMagnitude flagsReading a₀ = 1 / 4 ∧
      ¬ PairZerosOnLine (1 / 4) :=
  ⟨flagsReading_const, resolutionLimit_shiftMagnitude_flagsReading a₀,
    not_pairZerosOnLine_quarter⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
