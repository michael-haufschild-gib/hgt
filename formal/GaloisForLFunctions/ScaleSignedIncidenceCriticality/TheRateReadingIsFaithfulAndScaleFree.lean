import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthIsHalfTheDeficitGrowthRate
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthIsTheCompleteDilationInvariant

/-!
# The rate reading is faithful and scale-free

`TheDepthIsTheCompleteDilationInvariant` poses the question the field's floors leave open: a reading
that resolves the depth must be constant on dilation orbits and separate them, and every scale
reading of the programme fails on both counts. This module exhibits a reading that succeeds.

For a lattice datum let `rateSet p` be the set of nonnegative rates `β` at which the deficit of its
configuration is `O(e^{2βa})`. By `TheDepthIsHalfTheDeficitGrowthRate` every rate above the depth is
admissible and no nonnegative rate below it is, so

`sInf (rateSet p) = sdDepth p`   (`sInf_rateSet`).

Two consequences.

* The quantity `sInf ∘ rateSet` **equals the depth**, hence is constant on dilation orbits — it is
  scale-free, which no aperture, height, radius or ordinate reading is
  (`TheDichotomyIsAboutCoordinatesNotBoundedness`).
* It **separates the orbits**: equal rate sets force equal depths
  (`sdDepth_eq_of_rateSet_eq`), so the reading is faithful for the depth in the sense of
  `faithful_sdDepth_iff_dilationEquiv`.

`theRateReadingIsTheAnswer` states both. So the object a closing mechanism must estimate is now
named and shown to exist: not the sign of the Weil form at some aperture, not its size, but the
**exponential rate** at which its deficit grows along the aperture axis. That rate is the depth, it
carries no trace of the scale, and it is the only quantity of the field so far with both
properties.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The set of admissible rates -/

/-- The nonnegative rates at which the datum's deficit is `O(e^{2βa})`. -/
def rateSet (p : ScaleDepthDatum) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ deficitRateBelow β (offLineLattice p.2.1 p.2.2.1 p.2.2.2)}

theorem mem_rateSet_of_lt {p : ScaleDepthDatum} {β : ℝ} (hβ0 : 0 ≤ β) (hβ : sdDepth p < β) :
    β ∈ rateSet p :=
  ⟨hβ0, deficitRateBelow_of_lt p.2.1 p.2.2.1 p.2.2.2 hβ⟩

theorem notMem_rateSet_of_lt {p : ScaleDepthDatum} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β < sdDepth p) : β ∉ rateSet p := fun hmem =>
  not_deficitRateBelow_of_lt p.2.1 p.2.2.1 p.2.2.2 hβ0 hβ hmem.2

/-! ### 2. The infimum is the depth -/

/-- **The infimum of the admissible rates is the depth.** -/
theorem sInf_rateSet (p : ScaleDepthDatum) : sInf (rateSet p) = sdDepth p := by
  have hne : (rateSet p).Nonempty :=
    ⟨sdDepth p + 1, mem_rateSet_of_lt (by linarith [p.2.2.1]) (by linarith)⟩
  have hlb : ∀ β ∈ rateSet p, sdDepth p ≤ β := by
    intro β hβ
    by_contra hcon
    exact notMem_rateSet_of_lt hβ.1 (not_le.mp hcon) hβ
  refine le_antisymm ?_ (le_csInf hne hlb)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact csInf_le ⟨sdDepth p, hlb⟩
    (mem_rateSet_of_lt (by linarith [p.2.2.1]) (by linarith))

/-! ### 3. Faithful and scale-free -/

/-- **The rate reading separates the depths.** -/
theorem sdDepth_eq_of_rateSet_eq {p q : ScaleDepthDatum} (h : rateSet p = rateSet q) :
    sdDepth p = sdDepth q := by
  rw [← sInf_rateSet p, ← sInf_rateSet q, h]

/-- **The rate reading is scale-free**: it depends on the datum only through its depth, which is the
complete dilation invariant. -/
theorem sInf_rateSet_eq_of_sdDepth_eq {p q : ScaleDepthDatum} (h : sdDepth p = sdDepth q) :
    sInf (rateSet p) = sInf (rateSet q) := by
  rw [sInf_rateSet, sInf_rateSet, h]

/-- **The rate reading is the answer.** Its infimum is the depth, so it is constant on dilation
orbits and separates them — the two properties `TheDepthIsTheCompleteDilationInvariant` shows a
resolving reading must have, and which no scale reading of the field has. -/
theorem theRateReadingIsTheAnswer :
    (∀ p : ScaleDepthDatum, sInf (rateSet p) = sdDepth p) ∧
      (∀ p q : ScaleDepthDatum, rateSet p = rateSet q → sdDepth p = sdDepth q) ∧
      ∀ p q : ScaleDepthDatum, sdDepth p = sdDepth q → sInf (rateSet p) = sInf (rateSet q) :=
  ⟨sInf_rateSet, fun _ _ h => sdDepth_eq_of_rateSet_eq h,
    fun _ _ h => sInf_rateSet_eq_of_sdDepth_eq h⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
