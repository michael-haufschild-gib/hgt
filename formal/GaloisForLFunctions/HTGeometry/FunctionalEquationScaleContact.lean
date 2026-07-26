/-
The functional equation brings the two scale windows into contact only at a degenerate scale.

The functional equation exchanges a sum of length `N^c` for its dual of length `N^(1-c)`, so on the
scale variable it acts as the reflection

    **c ↦ 1 - c** ,

an involution whose unique fixed point is the critical scale `c = 1/2`.  This is the same reflection
the van der Corput `B`-process performs on the covering length variable.

The polynomial window is `c ≤ 1 - 1/k` and the completion window is `c ≥ 1`; they are disjoint.
Applying the functional equation to the polynomial window gives `[1/k, 1]`, which meets the completion
window only at the single point `c = 1` — the image of `c = 0`, blocks of one term.  So:

* no scale `c > 0` satisfies the polynomial condition while its dual satisfies the completion
  condition;
* the only contact is degenerate, at the scale where the block decomposition is trivial.

This is why the functional equation is simultaneously the *unique* classical coupling of smoothness
and multiplicativity and of no use for the frontier object: it is the map that brings the windows
into contact, and the contact point carries no content.
-/
import GaloisForLFunctions.HTGeometry.ScaleWindowIncompatibility

namespace HTGeometry

/-! ### The reflection -/

/-- The functional equation's action on the block-scale variable. -/
def feReflect (c : ℚ) : ℚ := 1 - c

/-- It is an involution. -/
@[simp] theorem feReflect_involutive (c : ℚ) : feReflect (feReflect c) = c := by
  unfold feReflect; ring

/-- **Its unique fixed point is the critical scale.** -/
theorem feReflect_fixed_iff (c : ℚ) : feReflect c = c ↔ c = 1 / 2 := by
  unfold feReflect
  constructor <;> intro h <;> linarith

/-- The reflection is order-reversing. -/
theorem feReflect_antitone {c c' : ℚ} (h : c ≤ c') : feReflect c' ≤ feReflect c := by
  unfold feReflect; linarith

/-! ### Membership in the two windows -/

/-- The polynomial window at degree `k`. -/
def polyWindow (k c : ℚ) : Prop := c ≤ taylorValidityMax k

/-- The completion window. -/
def completionWindow (c : ℚ) : Prop := completionMin ≤ c

/-- **The critical scale lies in the polynomial window for every degree at least two.** -/
theorem critical_in_polyWindow {k : ℚ} (hk : 2 ≤ k) : polyWindow k (1 / 2) := by
  unfold polyWindow taylorValidityMax
  have hk0 : (0:ℚ) < k := by linarith
  have : 1 / k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hk0 (by norm_num : (0:ℚ) < 2)]; linarith
  linarith

/-- **And never in the completion window.** -/
theorem critical_not_in_completionWindow : ¬ completionWindow (1 / 2) := by
  unfold completionWindow completionMin; norm_num

/-- **The functional equation fixes the critical scale**, so it cannot move it into the completion
window. -/
theorem fe_fixes_critical : feReflect (1 / 2) = 1 / 2 := by
  unfold feReflect; norm_num

/-! ### The image of the polynomial window -/

/-- **The dual of the largest valid polynomial scale is `1/k`** — still far from the completion
window. -/
theorem fe_image_of_validity_max (k : ℚ) : feReflect (taylorValidityMax k) = 1 / k := by
  unfold feReflect taylorValidityMax; ring

/-- **The dual of a polynomial scale lies in the completion window only when the scale is
nonpositive.** -/
theorem fe_dual_completes_iff (c : ℚ) : completionWindow (feReflect c) ↔ c ≤ 0 := by
  unfold completionWindow completionMin feReflect
  constructor <;> intro h <;> linarith

/-- **The contact is degenerate.**  No positive scale has its dual in the completion window while
itself lying in the polynomial window. -/
theorem fe_contact_is_degenerate {c : ℚ} (hc : 0 ≤ c)
    (hdual : completionWindow (feReflect c)) : c = 0 := by
  have := (fe_dual_completes_iff c).mp hdual
  linarith

/-- Equivalently: at every positive scale in the polynomial window, the dual still carries a positive
completion deficit. -/
theorem fe_dual_deficit_pos {c : ℚ} (hc : 0 < c) : 0 < completionDeficit (feReflect c) := by
  unfold completionDeficit feReflect; linarith

/-- The dual completion deficit at a scale is the scale itself. -/
@[simp] theorem fe_dual_deficit_eq (c : ℚ) : completionDeficit (feReflect c) = c := by
  unfold completionDeficit feReflect; ring

/-! ### The two failures are one reflection apart -/

/-- **The deficit and its dual sum to one.**  Completion fails on the primal side by `1 - c` and on
the dual side by `c`; the two cannot both vanish. -/
theorem deficits_sum_to_one (c : ℚ) :
    completionDeficit c + completionDeficit (feReflect c) = 1 := by
  unfold completionDeficit feReflect; ring

/-- **Hence at least one of the two sides carries a deficit of at least `1/2`,** with equality only at
the critical scale. -/
theorem some_side_has_half_deficit (c : ℚ) :
    1 / 2 ≤ completionDeficit c ∨ 1 / 2 ≤ completionDeficit (feReflect c) := by
  by_cases h : 1 / 2 ≤ completionDeficit c
  · exact Or.inl h
  · right
    have hsum := deficits_sum_to_one c
    have h' : completionDeficit c < 1 / 2 := lt_of_not_ge h
    linarith

/-- **At the critical scale both deficits are exactly `1/2`** — the functional equation's fixed point
is where the two failures are perfectly balanced, and neither can be traded for the other. -/
theorem critical_deficits_balanced :
    completionDeficit (1 / 2) = 1 / 2 ∧ completionDeficit (feReflect (1 / 2)) = 1 / 2 := by
  rw [fe_fixes_critical]
  constructor <;> (unfold completionDeficit; norm_num)

/-- **The closure.**  The functional equation is the only map available that exchanges the two
windows, it fixes the critical scale, and at that scale both completion deficits equal `1/2`.  So no
application of it can produce a scale where completion is productive. -/
theorem fe_cannot_produce_completion {c : ℚ} (hc : 0 < c) :
    ¬ completionWindow c ∨ ¬ completionWindow (feReflect c) := by
  right
  intro h
  have := (fe_dual_completes_iff c).mp h
  linarith

end HTGeometry
