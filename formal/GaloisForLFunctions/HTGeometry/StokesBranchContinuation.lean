import GaloisForLFunctions.HTGeometry.StokesContactWeightedForm

/-!
# Continuing a contact branch below its terminal height

A diagonal contact coordinate is computed from the whole ramification profile of one circle, while
an off-diagonal one stops at the fission height of the pair.  The two branches therefore differ by
a continuation attached below the terminal height of the common part.

Grafting such a continuation lowers complementary contact by exactly the reciprocal-ramification
path integral of the continuation, rescaled by the ramification accumulated above it:

```text
kappa(common) - kappa(common continued by b) = ∫ du / R(u)
```

over the heights covered by `b`.  This is the analytic route to strict diagonal--edge separation:
the continuation of a genuine branch is nontrivial, so its integral is strictly positive.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace ContactTower

/-- Continue a branch below its terminal height by attaching a second branch there. -/
def graft : ContactTower → ContactTower → ContactTower
  | .leaf _, s => s
  | .step level factor tail, s => .step level factor (graft tail s)

/-- Grafting below the terminal height leaves the top height unchanged. -/
theorem top_graft (s : ContactTower) :
    ∀ t : ContactTower, s.top = t.terminalHeight → (t.graft s).top = t.top := by
  intro t
  induction t with
  | leaf height =>
      intro hs
      simpa [graft, top, terminalHeight] using hs
  | step level factor tail _ =>
      intro _
      rfl

/-- The terminal height of a continued branch is that of the continuation. -/
theorem terminalHeight_graft (s : ContactTower) :
    ∀ t : ContactTower, (t.graft s).terminalHeight = s.terminalHeight := by
  intro t
  induction t with
  | leaf height => rfl
  | step level factor tail ih => simpa [graft, terminalHeight] using ih

/-- Ramification accumulates multiplicatively along a continued branch. -/
theorem totalRamification_graft (s : ContactTower) :
    ∀ t : ContactTower,
      (t.graft s).totalRamification = t.totalRamification * s.totalRamification := by
  intro t
  induction t with
  | leaf height => simp [graft, totalRamification]
  | step level factor tail ih =>
      simp only [graft, totalRamification, ih]
      ring

/-- A continuation attached at the terminal height preserves admissibility. -/
theorem valid_graft {s : ContactTower} (hsv : s.Valid) :
    ∀ t : ContactTower, t.Valid → s.top = t.terminalHeight → (t.graft s).Valid := by
  intro t
  induction t with
  | leaf height =>
      intro _ _
      simpa [graft] using hsv
  | step level factor tail ih =>
      intro ht hs
      simp only [Valid] at ht ⊢
      have hs' : s.top = tail.terminalHeight := by simpa [terminalHeight] using hs
      exact ⟨ht.1, by rw [top_graft s tail hs']; exact ht.2.1, ih ht.2.2 hs'⟩

/-- The reciprocal-ramification loss of a continued branch adds the loss of the continuation,
rescaled by the ramification accumulated above it. -/
theorem loss_graft (s : ContactTower) :
    ∀ t : ContactTower, s.top = t.terminalHeight →
      (t.graft s).loss = t.loss + s.loss / (t.totalRamification : ℚ) := by
  intro t
  induction t with
  | leaf height =>
      intro _
      simp [graft, loss, totalRamification]
  | step level factor tail ih =>
      intro hs
      have hs' : s.top = tail.terminalHeight := by simpa [terminalHeight] using hs
      simp only [graft, loss, totalRamification, top_graft s tail hs', ih hs']
      push_cast
      ring

/-- **Continuing a branch lowers its complementary contact by the rescaled loss of the
continuation.** -/
theorem contact_graft {t s : ContactTower} (hs : s.top = t.terminalHeight) :
    (t.graft s).contact = t.contact - s.loss / (t.totalRamification : ℚ) := by
  rw [contact_eq_top_sub_loss, contact_eq_top_sub_loss, top_graft s t hs, loss_graft s t hs]
  ring

/-- **The diagonal--edge contact gap is a genuine path integral.**  The difference between the
complementary contact of a common branch and that of its continuation is the interval integral of
the reciprocal ramification index over the heights the continuation covers. -/
theorem contact_sub_contact_graft_eq_analyticLoss {t s : ContactTower} (ht : t.Valid)
    (hsv : s.Valid) (hs : s.top = t.terminalHeight) :
    (t.contact : ℝ) - ((t.graft s).contact : ℝ) = s.analyticLoss t.totalRamification := by
  rw [analyticLoss_eq_loss_div s hsv (totalRamification_pos ht), contact_graft hs]
  push_cast
  ring

/-- **Strict diagonal--edge separation, analytic route.**  A nontrivial continuation has strictly
positive reciprocal-ramification integral, so it strictly lowers complementary contact. -/
theorem contact_graft_lt {t : ContactTower} (ht : t.Valid) {level : ℚ} {factor : ℕ}
    {tail : ContactTower} (hsv : (ContactTower.step level factor tail).Valid)
    (hs : (ContactTower.step level factor tail).top = t.terminalHeight) :
    (t.graft (ContactTower.step level factor tail)).contact < t.contact := by
  have hloss : 0 < (ContactTower.step level factor tail).loss := loss_step_pos hsv
  have hram : (0 : ℚ) < (t.totalRamification : ℚ) := by
    exact_mod_cast totalRamification_pos ht
  have hpos : 0 < (ContactTower.step level factor tail).loss / (t.totalRamification : ℚ) :=
    div_pos hloss hram
  rw [contact_graft hs]
  linarith

/-- A branch whose terminal height lies strictly below its top has strictly positive
reciprocal-ramification loss. -/
theorem loss_pos_of_terminalHeight_lt {t : ContactTower} (hvalid : t.Valid)
    (hlt : t.terminalHeight < t.top) : 0 < t.loss := by
  cases t with
  | leaf height => exact absurd hlt (lt_irrefl height)
  | step level factor tail => exact loss_step_pos hvalid

/-- **Lemma 8.1, analytic route.**  Distinct Stokes circles have positive fission height, so the
diagonal branch continues strictly below the terminal height of the common branch, and its
reciprocal-ramification integral strictly lowers the complementary contact:

```text
kappa(diagonal) < kappa(pair) .
```
-/
theorem contact_graft_lt_of_terminalHeight_lt {t s : ContactTower} (ht : t.Valid) (hsv : s.Valid)
    (hs : s.top = t.terminalHeight) (hlt : s.terminalHeight < s.top) :
    (t.graft s).contact < t.contact := by
  have hloss : 0 < s.loss := loss_pos_of_terminalHeight_lt hsv hlt
  have hram : (0 : ℚ) < (t.totalRamification : ℚ) := by
    exact_mod_cast totalRamification_pos ht
  rw [contact_graft hs]
  have : 0 < s.loss / (t.totalRamification : ℚ) := div_pos hloss hram
  linarith

/-- **The diagonal branch of a pair.**  Continuing the common branch of two distinct circles by the
remaining profile of one of them, down to terminal height zero, gives a branch with the same top,
terminal height zero, and strictly smaller complementary contact; the contact gap is exactly the
reciprocal-ramification integral over the heights below the fission height. -/
theorem diagonal_graft_law {common below : ContactTower} (hc : common.Valid) (hb : below.Valid)
    (hs : below.top = common.terminalHeight) (hzero : below.terminalHeight = 0)
    (hfission : 0 < common.terminalHeight) :
    (common.graft below).top = common.top ∧
      (common.graft below).terminalHeight = 0 ∧
      (common.graft below).contact < common.contact ∧
      (common.contact : ℝ) - ((common.graft below).contact : ℝ)
        = below.analyticLoss common.totalRamification := by
  refine ⟨top_graft below common hs, ?_, ?_, ?_⟩
  · rw [terminalHeight_graft below common, hzero]
  · exact contact_graft_lt_of_terminalHeight_lt hc hb hs (by rw [hzero, hs]; exact hfission)
  · exact contact_sub_contact_graft_eq_analyticLoss hc hb hs

end ContactTower

end IrregularStokes
end GaloisForLFunctions
