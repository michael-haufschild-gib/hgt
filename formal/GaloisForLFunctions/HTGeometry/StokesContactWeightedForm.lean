import GaloisForLFunctions.HTGeometry.StokesContactIntegral

/-!
# Complementary contact as a weighted level average

Evaluating the reciprocal-ramification path integral level by level turns the recursive contact
into a single weighted sum: the level at depth `a` carries the weight `1/D_{a-1} - 1/D_a`, where
`D_a` is the ramification accumulated down to that level, and the terminal height carries the
remaining weight `1/D_t`.

The weights are positive and add to one, so complementary contact is a genuine convex combination
of the level heights and the terminal height.  In particular it lies between the terminal height
and the top height, which is the comparison principle the separation lemmas use.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace ContactTower

/-- The terminal height of a contact branch. -/
def terminalHeight : ContactTower → ℚ
  | .leaf height => height
  | .step _ _ tail => tail.terminalHeight

/-- The ramification accumulated along a whole branch. -/
def totalRamification : ContactTower → ℕ
  | .leaf _ => 1
  | .step _ factor tail => factor * tail.totalRamification

theorem totalRamification_pos {t : ContactTower} (h : t.Valid) : 0 < t.totalRamification := by
  induction t with
  | leaf height => simp [totalRamification]
  | step level factor tail ih =>
      simp only [Valid] at h
      exact Nat.mul_pos (Nat.zero_lt_of_lt h.1) (ih h.2.2)

/-- The weighted level sum of a branch, with `w` the reciprocal ramification accumulated above it:
each level takes the decrement of `w` across its own step, and the terminal height takes what is
left. -/
def weightedLevelSum : ContactTower → ℚ → ℚ
  | .leaf height, w => w * height
  | .step level factor tail, w =>
      level * (w - w / (factor : ℚ)) + tail.weightedLevelSum (w / (factor : ℚ))

theorem weightedLevelSum_leaf (height w : ℚ) :
    (ContactTower.leaf height).weightedLevelSum w = w * height := rfl

theorem weightedLevelSum_step (level : ℚ) (factor : ℕ) (tail : ContactTower) (w : ℚ) :
    (ContactTower.step level factor tail).weightedLevelSum w
      = level * (w - w / (factor : ℚ)) + tail.weightedLevelSum (w / (factor : ℚ)) := rfl

/-- The weighted level sum is the contact scaled by the available weight. -/
theorem weightedLevelSum_eq_mul_contact (t : ContactTower) (w : ℚ) :
    t.weightedLevelSum w = w * t.contact := by
  induction t generalizing w with
  | leaf height => simp [weightedLevelSum, contact]
  | step level factor tail ih =>
      rw [weightedLevelSum_step, ih, contact]
      ring

/-- **The closed form of complementary contact.**  Contact is the weighted sum of the level heights
and the terminal height, the weight of each level being the decrement of reciprocal accumulated
ramification across its step. -/
theorem contact_eq_weightedLevelSum (t : ContactTower) : t.contact = t.weightedLevelSum 1 := by
  rw [weightedLevelSum_eq_mul_contact, one_mul]

/-- **The closed form of the analytic contact integral.**  Top height minus the genuine
reciprocal-ramification path integral is the weighted level sum. -/
theorem top_sub_analyticLoss_eq_weightedLevelSum (t : ContactTower) (hvalid : t.Valid) :
    (t.top : ℝ) - t.analyticLoss 1 = ((t.weightedLevelSum 1 : ℚ) : ℝ) := by
  rw [← contact_eq_weightedLevelSum]
  exact (contact_eq_top_sub_analyticLoss t hvalid).symm

/-! ### The weights are a probability vector -/

/-- The total weight distributed by a branch. -/
def weightTotal : ContactTower → ℚ → ℚ
  | .leaf _, w => w
  | .step _ factor tail, w => (w - w / (factor : ℚ)) + tail.weightTotal (w / (factor : ℚ))

/-- **The weights add to the available weight.** -/
theorem weightTotal_eq (t : ContactTower) (w : ℚ) : t.weightTotal w = w := by
  induction t generalizing w with
  | leaf height => simp [weightTotal]
  | step level factor tail ih =>
      rw [weightTotal, ih]
      ring

/-- Every level weight is positive on an admissible branch. -/
theorem level_weight_pos {level : ℚ} {factor : ℕ} {tail : ContactTower}
    (h : (ContactTower.step level factor tail).Valid) {w : ℚ} (hw : 0 < w) :
    0 < w - w / (factor : ℚ) := by
  simp only [Valid] at h
  have hfactor : (1 : ℚ) < (factor : ℚ) := by exact_mod_cast h.1
  have hfactorpos : (0 : ℚ) < (factor : ℚ) := by linarith
  have hlt : w / (factor : ℚ) < w := by
    rw [div_lt_iff₀ hfactorpos]
    nlinarith
  linarith

/-- The residual weight passed down a step stays positive. -/
theorem residual_weight_pos {level : ℚ} {factor : ℕ} {tail : ContactTower}
    (h : (ContactTower.step level factor tail).Valid) {w : ℚ} (hw : 0 < w) :
    0 < w / (factor : ℚ) := by
  simp only [Valid] at h
  have hfactor : (0 : ℚ) < (factor : ℚ) := by
    have : (1 : ℚ) < (factor : ℚ) := by exact_mod_cast h.1
    linarith
  exact div_pos hw hfactor

/-! ### The convex comparison principle -/

/-- Every level of a branch lies below its top height. -/
theorem weightedLevelSum_le {t : ContactTower} (hvalid : t.Valid) {c w : ℚ} (hw : 0 < w)
    (hlevels : t.top ≤ c) (hterm : t.terminalHeight ≤ c) : t.weightedLevelSum w ≤ w * c := by
  induction t generalizing w with
  | leaf height =>
      rw [weightedLevelSum_leaf]
      exact mul_le_mul_of_nonneg_left (by simpa [terminalHeight] using hterm) hw.le
  | step level factor tail ih =>
      have hstep := hvalid
      simp only [Valid] at hvalid
      have hlevel : level ≤ c := by simpa [top] using hlevels
      have htailtop : tail.top ≤ c := le_of_lt (lt_of_lt_of_le hvalid.2.1 hlevel)
      have htailterm : tail.terminalHeight ≤ c := by simpa [terminalHeight] using hterm
      have hres : 0 < w / (factor : ℚ) := residual_weight_pos hstep hw
      have hwpos : 0 < w - w / (factor : ℚ) := level_weight_pos hstep hw
      have h1 : level * (w - w / (factor : ℚ)) ≤ c * (w - w / (factor : ℚ)) :=
        mul_le_mul_of_nonneg_right hlevel hwpos.le
      have h2 : tail.weightedLevelSum (w / (factor : ℚ)) ≤ (w / (factor : ℚ)) * c :=
        ih hvalid.2.2 hres htailtop htailterm
      rw [weightedLevelSum_step]
      nlinarith

/-- The terminal height of an admissible branch is below its top height. -/
theorem terminalHeight_le_top {t : ContactTower} (hvalid : t.Valid) :
    t.terminalHeight ≤ t.top := by
  induction t with
  | leaf height => simp [terminalHeight, top]
  | step level factor tail ih =>
      simp only [Valid] at hvalid
      have htail := ih hvalid.2.2
      simp only [terminalHeight, top]
      exact le_of_lt (lt_of_le_of_lt htail hvalid.2.1)

/-- **The weighted level sum is above the terminal height.** -/
theorem le_weightedLevelSum {t : ContactTower} (hvalid : t.Valid) {c w : ℚ} (hw : 0 < w)
    (hterm : c ≤ t.terminalHeight) : w * c ≤ t.weightedLevelSum w := by
  induction t generalizing w with
  | leaf height =>
      rw [weightedLevelSum_leaf]
      exact mul_le_mul_of_nonneg_left (by simpa [terminalHeight] using hterm) hw.le
  | step level factor tail ih =>
      have hstep := hvalid
      simp only [Valid] at hvalid
      have htailterm : c ≤ tail.terminalHeight := by simpa [terminalHeight] using hterm
      have hlevel : c ≤ level :=
        le_of_lt (lt_of_le_of_lt (le_trans htailterm (terminalHeight_le_top hvalid.2.2))
          hvalid.2.1)
      have hres : 0 < w / (factor : ℚ) := residual_weight_pos hstep hw
      have hwpos : 0 < w - w / (factor : ℚ) := level_weight_pos hstep hw
      have h1 : c * (w - w / (factor : ℚ)) ≤ level * (w - w / (factor : ℚ)) :=
        mul_le_mul_of_nonneg_right hlevel hwpos.le
      have h2 : (w / (factor : ℚ)) * c ≤ tail.weightedLevelSum (w / (factor : ℚ)) :=
        ih hvalid.2.2 hres htailterm
      rw [weightedLevelSum_step]
      nlinarith

/-- **Contact is at most the top height.** -/
theorem contact_le_top {t : ContactTower} (hvalid : t.Valid) : t.contact ≤ t.top := by
  have h := weightedLevelSum_le hvalid (c := t.top) one_pos (le_refl _)
    (terminalHeight_le_top hvalid)
  rw [← contact_eq_weightedLevelSum] at h
  simpa using h

/-- **Contact is at least the terminal height.**  Together with the previous bound, complementary
contact is a convex combination of the level heights and the terminal height. -/
theorem terminalHeight_le_contact {t : ContactTower} (hvalid : t.Valid) :
    t.terminalHeight ≤ t.contact := by
  have h := le_weightedLevelSum hvalid (c := t.terminalHeight) one_pos (le_refl _)
  rw [← contact_eq_weightedLevelSum] at h
  simpa using h

/-- **Strict convex undercut.**  A branch whose levels stay below a bound and whose terminal height
is strictly below it has weighted sum strictly below the bound: the terminal weight is positive and
samples the strictly smaller value. -/
theorem weightedLevelSum_lt {t : ContactTower} (hvalid : t.Valid) {c w : ℚ} (hw : 0 < w)
    (hlevels : t.top ≤ c) (hterm : t.terminalHeight < c) : t.weightedLevelSum w < w * c := by
  induction t generalizing w with
  | leaf height =>
      rw [weightedLevelSum_leaf]
      exact mul_lt_mul_of_pos_left (by simpa [terminalHeight] using hterm) hw
  | step level factor tail ih =>
      have hstep := hvalid
      simp only [Valid] at hvalid
      have hlevel : level ≤ c := by simpa [top] using hlevels
      have htailtop : tail.top ≤ c := le_of_lt (lt_of_lt_of_le hvalid.2.1 hlevel)
      have htailterm : tail.terminalHeight < c := by simpa [terminalHeight] using hterm
      have hres : 0 < w / (factor : ℚ) := residual_weight_pos hstep hw
      have hwpos : 0 < w - w / (factor : ℚ) := level_weight_pos hstep hw
      have h1 : level * (w - w / (factor : ℚ)) ≤ c * (w - w / (factor : ℚ)) :=
        mul_le_mul_of_nonneg_right hlevel hwpos.le
      have h2 : tail.weightedLevelSum (w / (factor : ℚ)) < (w / (factor : ℚ)) * c :=
        ih hvalid.2.2 hres htailtop htailterm
      rw [weightedLevelSum_step]
      nlinarith

/-- **The undercut in contact form.**  This is the mechanism of the nested separation lemma: a
branch continuing below a common fission exponent has strictly smaller contact than that
exponent. -/
theorem contact_lt_of_terminalHeight_lt {t : ContactTower} (hvalid : t.Valid) {c : ℚ}
    (hlevels : t.top ≤ c) (hterm : t.terminalHeight < c) : t.contact < c := by
  have h := weightedLevelSum_lt hvalid (w := 1) one_pos hlevels hterm
  rw [← contact_eq_weightedLevelSum] at h
  simpa using h

/-! ### The terminal height carries the reciprocal of the total ramification -/

/-- Replace the terminal height of a branch, keeping its levels and ramification. -/
def setTerminal : ContactTower → ℚ → ContactTower
  | .leaf _, h => .leaf h
  | .step level factor tail, h => .step level factor (tail.setTerminal h)

theorem totalRamification_setTerminal (t : ContactTower) (h : ℚ) :
    (t.setTerminal h).totalRamification = t.totalRamification := by
  induction t with
  | leaf height => simp [setTerminal, totalRamification]
  | step level factor tail ih => simp [setTerminal, totalRamification, ih]

theorem terminalHeight_setTerminal (t : ContactTower) (h : ℚ) :
    (t.setTerminal h).terminalHeight = h := by
  induction t with
  | leaf height => simp [setTerminal, terminalHeight]
  | step level factor tail ih => simpa [setTerminal, terminalHeight] using ih

theorem top_setTerminal_le {t : ContactTower} {h : ℚ} (hle : h ≤ t.terminalHeight) :
    (t.setTerminal h).top ≤ t.top := by
  cases t with
  | leaf height => simpa [setTerminal, top, terminalHeight] using hle
  | step level factor tail => simp [setTerminal, top]

theorem valid_setTerminal {t : ContactTower} (hvalid : t.Valid) {h : ℚ} (hh : 0 ≤ h)
    (hle : h ≤ t.terminalHeight) : (t.setTerminal h).Valid := by
  induction t with
  | leaf height => simpa [setTerminal, Valid] using hh
  | step level factor tail ih =>
      simp only [Valid] at hvalid
      have hletail : h ≤ tail.terminalHeight := by simpa [terminalHeight] using hle
      refine ⟨hvalid.1, ?_, ih hvalid.2.2 hletail⟩
      exact lt_of_le_of_lt (top_setTerminal_le hletail) hvalid.2.1

/-- **The terminal height carries weight the reciprocal of the total ramification.**  Contact is
affine in the terminal height with that exact slope, which is the positive terminal weight the
separation argument uses. -/
theorem contact_setTerminal (t : ContactTower) (h : ℚ) :
    (t.setTerminal h).contact
      = (t.setTerminal 0).contact + h / (t.totalRamification : ℚ) := by
  induction t with
  | leaf height => simp [setTerminal, contact, totalRamification]
  | step level factor tail ih =>
      simp only [setTerminal, contact, totalRamification, ih]
      push_cast
      ring

/-- **The slope of contact in the terminal height is the reciprocal ramification.**  Every
difference quotient of complementary contact in the terminal height equals `1/R`, which is the
route's `d kappa / de = 1/R` in the rational model. -/
theorem contact_setTerminal_slope (t : ContactTower) {h h' : ℚ} (hne : h ≠ h') :
    ((t.setTerminal h').contact - (t.setTerminal h).contact) / (h' - h)
      = 1 / (t.totalRamification : ℚ) := by
  have hsub : h' - h ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [contact_setTerminal t h, contact_setTerminal t h']
  field_simp
  ring

/-- The terminal weight is positive on an admissible branch. -/
theorem terminal_weight_pos {t : ContactTower} (hvalid : t.Valid) :
    0 < (1 : ℚ) / (t.totalRamification : ℚ) := by
  have h : 0 < t.totalRamification := totalRamification_pos hvalid
  have hq : (0 : ℚ) < (t.totalRamification : ℚ) := by exact_mod_cast h
  exact div_pos one_pos hq

/-- **Contact is strictly increasing in the terminal height.**  This is the exact mechanism behind
the strict diagonal and nested separations. -/
theorem contact_setTerminal_strictMono {t : ContactTower} (hvalid : t.Valid) {h h' : ℚ}
    (hlt : h < h') : (t.setTerminal h).contact < (t.setTerminal h').contact := by
  rw [contact_setTerminal t h, contact_setTerminal t h']
  have hq : (0 : ℚ) < (t.totalRamification : ℚ) := by
    exact_mod_cast totalRamification_pos hvalid
  have hdiv := div_lt_div_of_pos_right hlt hq
  linarith

end ContactTower

end IrregularStokes
end GaloisForLFunctions
