/-
Doc 49 first-passage bookkeeping for the MID-central sweep cascade.

`SweepDichotomy` proves the one-step analytic kill/survive alternatives.  This
module records the finite combinatorics that doc 49 needs next: a born
off-line pair has a squared depth, future tower entries add real pushes, and
the pair is absorbed as soon as a partial depth reaches the on-line barrier.

The main reusable endpoint is `survivingBirths_length_le_of_creationRate`: if
every non-resonant birth is killed by its future pushes, then final survivors
are bounded by the number of resonant-window births.  This is the Lean-facing
shape of the de-randomized first-passage + creation-rate reduction in
MID-central.
-/
import GaloisForLFunctions.RHTower.SweepDichotomy

noncomputable section

namespace RHTower

/-- One created off-line pair in the tower cascade.  `time` indexes the first
future push it sees; `depthSq` is its initial squared distance from the on-line
barrier in the normalized `η²` coordinate. -/
structure CascadeBirth where
  time : ℕ
  depthSq : ℝ

/-- Algebraic sum of future real pushes. -/
def pushSum : List ℝ → ℝ
  | [] => 0
  | q :: qs => q + pushSum qs

/-- Total variation budget of future pushes. -/
def pushBudget : List ℝ → ℝ
  | [] => 0
  | q :: qs => |q| + pushBudget qs

theorem pushBudget_nonneg : ∀ qs : List ℝ, 0 ≤ pushBudget qs := by
  intro qs
  induction qs with
  | nil =>
      simp [pushBudget]
  | cons q qs ih =>
      exact add_nonneg (abs_nonneg q) ih

/-- Final squared depth after all listed pushes, ignoring earlier absorption. -/
def depthAfter : ℝ → List ℝ → ℝ
  | depthSq, [] => depthSq
  | depthSq, q :: qs => depthAfter (depthSq + q) qs

theorem depthAfter_eq_add_pushSum :
    ∀ (depthSq : ℝ) (pushes : List ℝ),
      depthAfter depthSq pushes = depthSq + pushSum pushes := by
  intro depthSq pushes
  induction pushes generalizing depthSq with
  | nil =>
      simp [depthAfter, pushSum]
  | cons q qs ih =>
      calc
        depthAfter depthSq (q :: qs) = depthAfter (depthSq + q) qs := rfl
        _ = (depthSq + q) + pushSum qs := ih (depthSq + q)
        _ = depthSq + pushSum (q :: qs) := by
          simp [pushSum]
          ring

/-- The pair survives all listed future pushes: every updated squared depth
stays strictly above the absorbing barrier. -/
def SurvivesFrom : ℝ → List ℝ → Prop
  | depthSq, [] => 0 < depthSq
  | depthSq, q :: qs => 0 < depthSq + q ∧ SurvivesFrom (depthSq + q) qs

/-- The pair is killed by first passage through the on-line barrier. -/
def KilledFrom : ℝ → List ℝ → Prop
  | depthSq, [] => depthSq ≤ 0
  | depthSq, q :: qs =>
      depthSq + q ≤ 0 ∨ (0 < depthSq + q ∧ KilledFrom (depthSq + q) qs)

theorem survivesFrom_not_killedFrom :
    ∀ {depthSq : ℝ} {pushes : List ℝ},
      SurvivesFrom depthSq pushes → ¬ KilledFrom depthSq pushes := by
  intro depthSq pushes
  induction pushes generalizing depthSq with
  | nil =>
      intro hsurv hkill
      dsimp [SurvivesFrom] at hsurv
      dsimp [KilledFrom] at hkill
      linarith
  | cons q qs ih =>
      intro hsurv hkill
      rcases hsurv with ⟨hnext, htail⟩
      dsimp [KilledFrom] at hkill
      rcases hkill with hnow | hlater
      · linarith
      · exact ih htail hlater.2

theorem survivesFrom_of_not_killedFrom :
    ∀ {depthSq : ℝ} {pushes : List ℝ},
      0 < depthSq → ¬ KilledFrom depthSq pushes → SurvivesFrom depthSq pushes := by
  intro depthSq pushes
  induction pushes generalizing depthSq with
  | nil =>
      intro hdepth _hnot
      simpa [SurvivesFrom] using hdepth
  | cons q qs ih =>
      intro _hdepth hnot
      have hnext : 0 < depthSq + q := by
        by_contra hle
        exact hnot (by
          dsimp [KilledFrom]
          exact Or.inl (le_of_not_gt hle))
      constructor
      · exact hnext
      · apply ih hnext
        intro htail
        exact hnot (by
          dsimp [KilledFrom]
          exact Or.inr ⟨hnext, htail⟩)

theorem survivesFrom_iff_not_killedFrom {depthSq : ℝ} {pushes : List ℝ}
    (hdepth : 0 < depthSq) :
    SurvivesFrom depthSq pushes ↔ ¬ KilledFrom depthSq pushes :=
  ⟨survivesFrom_not_killedFrom, survivesFrom_of_not_killedFrom hdepth⟩

/-- If the total remaining push already carries the squared depth past the
barrier, then some first-passage kill happens along the finite list. -/
theorem killedFrom_of_add_pushSum_nonpos :
    ∀ {depthSq : ℝ} {pushes : List ℝ},
      0 < depthSq → depthSq + pushSum pushes ≤ 0 → KilledFrom depthSq pushes := by
  intro depthSq pushes
  induction pushes generalizing depthSq with
  | nil =>
      intro hdepth hfinal
      simp [pushSum] at hfinal
      linarith
  | cons q qs ih =>
      intro hdepth hfinal
      dsimp [KilledFrom]
      by_cases hnext : depthSq + q ≤ 0
      · exact Or.inl hnext
      · have hnext_pos : 0 < depthSq + q := lt_of_not_ge hnext
        exact Or.inr ⟨hnext_pos, ih hnext_pos (by
          simp [pushSum] at hfinal ⊢
          linarith)⟩

/-- A crude deterministic discrepancy bound: if the total variation of future
pushes is smaller than the current squared depth, first passage cannot occur. -/
theorem survivesFrom_of_pushBudget_lt :
    ∀ {depthSq : ℝ} {pushes : List ℝ},
      pushBudget pushes < depthSq → SurvivesFrom depthSq pushes := by
  intro depthSq pushes
  induction pushes generalizing depthSq with
  | nil =>
      intro hbudget
      simp [pushBudget, SurvivesFrom] at hbudget ⊢
      linarith
  | cons q qs ih =>
      intro hbudget
      simp [pushBudget] at hbudget
      have htail_nonneg : 0 ≤ pushBudget qs := pushBudget_nonneg qs
      have hneg_abs : -|q| ≤ q := neg_abs_le q
      have hnext : 0 < depthSq + q := by
        have hpos : 0 < depthSq - |q| := by linarith
        linarith
      have htail_budget : pushBudget qs < depthSq + q := by
        linarith
      exact ⟨hnext, ih htail_budget⟩

/-- Future pushes seen by a birth in a finite tower segment. -/
def futurePushes (pushes : List ℝ) (birth : CascadeBirth) : List ℝ :=
  pushes.drop birth.time

def BirthSurvives (pushes : List ℝ) (birth : CascadeBirth) : Prop :=
  SurvivesFrom birth.depthSq (futurePushes pushes birth)

def BirthKilled (pushes : List ℝ) (birth : CascadeBirth) : Prop :=
  KilledFrom birth.depthSq (futurePushes pushes birth)

/-- Births that survive all future pushes in the finite tower segment. -/
def survivingBirths (pushes : List ℝ) (births : List CascadeBirth) : List CascadeBirth := by
  classical
  exact births.filter fun birth => BirthSurvives pushes birth

/-- Births lying in the designated resonance window.  For MID-central this is
the `|p| ≲ 0.19` transition window; the predicate is left abstract here. -/
def resonantBirths (inResonanceWindow : CascadeBirth → Prop)
    (births : List CascadeBirth) : List CascadeBirth := by
  classical
  exact births.filter inResonanceWindow

theorem mem_survivingBirths_iff {pushes births} {birth : CascadeBirth} :
    birth ∈ survivingBirths pushes births ↔
      birth ∈ births ∧ BirthSurvives pushes birth := by
  classical
  simp [survivingBirths, BirthSurvives]

theorem mem_resonantBirths_iff {births} {inResonanceWindow : CascadeBirth → Prop}
    {birth : CascadeBirth} :
    birth ∈ resonantBirths inResonanceWindow births ↔
      birth ∈ births ∧ inResonanceWindow birth := by
  classical
  simp [resonantBirths]

/-- First-passage localization: if every non-resonant birth is killed by the
future pushes, then every surviving birth lies in the resonance window. -/
theorem survivor_resonant_of_nonresonant_killed {pushes births}
    {inResonanceWindow : CascadeBirth → Prop}
    (hkill :
      ∀ birth ∈ births, ¬ inResonanceWindow birth → BirthKilled pushes birth) :
    ∀ birth ∈ survivingBirths pushes births, inResonanceWindow birth := by
  intro birth hbirth
  rcases (mem_survivingBirths_iff.mp hbirth) with ⟨hmem, hsurv⟩
  by_contra hnonres
  exact survivesFrom_not_killedFrom hsurv (hkill birth hmem hnonres)

/-- Counting form of first-passage localization.  It is intentionally stated
only with the abstract resonance predicate: the analytic work is precisely to
prove `hkill` and then bound the creation rate inside that predicate. -/
theorem survivingBirths_length_le_resonantBirths_length {pushes births}
    {inResonanceWindow : CascadeBirth → Prop}
    (hkill :
      ∀ birth ∈ births, ¬ inResonanceWindow birth → BirthKilled pushes birth) :
    (survivingBirths pushes births).length ≤
      (resonantBirths inResonanceWindow births).length := by
  classical
  induction births with
  | nil =>
      simp [survivingBirths, resonantBirths]
  | cons birth births ih =>
      have hkill_tail :
          ∀ b ∈ births, ¬ inResonanceWindow b → BirthKilled pushes b := by
        intro b hb hnonres
        exact hkill b (by simp [hb]) hnonres
      have ihtail := ih hkill_tail
      by_cases hsurv : BirthSurvives pushes birth
      · have hres : inResonanceWindow birth := by
          by_contra hnonres
          have hkilled : BirthKilled pushes birth := hkill birth (by simp) hnonres
          exact survivesFrom_not_killedFrom hsurv hkilled
        simpa [survivingBirths, resonantBirths, hsurv, hres] using
          Nat.succ_le_succ ihtail
      · by_cases hres : inResonanceWindow birth
        · simpa [survivingBirths, resonantBirths, hsurv, hres] using
            Nat.le_succ_of_le ihtail
        · simpa [survivingBirths, resonantBirths, hsurv, hres] using ihtail

/-- Packaged MID-central cascade input: first-passage kills every non-resonant
birth, and the creation-rate lemma bounds resonant births by `K`. -/
structure SweepCascadeInput (pushes : List ℝ) (births : List CascadeBirth)
    (inResonanceWindow : CascadeBirth → Prop) (K : ℕ) : Prop where
  nonresonant_killed :
    ∀ birth ∈ births, ¬ inResonanceWindow birth → BirthKilled pushes birth
  creation_rate :
    (resonantBirths inResonanceWindow births).length ≤ K

/-- The de-randomized first-passage + creation-rate endpoint. -/
theorem survivingBirths_length_le_of_creationRate {pushes births}
    {inResonanceWindow : CascadeBirth → Prop} {K : ℕ}
    (h : SweepCascadeInput pushes births inResonanceWindow K) :
    (survivingBirths pushes births).length ≤ K :=
  Nat.le_trans
    (survivingBirths_length_le_resonantBirths_length h.nonresonant_killed)
    h.creation_rate

/-- Zero creation in the resonance window gives no final survivors.  This is
the p-central specialization targeted by MID-central. -/
theorem survivingBirths_length_eq_zero_of_no_creation {pushes births}
    {inResonanceWindow : CascadeBirth → Prop}
    (h : SweepCascadeInput pushes births inResonanceWindow 0) :
    (survivingBirths pushes births).length = 0 :=
  Nat.eq_zero_of_le_zero (survivingBirths_length_le_of_creationRate h)

end RHTower
