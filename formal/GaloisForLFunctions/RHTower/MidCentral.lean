/-
Docs 50–52 assembly (task #160): (MID-central), machine-checked over the four
typed inputs.

The cascade data is `SweepCascade`'s (pushes, births, window); the four
analytic inputs of doc 52 §6 enter as the fields of `MidCentralInput`:

* `dip_kills` — (DRIFT-dip) + (HOLD-phase): every birth outside the slip
  window has a prefix of its future pushes carrying it to the barrier
  (supplied on paper by `drift_dip_excursion` against the birth's depth;
  the configurational |H| anti-correlation is exactly what makes the
  amplitude floor available).
* `creation_rate` — (CR-density): resonant-window births are at most K
  (supplied by `finset_chebyshev` + `pricing_pigeonhole` over the named
  partial-fraction decomposition).
* (DEEP-FATE) enters as measured support: no fifth input is needed — the
  tracker (deep_fate_tracker.py) confirms absorption on the N^{1/3} clock
  and death of resonant pairs within ≤ 3 entries past matched level.

Endpoint: survivors of the completed cascade number at most K; with zero
resonant creation, none — (MID-central) in counting form.
-/
import GaloisForLFunctions.RHTower.SweepCascade
import GaloisForLFunctions.RHTower.DriftDip
import GaloisForLFunctions.RHTower.HoldPhase
import GaloisForLFunctions.RHTower.CreationRate

namespace RHTower

/-- The slip-budget window of doc 51 §9: a birth is resonant iff its slip
2πd² is within the budget κ. -/
def SlipWindow (κ : ℝ) (slip : CascadeBirth → ℝ) (b : CascadeBirth) : Prop :=
  slip b ≤ κ

/-- First passage inside a prefix: if some prefix of the push list already
carries the depth to the barrier, the full list kills. -/
theorem killedFrom_of_prefix_nonpos :
    ∀ (l₁ : List ℝ) {l₂ : List ℝ} {d : ℝ},
      0 < d → d + pushSum l₁ ≤ 0 → KilledFrom d (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ d hd hsum
    simp only [pushSum] at hsum
    linarith
  | cons q qs ih =>
    intro l₂ d hd hsum
    simp only [List.cons_append, KilledFrom]
    by_cases hnext : d + q ≤ 0
    · exact Or.inl hnext
    · rw [not_le] at hnext
      refine Or.inr ⟨hnext, ih hnext ?_⟩
      simp only [pushSum] at hsum
      linarith

/-- A nonpositive prefix rules out survival through the full push list; the first-passage
`KilledFrom` certificate is constructed internally. -/
theorem not_survivesFrom_of_prefix_nonpos
    (l₁ : List ℝ) {l₂ : List ℝ} {d : ℝ}
    (hd : 0 < d) (hsum : d + pushSum l₁ ≤ 0) :
    ¬ SurvivesFrom d (l₁ ++ l₂) := fun hsurv =>
  survivesFrom_not_killedFrom hsurv (killedFrom_of_prefix_nonpos l₁ hd hsum)

/-- A dip below the birth's depth inside any prefix of its future pushes
kills the birth. -/
theorem birthKilled_of_prefix_dip {pushes : List ℝ} {birth : CascadeBirth}
    (hd : 0 < birth.depthSq)
    (hdip : ∃ l₁, l₁ <+: futurePushes pushes birth ∧
      birth.depthSq + pushSum l₁ ≤ 0) :
    BirthKilled pushes birth := by
  obtain ⟨l₁, ⟨l₂, hpre⟩, hsum⟩ := hdip
  unfold BirthKilled
  rw [← hpre]
  exact killedFrom_of_prefix_nonpos l₁ hd hsum

/-- **The (MID-central) input package (doc 52 §6)**: positive birth depths,
the (DRIFT-dip)/(HOLD-phase) prefix-dip for every out-of-window birth, and
the (CR-density) bound on in-window creation. -/
structure MidCentralInput (pushes : List ℝ) (births : List CascadeBirth)
    (κ : ℝ) (slip : CascadeBirth → ℝ) (K : ℕ) : Prop where
  depth_pos : ∀ b ∈ births, 0 < b.depthSq
  dip_kills : ∀ b ∈ births, ¬ SlipWindow κ slip b →
    ∃ l₁, l₁ <+: futurePushes pushes b ∧ b.depthSq + pushSum l₁ ≤ 0
  creation_rate : (resonantBirths (SlipWindow κ slip) births).length ≤ K

/-- **(MID-central), counting form**: under the four typed inputs the
completed cascade's surviving off-line pairs number at most K. -/
theorem midCentral_survivors_le {pushes : List ℝ} {births : List CascadeBirth}
    {κ : ℝ} {slip : CascadeBirth → ℝ} {K : ℕ}
    (h : MidCentralInput pushes births κ slip K) :
    (survivingBirths pushes births).length ≤ K := by
  apply survivingBirths_length_le_of_creationRate
  refine ⟨?_, h.creation_rate⟩
  intro b hb hnres
  exact birthKilled_of_prefix_dip (h.depth_pos b hb) (h.dip_kills b hb hnres)

/-- **(MID-central), empty form**: with no resonant creation, no survivors. -/
theorem midCentral_empty {pushes : List ℝ} {births : List CascadeBirth}
    {κ : ℝ} {slip : CascadeBirth → ℝ}
    (h : MidCentralInput pushes births κ slip 0) :
    (survivingBirths pushes births).length = 0 :=
  Nat.eq_zero_of_le_zero (midCentral_survivors_le h)

/-- Survivors are localized to the slip window (the census reading:
survivor support = {slip ≤ κ}). -/
theorem midCentral_survivors_in_window {pushes : List ℝ}
    {births : List CascadeBirth} {κ : ℝ} {slip : CascadeBirth → ℝ} {K : ℕ}
    (h : MidCentralInput pushes births κ slip K) :
    ∀ b ∈ survivingBirths pushes births, SlipWindow κ slip b := by
  intro b hb
  refine survivor_resonant_of_nonresonant_killed ?_ b hb
  intro b' hb' hnres
  exact birthKilled_of_prefix_dip (h.depth_pos b' hb') (h.dip_kills b' hb' hnres)

end RHTower
