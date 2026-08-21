import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat

/-!
# Alternating label sets

Fix an integer labelling `lab : V → ℤ`.  A finite set `σ` of vertices is *alternating* when the
labels occurring on it have pairwise distinct absolute values and, listed in order of increasing
absolute value, alternate in sign.  The *sign* of an alternating set is the sign of its label of
smallest absolute value.

This file develops the combinatorics of alternating sets that the Fan–Tucker path argument needs:

* `rk lab σ v` — the rank of `v ∈ σ` in the ordering by `|lab ·|`;
* `Consec lab σ u v` — `v` is the successor of `u` in that ordering;
* `alt lab s σ` — `σ` is alternating with sign `s`;
* `almostAlt lab s σ` — `σ` is not alternating but has an alternating facet, of sign `s`.

The main results are the facet counts `card_alt_erase_of_alt` and `card_alt_erase_of_almostAlt`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.BorsukUlam

open Finset

variable {V : Type*} [DecidableEq V]

/-- The rank of `v` inside `σ`: how many members of `σ` carry a strictly smaller label in
absolute value. -/
def rk (lab : V → ℤ) (σ : Finset V) (v : V) : ℕ :=
  (σ.filter (fun w => |lab w| < |lab v|)).card

/-- `true` when the label of `v` is positive. -/
def pos (lab : V → ℤ) (v : V) : Bool := decide (0 < lab v)

/-- The labels on `σ` have pairwise distinct absolute values. -/
def MagInj (lab : V → ℤ) (σ : Finset V) : Prop :=
  ∀ u ∈ σ, ∀ v ∈ σ, |lab u| = |lab v| → u = v

/-- No label on `σ` vanishes. -/
def Nz (lab : V → ℤ) (σ : Finset V) : Prop := ∀ v ∈ σ, lab v ≠ 0

section Rank

variable {lab : V → ℤ} {σ : Finset V}

theorem rk_lt_card {v : V} (hv : v ∈ σ) : rk lab σ v < σ.card := by
  rw [rk]
  have hsub : σ.filter (fun w => |lab w| < |lab v|) ⊆ σ.erase v := by
    intro w hw
    rw [mem_filter] at hw
    refine mem_erase.mpr ⟨?_, hw.1⟩
    rintro rfl
    exact lt_irrefl _ hw.2
  have h := card_le_card hsub
  rw [card_erase_of_mem hv] at h
  have hpos : 0 < σ.card := card_pos.mpr ⟨v, hv⟩
  omega

theorem rk_lt_rk_of_mag_lt {u v : V} (hu : u ∈ σ) (h : |lab u| < |lab v|) :
    rk lab σ u < rk lab σ v := by
  refine card_lt_card ⟨?_, ?_⟩
  · intro w hw
    rw [mem_filter] at hw ⊢
    exact ⟨hw.1, lt_trans hw.2 h⟩
  · intro hcon
    have hmem : u ∈ σ.filter (fun w => |lab w| < |lab v|) := mem_filter.mpr ⟨hu, h⟩
    have := hcon hmem
    rw [mem_filter] at this
    exact lt_irrefl _ this.2

theorem mag_lt_of_rk_lt (hmi : MagInj lab σ) {u v : V} (hu : u ∈ σ) (hv : v ∈ σ)
    (h : rk lab σ u < rk lab σ v) : |lab u| < |lab v| := by
  rcases lt_trichotomy (|lab u|) (|lab v|) with h1 | h1 | h1
  · exact h1
  · exact absurd (hmi u hu v hv h1) (by rintro rfl; omega)
  · exact absurd (rk_lt_rk_of_mag_lt hv h1) (by omega)

theorem rk_injOn (hmi : MagInj lab σ) {u v : V} (hu : u ∈ σ) (hv : v ∈ σ)
    (h : rk lab σ u = rk lab σ v) : u = v := by
  rcases lt_trichotomy (|lab u|) (|lab v|) with h1 | h1 | h1
  · exact absurd (rk_lt_rk_of_mag_lt hu h1) (by omega)
  · exact hmi u hu v hv h1
  · exact absurd (rk_lt_rk_of_mag_lt hv h1) (by omega)

theorem rk_surj (hmi : MagInj lab σ) {k : ℕ} (hk : k < σ.card) : ∃ v ∈ σ, rk lab σ v = k := by
  classical
  have hmaps : ∀ v ∈ σ, rk lab σ v ∈ Finset.range σ.card := by
    intro v hv
    exact mem_range.mpr (rk_lt_card hv)
  have hinj : ∀ u ∈ σ, ∀ v ∈ σ, rk lab σ u = rk lab σ v → u = v := fun u hu v hv h =>
    rk_injOn hmi hu hv h
  have hcard : (Finset.range σ.card).card ≤ σ.card := by simp
  have := Finset.surj_on_of_inj_on_of_card_le (fun (v : V) (_ : v ∈ σ) => rk lab σ v)
    (fun a ha => hmaps a ha) (fun a₁ a₂ ha₁ ha₂ h => hinj a₁ ha₁ a₂ ha₂ h) hcard
  obtain ⟨v, hv, hveq⟩ := this k (mem_range.mpr hk)
  exact ⟨v, hv, hveq.symm⟩

/-- `v` is the immediate successor of `u` in the ordering of `σ` by `|lab ·|`. -/
def Consec (lab : V → ℤ) (σ : Finset V) (u v : V) : Prop :=
  u ∈ σ ∧ v ∈ σ ∧ |lab u| < |lab v| ∧ ∀ w ∈ σ, ¬(|lab u| < |lab w| ∧ |lab w| < |lab v|)

theorem rk_succ_of_consec (hmi : MagInj lab σ) {u v : V} (h : Consec lab σ u v) :
    rk lab σ v = rk lab σ u + 1 := by
  obtain ⟨hu, hv, hlt, hno⟩ := h
  have hset : σ.filter (fun w => |lab w| < |lab v|) =
      insert u (σ.filter (fun w => |lab w| < |lab u|)) := by
    ext w
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hw, hwlt⟩
      by_cases hcase : |lab w| < |lab u|
      · exact Or.inr ⟨hw, hcase⟩
      · left
        refine hmi w hw u hu ?_
        rcases lt_trichotomy (|lab u|) (|lab w|) with h1 | h1 | h1
        · exact absurd ⟨h1, hwlt⟩ (hno w hw)
        · exact h1.symm
        · exact absurd h1 hcase
    · rintro (rfl | ⟨hw, hwlt⟩)
      · exact ⟨hu, hlt⟩
      · exact ⟨hw, lt_trans hwlt hlt⟩
  rw [rk, hset, card_insert_of_notMem (by simp)]
  rfl

theorem consec_of_rk_succ (hmi : MagInj lab σ) {u v : V} (hu : u ∈ σ) (hv : v ∈ σ)
    (h : rk lab σ v = rk lab σ u + 1) : Consec lab σ u v := by
  refine ⟨hu, hv, mag_lt_of_rk_lt hmi hu hv (by omega), ?_⟩
  rintro w hw ⟨h1, h2⟩
  have hr1 : rk lab σ u < rk lab σ w := rk_lt_rk_of_mag_lt hu h1
  have hr2 : rk lab σ w < rk lab σ v := rk_lt_rk_of_mag_lt hw h2
  omega

end Rank

section Alt

variable {lab : V → ℤ} {σ : Finset V} {s : Bool}

/-- `σ` is alternating with sign `s`: labels are nonzero with distinct absolute values, and the
sign of a label is `s` flipped once for each smaller label. -/
def alt (lab : V → ℤ) (s : Bool) (σ : Finset V) : Prop :=
  Nz lab σ ∧ MagInj lab σ ∧ ∀ v ∈ σ, pos lab v = xor s (decide (rk lab σ v % 2 = 1))

/-- A *defect*: two consecutive labels of the same sign. -/
def Defect (lab : V → ℤ) (σ : Finset V) (u v : V) : Prop :=
  Consec lab σ u v ∧ pos lab u = pos lab v

/-- `σ` is alternating for some sign. -/
def AltSet (lab : V → ℤ) (σ : Finset V) : Prop :=
  Nz lab σ ∧ MagInj lab σ ∧ ∀ u v, ¬ Defect lab σ u v

theorem alt_nz (h : alt lab s σ) : Nz lab σ := h.1

theorem alt_magInj (h : alt lab s σ) : MagInj lab σ := h.2.1

theorem exists_min (hmi : MagInj lab σ) (hne : σ.Nonempty) : ∃ v ∈ σ, rk lab σ v = 0 :=
  rk_surj hmi (card_pos.mpr hne)

theorem alt_sign_of_min (h : alt lab s σ) {v : V} (hv : v ∈ σ) (hr : rk lab σ v = 0) :
    s = pos lab v := by
  have := h.2.2 v hv
  rw [hr] at this
  simpa using this.symm

theorem decide_succ_mod_two (n : ℕ) : decide ((n + 1) % 2 = 1) = !decide (n % 2 = 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [Nat.add_mod, h]

theorem alt_no_defect (h : alt lab s σ) : ∀ u v, ¬ Defect lab σ u v := by
  rintro u v ⟨hc, hpos⟩
  have hmi := alt_magInj h
  have hsucc := rk_succ_of_consec hmi hc
  have h1 := h.2.2 u hc.1
  have h2 := h.2.2 v hc.2.1
  rw [hsucc, decide_succ_mod_two] at h2
  rw [h1, h2] at hpos
  have hxor : ∀ (a b : Bool), xor a b ≠ xor a (!b) := by decide
  exact hxor s _ hpos

theorem altSet_of_alt (h : alt lab s σ) : AltSet lab σ :=
  ⟨alt_nz h, alt_magInj h, alt_no_defect h⟩

/-- Reconstruct the alternating pattern from the absence of defects. -/
theorem alt_of_altSet (h : AltSet lab σ) {v₀ : V} (hv₀ : v₀ ∈ σ) (hr₀ : rk lab σ v₀ = 0) :
    alt lab (pos lab v₀) σ := by
  obtain ⟨hnz, hmi, hnd⟩ := h
  refine ⟨hnz, hmi, ?_⟩
  have key : ∀ k : ℕ, ∀ v ∈ σ, rk lab σ v = k →
      pos lab v = xor (pos lab v₀) (decide (k % 2 = 1)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hrv
      match k with
      | 0 =>
        have : v = v₀ := rk_injOn hmi hv hv₀ (by rw [hrv, hr₀])
        subst this
        simp
      | (m + 1) =>
        have hlt : rk lab σ v < σ.card := rk_lt_card hv
        have hm : m < σ.card := by omega
        obtain ⟨u, hu, hru⟩ := rk_surj hmi hm
        have hc : Consec lab σ u v := consec_of_rk_succ hmi hu hv (by rw [hrv, hru])
        have hne : pos lab u ≠ pos lab v := fun h => hnd u v ⟨hc, h⟩
        have hiu := ih m (by omega) u hu hru
        have hv' : pos lab v = !(pos lab u) := by
          revert hne
          cases pos lab u <;> cases pos lab v <;> simp
        rw [hv', hiu, decide_succ_mod_two]
        rcases Bool.eq_false_or_eq_true (pos lab v₀) with h0 | h0 <;>
          rcases Bool.eq_false_or_eq_true (decide (m % 2 = 1)) with h1 | h1 <;>
          simp [h0, h1]
  intro v hv
  exact key (rk lab σ v) v hv rfl

theorem altSet_iff_exists_alt (hne : σ.Nonempty) :
    AltSet lab σ ↔ ∃ s, alt lab s σ := by
  constructor
  · intro h
    obtain ⟨v₀, hv₀, hr₀⟩ := exists_min h.2.1 hne
    exact ⟨pos lab v₀, alt_of_altSet h hv₀ hr₀⟩
  · rintro ⟨s, hs⟩
    exact altSet_of_alt hs

end Alt

section Erase

variable {lab : V → ℤ} {σ : Finset V} {s : Bool}

theorem Nz.subset' (h : Nz lab σ) {τ : Finset V} (hsub : τ ⊆ σ) : Nz lab τ :=
  fun v hv => h v (hsub hv)

theorem MagInj.subset' (h : MagInj lab σ) {τ : Finset V} (hsub : τ ⊆ σ) : MagInj lab τ :=
  fun u hu v hv huv => h u (hsub hu) v (hsub hv) huv

theorem rk_insert {x : V} (hx : x ∉ σ) (v : V) :
    rk lab (insert x σ) v = rk lab σ v + (if |lab x| < |lab v| then 1 else 0) := by
  rw [rk, rk, filter_insert]
  by_cases h : |lab x| < |lab v|
  · rw [if_pos h, if_pos h, card_insert_of_notMem (fun hcon => hx (mem_of_mem_filter _ hcon))]
  · rw [if_neg h, if_neg h]

theorem rk_erase_add {w : V} (hw : w ∈ σ) (v : V) :
    rk lab (σ.erase w) v + (if |lab w| < |lab v| then 1 else 0) = rk lab σ v := by
  have hfe : ((σ.erase w).filter (fun z => |lab z| < |lab v|)) =
      ((σ.filter (fun z => |lab z| < |lab v|)).erase w) := filter_erase _ _
  rw [rk, rk, hfe]
  by_cases h : |lab w| < |lab v|
  · have hmem : w ∈ σ.filter (fun z => |lab z| < |lab v|) := mem_filter.mpr ⟨hw, h⟩
    have hc : 0 < (σ.filter (fun z => |lab z| < |lab v|)).card := card_pos.mpr ⟨w, hmem⟩
    rw [if_pos h, card_erase_of_mem hmem]
    omega
  · have hnot : w ∉ σ.filter (fun z => |lab z| < |lab v|) := fun hcon =>
      h (mem_filter.mp hcon).2
    rw [if_neg h, erase_eq_of_notMem hnot]

theorem exists_pred {v : V} (hmi : MagInj lab σ) (hv : v ∈ σ) (hr : 0 < rk lab σ v) :
    ∃ u ∈ σ, Consec lab σ u v ∧ rk lab σ u + 1 = rk lab σ v := by
  obtain ⟨u, hu, hru⟩ := rk_surj hmi (k := rk lab σ v - 1)
    (lt_of_le_of_lt (Nat.sub_le _ _) (rk_lt_card hv))
  exact ⟨u, hu, consec_of_rk_succ hmi hu hv (by omega), by omega⟩

theorem exists_succ {v : V} (hmi : MagInj lab σ) (hv : v ∈ σ) (hr : rk lab σ v + 1 < σ.card) :
    ∃ y ∈ σ, Consec lab σ v y := by
  obtain ⟨y, hy, hry⟩ := rk_surj hmi hr
  exact ⟨y, hy, consec_of_rk_succ hmi hv hy (by omega)⟩

theorem no_pred_of_rk_zero {u v : V} (hmi : MagInj lab σ) (hr : rk lab σ v = 0)
    (h : Consec lab σ u v) : False := by
  have := rk_succ_of_consec hmi h
  omega

theorem no_succ_of_rk_top {v y : V} (hmi : MagInj lab σ) (hr : rk lab σ v + 1 = σ.card)
    (h : Consec lab σ v y) : False := by
  have h1 := rk_succ_of_consec hmi h
  have h2 := rk_lt_card (lab := lab) h.2.1
  omega

theorem consec_left_unique {u u' v : V} (hmi : MagInj lab σ) (h : Consec lab σ u v)
    (h' : Consec lab σ u' v) : u = u' := by
  have h1 := rk_succ_of_consec hmi h
  have h2 := rk_succ_of_consec hmi h'
  exact rk_injOn hmi h.1 h'.1 (by omega)

theorem consec_right_unique {u v v' : V} (hmi : MagInj lab σ) (h : Consec lab σ u v)
    (h' : Consec lab σ u v') : v = v' := by
  have h1 := rk_succ_of_consec hmi h
  have h2 := rk_succ_of_consec hmi h'
  exact rk_injOn hmi h.2.1 h'.2.1 (by omega)

theorem consec_erase_iff (hmi : MagInj lab σ) {w x y : V} (hw : w ∈ σ) (hx : x ∈ σ.erase w)
    (hy : y ∈ σ.erase w) :
    Consec lab (σ.erase w) x y ↔ (Consec lab σ x y ∨ (Consec lab σ x w ∧ Consec lab σ w y)) := by
  have hxσ : x ∈ σ := mem_of_mem_erase hx
  have hyσ : y ∈ σ := mem_of_mem_erase hy
  constructor
  · rintro ⟨-, -, hlt, hno⟩
    by_cases hbet : |lab x| < |lab w| ∧ |lab w| < |lab y|
    · refine Or.inr ⟨⟨hxσ, hw, hbet.1, ?_⟩, ⟨hw, hyσ, hbet.2, ?_⟩⟩
      · rintro z hz ⟨hz1, hz2⟩
        have hzw : z ≠ w := by
          rintro rfl
          exact lt_irrefl _ hz2
        exact hno z (mem_erase.mpr ⟨hzw, hz⟩) ⟨hz1, lt_trans hz2 hbet.2⟩
      · rintro z hz ⟨hz1, hz2⟩
        have hzw : z ≠ w := by
          rintro rfl
          exact lt_irrefl _ hz1
        exact hno z (mem_erase.mpr ⟨hzw, hz⟩) ⟨lt_trans hbet.1 hz1, hz2⟩
    · refine Or.inl ⟨hxσ, hyσ, hlt, ?_⟩
      rintro z hz ⟨h1, h2⟩
      by_cases hzw : z = w
      · subst hzw
        exact hbet ⟨h1, h2⟩
      · exact hno z (mem_erase.mpr ⟨hzw, hz⟩) ⟨h1, h2⟩
  · rintro (⟨-, -, hlt, hno⟩ | ⟨⟨-, -, h1, hno1⟩, ⟨-, -, h2, hno2⟩⟩)
    · exact ⟨hx, hy, hlt, fun z hz hzz => hno z (mem_of_mem_erase hz) hzz⟩
    · refine ⟨hx, hy, lt_trans h1 h2, ?_⟩
      rintro z hz ⟨hz1, hz2⟩
      have hzσ : z ∈ σ := mem_of_mem_erase hz
      have hzw : z ≠ w := (mem_erase.mp hz).1
      rcases lt_trichotomy (|lab z|) (|lab w|) with hc | hc | hc
      · exact hno1 z hzσ ⟨hz1, hc⟩
      · exact hzw (hmi z hzσ w hw hc)
      · exact hno2 z hzσ ⟨hc, hz2⟩

end Erase

end GaloisForLFunctions.BorsukUlam
