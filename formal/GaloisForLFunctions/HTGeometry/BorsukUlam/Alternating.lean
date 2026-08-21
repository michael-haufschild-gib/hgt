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
set_option linter.unusedVariables false

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

theorem altSet_of_card_le_one (hnz : Nz lab σ) (h : σ.card ≤ 1) : AltSet lab σ := by
  refine ⟨hnz, fun u hu v hv _ => card_le_one.mp h u hu v hv, ?_⟩
  rintro u v ⟨hc, -⟩
  have huv : u = v := card_le_one.mp h u hc.1 v hc.2.1
  rw [huv] at hc
  exact lt_irrefl _ hc.2.2.1

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
    simp

theorem rk_erase_add {w : V} (hw : w ∈ σ) (v : V) :
    rk lab (σ.erase w) v + (if |lab w| < |lab v| then 1 else 0) = rk lab σ v := by
  have hfe : ((σ.erase w).filter (fun z => |lab z| < |lab v|)) =
      ((σ.filter (fun z => |lab z| < |lab v|)).erase w) := by
    rw [Finset.filter_erase]
  rw [rk, rk, hfe]
  by_cases h : |lab w| < |lab v|
  · have hmem : w ∈ σ.filter (fun z => |lab z| < |lab v|) := mem_filter.mpr ⟨hw, h⟩
    have hc : 0 < (σ.filter (fun z => |lab z| < |lab v|)).card := card_pos.mpr ⟨w, hmem⟩
    rw [if_pos h, card_erase_of_mem hmem]
    omega
  · have hnot : w ∉ σ.filter (fun z => |lab z| < |lab v|) := fun hcon =>
      h (mem_filter.mp hcon).2
    rw [if_neg h, erase_eq_of_notMem hnot]
    simp

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

theorem altSet_erase_iff (hnz : Nz lab σ) (hmi : MagInj lab σ) {w : V} (hw : w ∈ σ) :
    AltSet lab (σ.erase w) ↔
      ((∀ x y, Defect lab σ x y → x = w ∨ y = w) ∧
       (∀ x y, Consec lab σ x w → Consec lab σ w y → pos lab x ≠ pos lab y)) := by
  constructor
  · rintro ⟨-, -, hnd⟩
    constructor
    · rintro x y ⟨hc, hp⟩
      by_contra hcon
      push Not at hcon
      exact hnd x y ⟨(consec_erase_iff hmi hw (mem_erase.mpr ⟨hcon.1, hc.1⟩)
        (mem_erase.mpr ⟨hcon.2, hc.2.1⟩)).mpr (Or.inl hc), hp⟩
    · intro x y hxw hwy hp
      have hxe : x ∈ σ.erase w := mem_erase.mpr ⟨by rintro rfl; exact lt_irrefl _ hxw.2.2.1, hxw.1⟩
      have hye : y ∈ σ.erase w := mem_erase.mpr ⟨by rintro rfl; exact lt_irrefl _ hwy.2.2.1,
        hwy.2.1⟩
      exact hnd x y ⟨(consec_erase_iff hmi hw hxe hye).mpr (Or.inr ⟨hxw, hwy⟩), hp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hnz.subset' (erase_subset _ _), hmi.subset' (erase_subset _ _), ?_⟩
    rintro x y ⟨hc, hp⟩
    have hxe := hc.1
    have hye := hc.2.1
    rcases (consec_erase_iff hmi hw hxe hye).mp hc with hc' | ⟨hc1, hc2⟩
    · rcases h1 x y ⟨hc', hp⟩ with rfl | rfl
      · exact (mem_erase.mp hxe).1 rfl
      · exact (mem_erase.mp hye).1 rfl
    · exact h2 x y hc1 hc2 hp

theorem alt_sign_unique {s' : Bool} (hne : σ.Nonempty) (h1 : alt lab s σ) (h2 : alt lab s' σ) :
    s = s' := by
  obtain ⟨m, hm, hrm⟩ := exists_min (alt_magInj h1) hne
  rw [alt_sign_of_min h1 hm hrm, alt_sign_of_min h2 hm hrm]

/-- The minimum of `σ.erase w` when `w` is not itself the minimum. -/
theorem rk_erase_zero_of_ne_min (hmi : MagInj lab σ) {w m : V} (hw : w ∈ σ) (hm : m ∈ σ)
    (hrm : rk lab σ m = 0) (hne : m ≠ w) : m ∈ σ.erase w ∧ rk lab (σ.erase w) m = 0 := by
  refine ⟨mem_erase.mpr ⟨hne, hm⟩, ?_⟩
  have h := rk_erase_add (lab := lab) hw m
  omega

/-- The minimum of `σ.erase w` when `w` is the minimum: it is the successor of `w`. -/
theorem rk_erase_zero_of_min (hmi : MagInj lab σ) {w y : V} (hw : w ∈ σ) (hy : y ∈ σ)
    (hrw : rk lab σ w = 0) (hry : rk lab σ y = 1) : y ∈ σ.erase w ∧ rk lab (σ.erase w) y = 0 := by
  have hne : y ≠ w := by
    intro hcon
    rw [hcon] at hry
    omega
  refine ⟨mem_erase.mpr ⟨hne, hy⟩, ?_⟩
  have hlt : |lab w| < |lab y| := mag_lt_of_rk_lt hmi hw hy (by omega)
  have h := rk_erase_add (lab := lab) hw y
  rw [if_pos hlt] at h
  omega

theorem altSet_erase_iff_of_altSet (h : AltSet lab σ) {w : V} (hw : w ∈ σ) :
    AltSet lab (σ.erase w) ↔ (rk lab σ w = 0 ∨ rk lab σ w + 1 = σ.card) := by
  obtain ⟨hnz, hmi, hnd⟩ := h
  rw [altSet_erase_iff hnz hmi hw]
  constructor
  · rintro ⟨-, h2⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hzero, htop⟩ := hcon
    obtain ⟨x, hx, hcx, -⟩ := exists_pred hmi hw (Nat.pos_of_ne_zero hzero)
    have hlt : rk lab σ w + 1 < σ.card := by
      have := rk_lt_card (lab := lab) hw
      omega
    obtain ⟨y, hy, hcy⟩ := exists_succ hmi hw hlt
    have hxw : pos lab x ≠ pos lab w := fun hp => hnd x w ⟨hcx, hp⟩
    have hwy : pos lab w ≠ pos lab y := fun hp => hnd w y ⟨hcy, hp⟩
    refine h2 x y hcx hcy ?_
    revert hxw hwy
    cases pos lab x <;> cases pos lab w <;> cases pos lab y <;> simp
  · intro hcase
    refine ⟨fun x y hd => absurd hd (hnd x y), ?_⟩
    intro x y hxw hwy hp
    rcases hcase with h0 | h1
    · exact no_pred_of_rk_zero hmi h0 hxw
    · exact no_succ_of_rk_top hmi h1 hwy

theorem alt_erase_max (h : alt lab s σ) (hcard : 2 ≤ σ.card) {w : V} (hw : w ∈ σ)
    (hrw : rk lab σ w + 1 = σ.card) : alt lab s (σ.erase w) := by
  have hAS : AltSet lab (σ.erase w) :=
    (altSet_erase_iff_of_altSet (altSet_of_alt h) hw).mpr (Or.inr hrw)
  obtain ⟨m, hm, hrm⟩ := exists_min (alt_magInj h) ⟨w, hw⟩
  have hne : m ≠ w := by
    rintro rfl
    omega
  obtain ⟨hme, hrme⟩ := rk_erase_zero_of_ne_min (alt_magInj h) hw hm hrm hne
  have hgot := alt_of_altSet hAS hme hrme
  rwa [← alt_sign_of_min h hm hrm] at hgot

theorem alt_erase_min (h : alt lab s σ) (hcard : 2 ≤ σ.card) {w : V} (hw : w ∈ σ)
    (hrw : rk lab σ w = 0) : alt lab (!s) (σ.erase w) := by
  have hAS : AltSet lab (σ.erase w) :=
    (altSet_erase_iff_of_altSet (altSet_of_alt h) hw).mpr (Or.inl hrw)
  obtain ⟨y, hy, hry⟩ := rk_surj (alt_magInj h) (show 1 < σ.card by omega)
  obtain ⟨hye, hrye⟩ := rk_erase_zero_of_min (alt_magInj h) hw hy hrw hry
  have h1 := alt_of_altSet hAS hye hrye
  have h2 : pos lab y = !s := by
    have hh := h.2.2 y hy
    rw [hry] at hh
    simpa using hh
  rwa [h2] at h1

theorem alt_erase_cases (h : alt lab s σ) (hcard : 2 ≤ σ.card) {ε : Bool} {v : V}
    (hv : v ∈ σ) (hav : alt lab ε (σ.erase v)) :
    (ε = s ∧ rk lab σ v + 1 = σ.card) ∨ (ε = !s ∧ rk lab σ v = 0) := by
  have hne : (σ.erase v).Nonempty := by
    rw [← card_pos, card_erase_of_mem hv]
    omega
  rcases (altSet_erase_iff_of_altSet (altSet_of_alt h) hv).mp (altSet_of_alt hav) with h0 | h1
  · exact Or.inr ⟨alt_sign_unique hne hav (alt_erase_min h hcard hv h0), h0⟩
  · exact Or.inl ⟨alt_sign_unique hne hav (alt_erase_max h hcard hv h1), h1⟩

/-- An alternating set with at least two elements has, for each sign, exactly one vertex whose
removal leaves an alternating set of that sign. -/
theorem exists_unique_alt_erase_of_alt (h : alt lab s σ) (hcard : 2 ≤ σ.card) (ε : Bool) :
    ∃ a ∈ σ, alt lab ε (σ.erase a) ∧ ∀ v ∈ σ, alt lab ε (σ.erase v) → v = a := by
  have hmi := alt_magInj h
  rcases Bool.eq_or_eq_not ε s with rfl | rfl
  · obtain ⟨a, ha, hra⟩ := rk_surj hmi (show σ.card - 1 < σ.card by omega)
    have hra' : rk lab σ a + 1 = σ.card := by omega
    refine ⟨a, ha, alt_erase_max h hcard ha hra', ?_⟩
    intro v hv hav
    rcases alt_erase_cases h hcard hv hav with ⟨-, hv1⟩ | ⟨hcon, -⟩
    · exact rk_injOn hmi hv ha (by omega)
    · simp at hcon
  · obtain ⟨a, ha, hra⟩ := rk_surj hmi (show 0 < σ.card by omega)
    refine ⟨a, ha, alt_erase_min h hcard ha hra, ?_⟩
    intro v hv hav
    rcases alt_erase_cases h hcard hv hav with ⟨hcon, -⟩ | ⟨-, hv0⟩
    · simp at hcon
    · exact rk_injOn hmi hv ha (by omega)

end Erase

section AlmostAlt

variable {lab : V → ℤ} {σ : Finset V} {s : Bool}

/-- Two vertices carrying the same label may be exchanged without affecting alternation. -/
theorem alt_insert_congr {C : Finset V} {x y : V} (hx : x ∉ C) (hy : y ∉ C)
    (hlab : lab x = lab y) (h : alt lab s (insert x C)) : alt lab s (insert y C) := by
  obtain ⟨hnz, hmi, hsg⟩ := h
  have hmag : |lab x| = |lab y| := by rw [hlab]
  have hrkC : ∀ v : V, rk lab (insert y C) v = rk lab (insert x C) v := by
    intro v
    rw [rk_insert hx, rk_insert hy, hmag]
  have hrkxy : rk lab (insert y C) y = rk lab (insert x C) x := by
    rw [hrkC, rk_insert hx, rk_insert hx]
    simp only [rk, hmag]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv'
    · rw [← hlab]
      exact hnz x (mem_insert_self _ _)
    · exact hnz v (mem_insert_of_mem hv')
  · intro u hu v hv huv
    rcases mem_insert.mp hu with rfl | hu' <;> rcases mem_insert.mp hv with rfl | hv'
    · rfl
    · exact absurd (hmi x (mem_insert_self _ _) v (mem_insert_of_mem hv')
        (by rw [hmag]; exact huv)) (by rintro rfl; exact hx hv')
    · exact absurd (hmi u (mem_insert_of_mem hu') x (mem_insert_self _ _)
        (by rw [hmag]; exact huv)) (by rintro rfl; exact hx hu')
    · exact hmi u (mem_insert_of_mem hu') v (mem_insert_of_mem hv') huv
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv'
    · have hposeq : pos lab v = pos lab x := by simp [pos, hlab]
      rw [hrkxy, hposeq]
      exact hsg x (mem_insert_self _ _)
    · rw [hrkC]
      exact hsg v (mem_insert_of_mem hv')

/-- Repeated-label case: if two distinct vertices of `σ` carry the same label and removing one of
them leaves an alternating set, then exactly those two removals work, with the same sign. -/
theorem alt_erase_repeat {x y : V} (hx : x ∈ σ) (hy : y ∈ σ) (hxy : x ≠ y)
    (hlab : lab x = lab y) (hax : alt lab s (σ.erase x)) :
    alt lab s (σ.erase y) ∧
      ∀ v ∈ σ, ∀ ε : Bool, alt lab ε (σ.erase v) → (v = x ∨ v = y) ∧ ε = s := by
  set C : Finset V := (σ.erase x).erase y with hC
  have hyC : y ∉ C := notMem_erase _ _
  have hxC : x ∉ C := fun hcon => (notMem_erase x σ) (mem_of_mem_erase hcon)
  have hex : σ.erase x = insert y C := by
    rw [hC, insert_erase (mem_erase.mpr ⟨Ne.symm hxy, hy⟩)]
  have hey : σ.erase y = insert x C := by
    rw [hC]
    ext z
    simp only [mem_insert, mem_erase]
    constructor
    · rintro ⟨hzy, hzσ⟩
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr ⟨hzy, hzx, hzσ⟩
    · rintro (rfl | ⟨hzy, hzx, hzσ⟩)
      · exact ⟨hxy, hx⟩
      · exact ⟨hzy, hzσ⟩
  have hay : alt lab s (σ.erase y) := by
    rw [hey]
    rw [hex] at hax
    exact alt_insert_congr hyC hxC hlab.symm hax
  refine ⟨hay, ?_⟩
  intro v hv ε hav
  have hvxy : v = x ∨ v = y := by
    by_contra hcon
    push Not at hcon
    have hxe : x ∈ σ.erase v := mem_erase.mpr ⟨fun hcc => hcon.1 hcc.symm, hx⟩
    have hye : y ∈ σ.erase v := mem_erase.mpr ⟨fun hcc => hcon.2 hcc.symm, hy⟩
    exact hxy (alt_magInj hav x hxe y hye (by rw [hlab]))
  refine ⟨hvxy, ?_⟩
  rcases hvxy with rfl | rfl
  · exact alt_sign_unique (by rw [hex]; exact ⟨y, mem_insert_self _ _⟩) hav hax
  · exact alt_sign_unique (by rw [hey]; exact ⟨x, mem_insert_self _ _⟩) hav hay

/-- Distinct-magnitude case: a non-alternating set with an alternating facet has exactly two
alternating facets, obtained by deleting the two ends of its unique defect, and both have the
same sign. -/
theorem alt_erase_defect (hnz : Nz lab σ) (hmi : MagInj lab σ) (hnotAlt : ¬ AltSet lab σ)
    {u : V} (hu : u ∈ σ) (hau : alt lab s (σ.erase u)) :
    ∃ a ∈ σ, ∃ b ∈ σ, a ≠ b ∧ alt lab s (σ.erase a) ∧ alt lab s (σ.erase b) ∧
      ∀ v ∈ σ, ∀ ε : Bool, alt lab ε (σ.erase v) → (v = a ∨ v = b) ∧ ε = s := by
  have hexdef : ∃ x y, Defect lab σ x y := by
    by_contra hcon
    push Not at hcon
    exact hnotAlt ⟨hnz, hmi, fun x y => hcon x y⟩
  obtain ⟨d₁, d₂, hd⟩ := hexdef
  obtain ⟨hall, hbridge⟩ := (altSet_erase_iff hnz hmi hu).mp (altSet_of_alt hau)
  have hdef2 : ∀ x y x' y', Defect lab σ x y → Defect lab σ x' y' → x = x' ∧ y = y' := by
    intro x y x' y' h1 h2
    rcases hall x y h1 with hxu | hyu <;> rcases hall x' y' h2 with hxu' | hyu'
    · refine ⟨by rw [hxu, hxu'], ?_⟩
      refine consec_right_unique hmi (u := u) ?_ ?_
      · rw [← hxu]; exact h1.1
      · rw [← hxu']; exact h2.1
    · exfalso
      refine hbridge x' y ?_ ?_ ?_
      · rw [← hyu']; exact h2.1
      · rw [← hxu]; exact h1.1
      · rw [h2.2, hyu', ← hxu, h1.2]
    · exfalso
      refine hbridge x y' ?_ ?_ ?_
      · rw [← hyu]; exact h1.1
      · rw [← hxu']; exact h2.1
      · rw [h1.2, hyu, ← hxu', h2.2]
    · refine ⟨?_, by rw [hyu, hyu']⟩
      refine consec_left_unique hmi (v := u) ?_ ?_
      · rw [← hyu]; exact h1.1
      · rw [← hyu']; exact h2.1
  have huniq : ∀ x y, Defect lab σ x y → x = d₁ ∧ y = d₂ := fun x y h => hdef2 x y d₁ d₂ h hd
  have hd1σ : d₁ ∈ σ := hd.1.1
  have hd2σ : d₂ ∈ σ := hd.1.2.1
  have hd12 : d₁ ≠ d₂ := by
    intro hcon
    rw [hcon] at hd
    exact lt_irrefl _ hd.1.2.2.1
  have hrk12 : rk lab σ d₂ = rk lab σ d₁ + 1 := rk_succ_of_consec hmi hd.1
  have hne1 : (σ.erase d₁).Nonempty := ⟨d₂, mem_erase.mpr ⟨Ne.symm hd12, hd2σ⟩⟩
  have hne2 : (σ.erase d₂).Nonempty := ⟨d₁, mem_erase.mpr ⟨hd12, hd1σ⟩⟩
  have hAS1 : AltSet lab (σ.erase d₁) := by
    rw [altSet_erase_iff hnz hmi hd1σ]
    refine ⟨fun x y hxy => Or.inl (huniq x y hxy).1, ?_⟩
    intro x y hx hy hp
    have hy2 : y = d₂ := consec_right_unique hmi hy hd.1
    have hnd : ¬ Defect lab σ x d₁ := by
      intro hcon
      exact hd12 (huniq x d₁ hcon).2
    have hxd : pos lab x ≠ pos lab d₁ := fun hpp => hnd ⟨hx, hpp⟩
    rw [hy2, ← hd.2] at hp
    exact hxd hp
  have hAS2 : AltSet lab (σ.erase d₂) := by
    rw [altSet_erase_iff hnz hmi hd2σ]
    refine ⟨fun x y hxy => Or.inr (huniq x y hxy).2, ?_⟩
    intro x y hx hy hp
    have hx1 : x = d₁ := consec_left_unique hmi hx hd.1
    have hnd : ¬ Defect lab σ d₂ y := by
      intro hcon
      exact hd12 (huniq d₂ y hcon).1.symm
    have hyd : pos lab d₂ ≠ pos lab y := fun hpp => hnd ⟨hy, hpp⟩
    rw [hx1, hd.2] at hp
    exact hyd hp
  obtain ⟨m, hm, hrm⟩ := exists_min hmi ⟨d₁, hd1σ⟩
  have hd2m : d₂ ≠ m := by
    intro hcon
    rw [hcon, hrm] at hrk12
    omega
  have hsign2 : alt lab (pos lab m) (σ.erase d₂) := by
    obtain ⟨hme, hrme⟩ := rk_erase_zero_of_ne_min hmi hd2σ hm hrm (Ne.symm hd2m)
    exact alt_of_altSet hAS2 hme hrme
  have hsign1 : alt lab (pos lab m) (σ.erase d₁) := by
    by_cases hcase : d₁ = m
    · have hrk2 : rk lab σ d₂ = 1 := by rw [hrk12, hcase, hrm]
      obtain ⟨hme, hrme⟩ := rk_erase_zero_of_min hmi hd1σ hd2σ (by rw [hcase]; exact hrm) hrk2
      have hgot := alt_of_altSet hAS1 hme hrme
      rw [← hd.2] at hgot
      rw [← hcase]
      exact hgot
    · obtain ⟨hme, hrme⟩ := rk_erase_zero_of_ne_min hmi hd1σ hm hrm (fun hcc => hcase hcc.symm)
      exact alt_of_altSet hAS1 hme hrme
  have hsm : s = pos lab m := by
    rcases hall d₁ d₂ hd with h1 | h2
    · rw [← h1] at hau
      exact alt_sign_unique hne1 hau hsign1
    · rw [← h2] at hau
      exact alt_sign_unique hne2 hau hsign2
  subst hsm
  refine ⟨d₁, hd1σ, d₂, hd2σ, hd12, hsign1, hsign2, ?_⟩
  intro v hv ε hav
  obtain ⟨hallv, -⟩ := (altSet_erase_iff hnz hmi hv).mp (altSet_of_alt hav)
  have hvd : v = d₁ ∨ v = d₂ := by
    rcases hallv d₁ d₂ hd with h1 | h2
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  refine ⟨hvd, ?_⟩
  rcases hvd with rfl | rfl
  · exact alt_sign_unique hne1 hav hsign1
  · exact alt_sign_unique hne2 hav hsign2

/-- `σ` is almost-alternating with sign `s`: not alternating, but some facet is alternating with
sign `s`. -/
def almostAlt (lab : V → ℤ) (s : Bool) (σ : Finset V) : Prop :=
  ¬ AltSet lab σ ∧ ∃ v ∈ σ, alt lab s (σ.erase v)

/-- **Two facets.**  An almost-alternating set without a complementary pair of labels has exactly
two alternating facets, and both carry its sign. -/
theorem exists_pair_alt_erase_of_almostAlt (hnz : Nz lab σ)
    (hcompl : ∀ x ∈ σ, ∀ y ∈ σ, lab x + lab y ≠ 0) (h : almostAlt lab s σ) :
    ∃ a ∈ σ, ∃ b ∈ σ, a ≠ b ∧ alt lab s (σ.erase a) ∧ alt lab s (σ.erase b) ∧
      ∀ v ∈ σ, ∀ ε : Bool, alt lab ε (σ.erase v) → (v = a ∨ v = b) ∧ ε = s := by
  obtain ⟨hnotAlt, u, hu, hau⟩ := h
  by_cases hmi : MagInj lab σ
  · exact alt_erase_defect hnz hmi hnotAlt hu hau
  · rw [MagInj] at hmi
    push Not at hmi
    obtain ⟨x, hx, y, hy, hmag, hxy⟩ := hmi
    have hlab : lab x = lab y := by
      rcases abs_eq_abs.mp hmag with hcase | hcase
      · exact hcase
      · exact absurd (by rw [hcase]; ring) (hcompl x hx y hy)
    have huxy : u = x ∨ u = y := by
      by_contra hcon
      push Not at hcon
      have hxe : x ∈ σ.erase u := mem_erase.mpr ⟨fun hcc => hcon.1 hcc.symm, hx⟩
      have hye : y ∈ σ.erase u := mem_erase.mpr ⟨fun hcc => hcon.2 hcc.symm, hy⟩
      exact hxy (alt_magInj hau x hxe y hye hmag)
    rcases huxy with rfl | rfl
    · obtain ⟨hay, huniq⟩ := alt_erase_repeat hu hy hxy hlab hau
      exact ⟨u, hu, y, hy, hxy, hau, hay, huniq⟩
    · obtain ⟨hax, huniq⟩ := alt_erase_repeat hu hx (Ne.symm hxy) hlab.symm hau
      refine ⟨u, hu, x, hx, Ne.symm hxy, hau, hax, ?_⟩
      intro v hv ε hav
      obtain ⟨hor, hε⟩ := huniq v hv ε hav
      exact ⟨hor, hε⟩

/-- Adding one vertex to an alternating set gives an alternating or an almost-alternating set. -/
theorem altSet_or_almostAlt {τ : Finset V} {v : V} (hv : v ∈ τ) (h : alt lab s (τ.erase v)) :
    AltSet lab τ ∨ almostAlt lab s τ := by
  by_cases hcase : AltSet lab τ
  · exact Or.inl hcase
  · exact Or.inr ⟨hcase, v, hv, h⟩

/-- An alternating set whose labels have absolute value at most `n` has at most `n` elements. -/
theorem alt_card_le {n : ℕ} (h : alt lab s σ) (hb : ∀ v ∈ σ, |lab v| ≤ (n : ℤ)) :
    σ.card ≤ n := by
  have hmaps : ∀ v ∈ σ, (|lab v|).toNat ∈ Finset.Icc 1 n := by
    intro v hv
    have h0 : lab v ≠ 0 := h.1 v hv
    have h1 : 1 ≤ |lab v| := by
      rcases lt_trichotomy (lab v) 0 with hc | hc | hc
      · rw [abs_of_neg hc]; omega
      · exact absurd hc h0
      · rw [abs_of_pos hc]; omega
    have h2 := hb v hv
    simp only [Finset.mem_Icc]
    omega
  have hinj : ∀ u ∈ σ, ∀ v ∈ σ, (|lab u|).toNat = (|lab v|).toNat → u = v := by
    intro u hu v hv huv
    refine h.2.1 u hu v hv ?_
    have h1 : 0 ≤ |lab u| := abs_nonneg _
    have h2 : 0 ≤ |lab v| := abs_nonneg _
    omega
  have := Finset.card_le_card_of_injOn (fun v => (|lab v|).toNat) hmaps hinj
  simpa using this

/-- Alternation transported along a label-negating injection, with the sign flipped. -/
theorem alt_image_neg {ν : V → V} (hν : Function.Injective ν) (hlab : ∀ v, lab (ν v) = -(lab v))
    (h : alt lab s σ) : alt lab (!s) (σ.image ν) := by
  obtain ⟨hnz, hmi, hsg⟩ := h
  have habs : ∀ v, |lab (ν v)| = |lab v| := by
    intro v
    rw [hlab, abs_neg]
  have hrk : ∀ v : V, rk lab (σ.image ν) (ν v) = rk lab σ v := by
    intro v
    have himg : (σ.image ν).filter (fun w => |lab w| < |lab (ν v)|) =
        (σ.filter (fun w => |lab w| < |lab v|)).image ν := by
      ext z
      constructor
      · intro hz
        rw [mem_filter] at hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz.1
        have h2 := hz.2
        rw [habs, habs] at h2
        exact mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, h2⟩, rfl⟩
      · intro hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
        rw [mem_filter] at hw
        refine mem_filter.mpr ⟨mem_image.mpr ⟨w, hw.1, rfl⟩, ?_⟩
        rw [habs, habs]
        exact hw.2
    rw [rk, rk, himg, card_image_of_injective _ hν]
  refine ⟨?_, ?_, ?_⟩
  · rintro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    rw [hlab]
    simpa using hnz w hw
  · rintro z hz z' hz' hzz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨w', hw', rfl⟩ := mem_image.mp hz'
    rw [habs, habs] at hzz
    rw [hmi w hw w' hw' hzz]
  · rintro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hposneg : pos lab (ν w) = !(pos lab w) := by
      have h0 : lab w ≠ 0 := hnz w hw
      simp only [pos, hlab]
      rcases lt_trichotomy (lab w) 0 with hc | hc | hc
      · simp [hc, not_lt.mpr (le_of_lt hc)]
      · exact absurd hc h0
      · simp [hc, not_lt.mpr (le_of_lt hc)]
    rw [hposneg, hrk, hsg w hw]
    rcases Bool.eq_false_or_eq_true s with rfl | rfl <;>
      rcases Bool.eq_false_or_eq_true (decide (rk lab σ w % 2 = 1)) with h1 | h1 <;> simp [h1]

end AlmostAlt

end GaloisForLFunctions.BorsukUlam
