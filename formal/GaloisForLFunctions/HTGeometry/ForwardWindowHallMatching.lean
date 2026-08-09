import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# Forward-window matching collapses Hall's condition to intervals

For the one-sided equal-window relation `e < q ≤ e + H` between two finite sets of integers, the
exponentially large family of Hall subset inequalities is equivalent to the inequalities indexed
by consecutive integer intervals alone.

The nontrivial direction decomposes an arbitrary source subset at its window gaps: the largest
source point that has no successor within `H` splits the subset into two parts whose neighbour
sets are separated by that gap, and a gap-free subset has neighbour set exactly the single
interval `(min, max + H]`.

The file also records the sharp exponent threshold behind the loss of local information: an
exponent strictly below the exceptional saving and large enough to reach the interval transition
exists exactly above one quarter.
-/

namespace HTGeometry

/-! ## The forward window relation -/

/-- Targets reachable from the source point `e` through the one-sided window of length `H`. -/
def forwardWindow (T : Finset ℤ) (H e : ℤ) : Finset ℤ := T ∩ Finset.Ioc e (e + H)

theorem mem_forwardWindow {T : Finset ℤ} {H e q : ℤ} :
    q ∈ forwardWindow T H e ↔ q ∈ T ∧ e < q ∧ q ≤ e + H := by
  simp [forwardWindow, Finset.mem_inter, Finset.mem_Ioc]

/-- Hall's subset condition for the forward-window relation. -/
def ForwardWindowHallCondition (E T : Finset ℤ) (H : ℤ) : Prop :=
  ∀ s ⊆ E, s.card ≤ (s.biUnion (forwardWindow T H)).card

/-- The interval condition: every source interval is dominated by its shifted target window. -/
def ForwardWindowIntervalCondition (E T : Finset ℤ) (H : ℤ) : Prop :=
  ∀ a b : ℤ, (E ∩ Finset.Icc a b).card ≤ (T ∩ Finset.Ioc a (b + H)).card

/-- The matching statement: an injective forward assignment defined on the source set. -/
def HasForwardWindowMatching (E T : Finset ℤ) (H : ℤ) : Prop :=
  ∃ f : ℤ → ℤ, Set.InjOn f E ∧ ∀ e ∈ E, f e ∈ T ∧ e < f e ∧ f e ≤ e + H

/-! ## Necessity -/

theorem forwardWindowIntervalCondition_of_hasMatching
    {E T : Finset ℤ} {H : ℤ} (hm : HasForwardWindowMatching E T H) :
    ForwardWindowIntervalCondition E T H := by
  classical
  obtain ⟨f, hinj, hf⟩ := hm
  intro a b
  have hsub : (E ∩ Finset.Icc a b).image f ⊆ T ∩ Finset.Ioc a (b + H) := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨heE, heI⟩ := Finset.mem_inter.mp he
    obtain ⟨hab, hbb⟩ := Finset.mem_Icc.mp heI
    obtain ⟨hT, hlt, hle⟩ := hf e heE
    exact Finset.mem_inter.mpr ⟨hT, Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hab hlt,
      le_trans hle (by linarith)⟩⟩
  have hcard : ((E ∩ Finset.Icc a b).image f).card = (E ∩ Finset.Icc a b).card := by
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    exact hinj (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1 hxy
  calc (E ∩ Finset.Icc a b).card = ((E ∩ Finset.Icc a b).image f).card := hcard.symm
    _ ≤ (T ∩ Finset.Ioc a (b + H)).card := Finset.card_le_card hsub

/-! ## Sufficiency -/

/-- Source points after which the window relation has a gap: no other source point of `s` lies in
`(x, x + H]`, and `x` is not the largest point of `s`. -/
private def gapCut (s : Finset ℤ) (H b : ℤ) : Finset ℤ :=
  s.filter fun x => x < b ∧ ∀ y ∈ s, y ≤ x ∨ x + H < y

/-- A gap-free source subset has neighbour set exactly one interval. -/
private theorem inter_Ioc_subset_biUnion_forwardWindow
    {T s : Finset ℤ} {H : ℤ} (hne : s.Nonempty)
    (hgap : gapCut s H (s.max' hne) = ∅) :
    T ∩ Finset.Ioc (s.min' hne) (s.max' hne + H) ⊆ s.biUnion (forwardWindow T H) := by
  classical
  intro q hq
  obtain ⟨hqT, hqI⟩ := Finset.mem_inter.mp hq
  obtain ⟨hlt, hle⟩ := Finset.mem_Ioc.mp hqI
  set a := s.min' hne with ha
  set b := s.max' hne with hb
  have hPne : (s.filter fun x => x < q).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨s.min'_mem hne, hlt⟩⟩
  set e := (s.filter fun x => x < q).max' hPne with he
  have hemem : e ∈ s.filter fun x => x < q := Finset.max'_mem _ hPne
  have hes : e ∈ s := (Finset.mem_filter.mp hemem).1
  have heq : e < q := (Finset.mem_filter.mp hemem).2
  have hqle : q ≤ e + H := by
    by_contra hcon0
    have hcon : e + H < q := not_le.mp hcon0
    by_cases hEb : e = b
    · rw [hEb] at hcon; linarith
    · have heb : e < b := lt_of_le_of_ne (s.le_max' e hes) hEb
      have hnot : e ∉ gapCut s H b := by rw [hgap]; simp
      have hfail : ¬ (e < b ∧ ∀ y ∈ s, y ≤ e ∨ e + H < y) := by
        intro hh
        exact hnot (Finset.mem_filter.mpr ⟨hes, hh⟩)
      have hex : ∃ y ∈ s, e < y ∧ y ≤ e + H := by
        by_contra hno
        refine hfail ⟨heb, fun y hy => ?_⟩
        rcases le_or_gt y e with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          by_contra hle2
          exact hno ⟨y, hy, h, not_lt.mp hle2⟩
      obtain ⟨y, hy, hey, hyH⟩ := hex
      have hyq : y < q := lt_of_le_of_lt hyH hcon
      have : y ≤ e := Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hy, hyq⟩)
      linarith
  exact Finset.mem_biUnion.mpr ⟨e, hes, mem_forwardWindow.mpr ⟨hqT, heq, hqle⟩⟩

/-- **Interval sufficiency.**  The interval condition implies the full Hall subset condition. -/
theorem forwardWindowHallCondition_of_intervalCondition
    {E T : Finset ℤ} {H : ℤ} (hI : ForwardWindowIntervalCondition E T H) :
    ForwardWindowHallCondition E T H := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hsE
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    set b := s.max' hne with hb
    by_cases hcut : (gapCut s H b).Nonempty
    · set c := (gapCut s H b).max' hcut with hc
      have hcmem : c ∈ gapCut s H b := Finset.max'_mem _ hcut
      have hcs : c ∈ s := (Finset.mem_filter.mp hcmem).1
      have hcb : c < b := (Finset.mem_filter.mp hcmem).2.1
      have hcgap : ∀ y ∈ s, y ≤ c ∨ c + H < y := (Finset.mem_filter.mp hcmem).2.2
      set s₁ := s.filter fun x => x ≤ c with hs₁
      set s₂ := s.filter fun x => ¬ x ≤ c with hs₂
      have hs₁sub : s₁ ⊂ s := by
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro hcon
        have hbmem : b ∈ s₁ := hcon (s.max'_mem hne)
        have : b ≤ c := (Finset.mem_filter.mp hbmem).2
        linarith
      have hs₂sub : s₂ ⊂ s := by
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro hcon
        have hcmem₂ : c ∈ s₂ := hcon hcs
        exact absurd le_rfl (Finset.mem_filter.mp hcmem₂).2
      have hcards : s₁.card + s₂.card = s.card :=
        Finset.card_filter_add_card_filter_not _
      have hdisj : Disjoint (s₁.biUnion (forwardWindow T H))
          (s₂.biUnion (forwardWindow T H)) := by
        rw [Finset.disjoint_left]
        intro q hq₁ hq₂
        obtain ⟨e₁, he₁, hqe₁⟩ := Finset.mem_biUnion.mp hq₁
        obtain ⟨e₂, he₂, hqe₂⟩ := Finset.mem_biUnion.mp hq₂
        have h1 : e₁ ≤ c := (Finset.mem_filter.mp he₁).2
        have h2s : e₂ ∈ s := (Finset.mem_filter.mp he₂).1
        have h2 : ¬ e₂ ≤ c := (Finset.mem_filter.mp he₂).2
        have h2gap : c + H < e₂ := by
          rcases hcgap e₂ h2s with h | h
          · exact absurd h h2
          · exact h
        have hq1 : q ≤ e₁ + H := (mem_forwardWindow.mp hqe₁).2.2
        have hq2 : e₂ < q := (mem_forwardWindow.mp hqe₂).2.1
        linarith
      have hsplit : (s.filter fun x => x ≤ c) ∪ (s.filter fun x => ¬ x ≤ c) = s :=
        Finset.filter_union_filter_not_eq _ _
      have hunion : s.biUnion (forwardWindow T H) =
          s₁.biUnion (forwardWindow T H) ∪ s₂.biUnion (forwardWindow T H) := by
        rw [hs₁, hs₂, ← Finset.union_biUnion, hsplit]
      rw [← hcards, hunion, Finset.card_union_of_disjoint hdisj]
      exact Nat.add_le_add (ih s₁ hs₁sub (hs₁sub.1.trans hsE))
        (ih s₂ hs₂sub (hs₂sub.1.trans hsE))
    · have hgap : gapCut s H b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcut
      set a := s.min' hne with ha
      have hsub : s ⊆ E ∩ Finset.Icc a b := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hsE hx,
          Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩⟩
      calc s.card ≤ (E ∩ Finset.Icc a b).card := Finset.card_le_card hsub
        _ ≤ (T ∩ Finset.Ioc a (b + H)).card := hI a b
        _ ≤ (s.biUnion (forwardWindow T H)).card :=
            Finset.card_le_card (inter_Ioc_subset_biUnion_forwardWindow hne hgap)

/-! ## The matching equivalence -/

theorem hasForwardWindowMatching_of_hallCondition
    {E T : Finset ℤ} {H : ℤ} (hH : ForwardWindowHallCondition E T H) :
    HasForwardWindowMatching E T H := by
  classical
  have hall : ∀ s : Finset {x // x ∈ E},
      s.card ≤ (s.biUnion fun x => forwardWindow T H (x : ℤ)).card := by
    intro s
    have himg : (s.image Subtype.val).card = s.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hsub : (s.image Subtype.val) ⊆ E := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact y.2
    have hbi : (s.image Subtype.val).biUnion (forwardWindow T H) =
        s.biUnion fun x => forwardWindow T H (x : ℤ) := by
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, hq⟩
        exact ⟨y, hy, hq⟩
      · rintro ⟨y, hy, hq⟩
        exact ⟨(y : ℤ), ⟨y, hy, rfl⟩, hq⟩
    have := hH _ hsub
    rwa [himg, hbi] at this
  obtain ⟨g, hginj, hgmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x : {x // x ∈ E} => forwardWindow T H (x : ℤ))).mp hall
  refine ⟨fun z => if h : z ∈ E then g ⟨z, h⟩ else 0, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ E := hx
    have hy' : y ∈ E := hy
    simp only [dif_pos hx', dif_pos hy'] at hxy
    exact congrArg Subtype.val (hginj hxy)
  · intro e he
    have := mem_forwardWindow.mp (hgmem ⟨e, he⟩)
    simpa only [dif_pos he] using this

/-- **Forward-window Hall reduction.**  For the one-sided equal-window relation, an injective
forward assignment on `E` exists exactly when every consecutive integer interval satisfies the
shifted counting inequality. -/
theorem hasForwardWindowMatching_iff_intervalCondition (E T : Finset ℤ) (H : ℤ) :
    HasForwardWindowMatching E T H ↔ ForwardWindowIntervalCondition E T H :=
  ⟨forwardWindowIntervalCondition_of_hasMatching,
    fun hI => hasForwardWindowMatching_of_hallCondition
      (forwardWindowHallCondition_of_intervalCondition hI)⟩

/-- The exponentially many Hall subset inequalities collapse to the interval inequalities. -/
theorem forwardWindowHallCondition_iff_intervalCondition (E T : Finset ℤ) (H : ℤ) :
    ForwardWindowHallCondition E T H ↔ ForwardWindowIntervalCondition E T H :=
  ⟨fun hH => forwardWindowIntervalCondition_of_hasMatching
      (hasForwardWindowMatching_of_hallCondition hH),
    forwardWindowHallCondition_of_intervalCondition⟩

/-! ## The sharp quarter threshold -/

/-- Only the two trivial bounds are available from a global cardinality saving. -/
theorem card_inter_Icc_le_min (E : Finset ℤ) (a b : ℤ) :
    (E ∩ Finset.Icc a b).card ≤ min (Finset.Icc a b).card E.card := by
  classical
  exact le_min (Finset.card_le_card Finset.inter_subset_right)
    (Finset.card_le_card Finset.inter_subset_left)

/-- **Sharp quarter threshold.**  A window exponent that is strictly below the exceptional saving
and still reaches the small-interval/large-interval transition exists exactly when the saving
exceeds one quarter. -/
theorem exists_windowExponent_iff_quarter_lt (kappa : ℝ) :
    (∃ eta : ℝ, 0 < eta ∧ eta < kappa ∧ 1 / 2 ≤ eta + kappa) ↔ 1 / 4 < kappa := by
  constructor
  · rintro ⟨eta, hpos, hlt, hsum⟩
    linarith
  · intro hk
    exact ⟨1 / 4, by norm_num, hk, by linarith⟩

end HTGeometry
