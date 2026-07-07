/-
The two-phase staircase descent: joint subset-sum steering of a planar walk.

Finite pools of planar steps confined to sign quadrants, with a per-step magnitude
floor `f` on each coordinate and a common ceiling `δ`, drive a pair of deficits into a
`δ`-box.  The order of operations is the content: alternating corrections diverge —
returning an exited coordinate to its band disturbs the other by up to `δ`, which
costs at least `δ/f ≥ 1` further corrections, a non-contracting cascade.  The repair
is that BOTH quadrant pools of a needed half-plane advance the driven coordinate by at
least `f`, differing only in the direction of the other coordinate.  So one descends
the first deficit monotonically while choosing, at each step, the pool whose second
coordinate keeps the second deficit banded, and then repeats with the coordinates
exchanged: two monotone descents, no cascade, final tolerance one ceiling per
coordinate.
-/
import GaloisForLFunctions.RHTower.WindowBudget

noncomputable section

namespace RHTower

open Finset

/-- **The single-phase descent**: from two disjoint pools whose steps have the driven
coordinate in `[f, δ]` and the banded coordinate in `[f, δ]` (pool `A`) or `[−δ, −f]`
(pool `B`), any deficit `dU ≤ n·f + δ` is driven into `(−δ, δ]` using at most `n`
steps in total, while the banded deficit never leaves `(−δ, max D δ]`: when the banded
deficit is positive one draws from `A` (it descends), otherwise from `B` (it ascends
by at most one ceiling, staying below `δ`). -/
theorem staircase_drive {u v : ℕ → ℝ} {f δ : ℝ} (hf : 0 < f) (hfδ : f ≤ δ) :
    ∀ (n : ℕ) (A B : Finset ℕ), Disjoint A B →
      (∀ q ∈ A, f ≤ u q ∧ u q ≤ δ ∧ f ≤ v q ∧ v q ≤ δ) →
      (∀ q ∈ B, f ≤ u q ∧ u q ≤ δ ∧ -δ ≤ v q ∧ v q ≤ -f) →
      ∀ (dU dV D : ℝ), -δ < dU → dU ≤ n * f + δ → -δ < dV → dV ≤ max D δ →
      n ≤ A.card → n ≤ B.card →
      ∃ S : Finset ℕ, S ⊆ A ∪ B ∧ S.card ≤ n ∧
        -δ < dU - ∑ q ∈ S, u q ∧ dU - ∑ q ∈ S, u q ≤ δ ∧
        -δ < dV - ∑ q ∈ S, v q ∧ dV - ∑ q ∈ S, v q ≤ max D δ := by
  intro n
  induction n with
  | zero =>
    intro A B _ _ _ dU dV D hdU0 hdU1 hdV0 hdV1 _ _
    have h1 : dU ≤ δ := by push_cast at hdU1; linarith
    exact ⟨∅, empty_subset _, le_rfl, by simpa using hdU0, by simpa using h1,
      by simpa using hdV0, by simpa using hdV1⟩
  | succ n ih =>
    intro A B hdisj hA hB dU dV D hdU0 hdU1 hdV0 hdV1 hcardA hcardB
    have hδ : (0 : ℝ) < δ := lt_of_lt_of_le hf hfδ
    by_cases hstop : dU ≤ δ
    · exact ⟨∅, empty_subset _, by simp, by simpa using hdU0, by simpa using hstop,
        by simpa using hdV0, by simpa using hdV1⟩
    have hstop' : δ < dU := lt_of_not_ge hstop
    by_cases hside : 0 < dV
    · -- the banded deficit is positive: draw from the pool that descends it
      have hAne : A.Nonempty := card_pos.mp (lt_of_lt_of_le (Nat.succ_pos n) hcardA)
      obtain ⟨a, ha⟩ := hAne
      obtain ⟨hau1, hau2, hav1, hav2⟩ := hA a ha
      obtain ⟨S', hS'sub, hS'card, h1, h2, h3, h4⟩ :=
        ih (A.erase a) B (hdisj.mono_left (erase_subset _ _))
          (fun q hq => hA q (mem_of_mem_erase hq)) hB
          (dU - u a) (dV - v a) D
          (by linarith) (by push_cast at hdU1 ⊢; linarith)
          (by linarith) (by linarith)
          (by rw [card_erase_of_mem ha]; omega) (le_trans (Nat.le_succ n) hcardB)
      have haS' : a ∉ S' := by
        intro hmem
        rcases mem_union.mp (hS'sub hmem) with h | h
        · exact notMem_erase a A h
        · exact disjoint_left.mp hdisj ha h
      refine ⟨insert a S', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx'
        · exact mem_union_left _ ha
        · rcases mem_union.mp (hS'sub hx') with h | h
          · exact mem_union_left _ (mem_of_mem_erase h)
          · exact mem_union_right _ h
      · rw [card_insert_of_notMem haS']; omega
      · rw [sum_insert haS']; linarith
      · rw [sum_insert haS']; linarith
      · rw [sum_insert haS']; linarith
      · rw [sum_insert haS']; linarith
    · -- the banded deficit is nonpositive: draw from the pool that ascends it
      have hside' : dV ≤ 0 := le_of_not_gt hside
      have hBne : B.Nonempty := card_pos.mp (lt_of_lt_of_le (Nat.succ_pos n) hcardB)
      obtain ⟨b, hb⟩ := hBne
      obtain ⟨hbu1, hbu2, hbv1, hbv2⟩ := hB b hb
      obtain ⟨S', hS'sub, hS'card, h1, h2, h3, h4⟩ :=
        ih A (B.erase b) (hdisj.mono_right (erase_subset _ _)) hA
          (fun q hq => hB q (mem_of_mem_erase hq))
          (dU - u b) (dV - v b) D
          (by linarith) (by push_cast at hdU1 ⊢; linarith)
          (by linarith) (by
            have hmax : δ ≤ max D δ := le_max_right D δ
            linarith)
          (le_trans (Nat.le_succ n) hcardA) (by rw [card_erase_of_mem hb]; omega)
      have hbS' : b ∉ S' := by
        intro hmem
        rcases mem_union.mp (hS'sub hmem) with h | h
        · exact disjoint_left.mp hdisj h hb
        · exact notMem_erase b B h
      refine ⟨insert b S', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx'
        · exact mem_union_right _ hb
        · rcases mem_union.mp (hS'sub hx') with h | h
          · exact mem_union_left _ h
          · exact mem_union_right _ (mem_of_mem_erase h)
      · rw [card_insert_of_notMem hbS']; omega
      · rw [sum_insert hbS']; linarith
      · rw [sum_insert hbS']; linarith
      · rw [sum_insert hbS']; linarith
      · rw [sum_insert hbS']; linarith

/-- **The two-phase staircase**: three disjoint quadrant pools with floor `f` and
ceiling `δ` — both coordinates up, first up second down, first down second up — steer
a pair of nonnegative deficits into the `δ`-box simultaneously.  Phase one drives the
first deficit against the two first-coordinate-positive pools, keeping the second
banded; phase two drives the second deficit against the remainder of the doubly
positive pool and the second-coordinate-positive pool, keeping the first — already in
its band — banded.  The pool budgets are counts against `f`, not masses. -/
theorem staircase_reach_nonneg {u v : ℕ → ℝ} {f δ : ℝ} (hf : 0 < f) (hfδ : f ≤ δ)
    {App ApM AMp : Finset ℕ}
    (hd1 : Disjoint App ApM) (hd2 : Disjoint App AMp) (hd3 : Disjoint ApM AMp)
    (hApp : ∀ q ∈ App, f ≤ u q ∧ u q ≤ δ ∧ f ≤ v q ∧ v q ≤ δ)
    (hApM : ∀ q ∈ ApM, f ≤ u q ∧ u q ≤ δ ∧ -δ ≤ v q ∧ v q ≤ -f)
    (hAMp : ∀ q ∈ AMp, -δ ≤ u q ∧ u q ≤ -f ∧ f ≤ v q ∧ v q ≤ δ)
    {Tp Tm : ℝ} (hTp : 0 ≤ Tp) (hTm : 0 ≤ Tm)
    {n₁ n₂ : ℕ} (hn₁ : Tp ≤ n₁ * f + δ) (hn₂ : max Tm δ ≤ n₂ * f + δ)
    (hc1 : n₁ + n₂ ≤ App.card) (hc2 : n₁ ≤ ApM.card) (hc3 : n₂ ≤ AMp.card) :
    ∃ S : Finset ℕ, S ⊆ App ∪ ApM ∪ AMp ∧
      |Tp - ∑ q ∈ S, u q| ≤ δ ∧ |Tm - ∑ q ∈ S, v q| ≤ δ := by
  have hδ : (0 : ℝ) < δ := lt_of_lt_of_le hf hfδ
  obtain ⟨S₁, hS₁sub, hS₁card, hU1a, hU1b, hV1a, hV1b⟩ :=
    staircase_drive hf hfδ n₁ App ApM hd1 hApp hApM Tp Tm Tm
      (by linarith) hn₁ (by linarith) (le_max_left _ _)
      (le_trans (Nat.le_add_right n₁ n₂) hc1) hc2
  have hcardApp : n₂ ≤ (App \ S₁).card := by
    have h := card_le_card_sdiff_add_card (s := App) (t := S₁)
    omega
  obtain ⟨S₂, hS₂sub, hS₂card, hV2a, hV2b, hU2a, hU2b⟩ :=
    staircase_drive (u := v) (v := u) hf hfδ n₂ (App \ S₁) AMp
      (hd2.mono_left sdiff_subset)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := hApp q (mem_sdiff.mp hq).1
        exact ⟨h3, h4, h1, h2⟩)
      (fun q hq => by
        obtain ⟨h1, h2, h3, h4⟩ := hAMp q hq
        exact ⟨h3, h4, h1, h2⟩)
      (Tm - ∑ q ∈ S₁, v q) (Tp - ∑ q ∈ S₁, u q) δ
      hV1a (le_trans hV1b hn₂) hU1a (by rw [max_self]; exact hU1b)
      hcardApp hc3
  have hU2b' : (Tp - ∑ q ∈ S₁, u q) - ∑ q ∈ S₂, u q ≤ δ := by
    rwa [max_self] at hU2b
  have hdisjS : Disjoint S₁ S₂ := by
    rw [disjoint_left]
    intro x hx1 hx2
    rcases mem_union.mp (hS₂sub hx2) with h | h
    · exact (mem_sdiff.mp h).2 hx1
    · rcases mem_union.mp (hS₁sub hx1) with h' | h'
      · exact disjoint_left.mp hd2 h' h
      · exact disjoint_left.mp hd3 h' h
  refine ⟨S₁ ∪ S₂, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_union.mp hx with h | h
    · rcases mem_union.mp (hS₁sub h) with h' | h'
      · exact mem_union_left _ (mem_union_left _ h')
      · exact mem_union_left _ (mem_union_right _ h')
    · rcases mem_union.mp (hS₂sub h) with h' | h'
      · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mp h').1)
      · exact mem_union_right _ h'
  · rw [sum_union hdisjS, abs_le]
    constructor <;> linarith
  · rw [sum_union hdisjS, abs_le]
    constructor <;> linarith

end RHTower
