import GaloisForLFunctions.HTGeometry.KleinbockMargulis.DerivChain
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cutting an interval at finitely many points

If a set `S` inside an interval avoids a finite set `Z` and is "convex across `Z`" — any two of
its points with no point of `Z` between them have the whole segment inside `S` — then `S` is a
union of at most `|Z| + 1` intervals, so its measure is at most `(|Z| + 1)` times the length of the
longest interval it contains.

Together with the fact that a function with nonvanishing `k`-th derivative takes any value at most
`k` times, this produces the interval on which the paper's Sublemma 3.3.1 operates.

## Main results

* `card_le_of_chain_ne_zero` — a chain with nonvanishing top member takes each value at most `k`
  times.
* `volume_le_of_cuts` — the counting estimate.
-/

open Set MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

/-! ### Level sets are small -/

/-- A derivative chain whose `k`-th member never vanishes takes each value at most `k` times. -/
theorem card_le_of_chain_ne_zero {U : Set ℝ} (hUc : U.OrdConnected) {F : ℕ → ℝ → ℝ}
    {k : ℕ} (hF : IsDerivChain k F U) (hk : 1 ≤ k) (hne : ∀ x ∈ U, F k x ≠ 0) (c : ℝ)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ U ∧ F 0 x = c) : s.card ≤ k := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq (s := s) (n := k' + 2) (by omega)
  set pts : Fin (k' + 2) → ℝ := fun i => ((t.orderIsoOfFin hcard i : ℝ)) with hpts
  have hmono : StrictMono pts := fun i j hij => (t.orderIsoOfFin hcard).strictMono hij
  have hmem : ∀ i, pts i ∈ t := fun i => (t.orderIsoOfFin hcard i).2
  set G : ℕ → ℝ → ℝ := fun j => Nat.casesOn j (fun x => F 0 x - c) fun j' => F (j' + 1) with hG
  have hGchain : IsDerivChain (k' + 1) G U := by
    intro j hj x hx
    rcases j with _ | j
    · exact (hF 0 (by omega) x hx).sub_const c
    · exact hF (j + 1) hj x hx
  obtain ⟨ξ, hξmem, hξ⟩ :=
    exists_chain_eq_zero hUc (k' + 1) G hGchain pts hmono
      (fun i => (hs _ (hts (hmem i))).1)
      (fun i => by
        show F 0 (pts i) - c = 0
        rw [(hs _ (hts (hmem i))).2, sub_self])
  have hξU : ξ ∈ U :=
    hUc.out (hs _ (hts (hmem 0))).1 (hs _ (hts (hmem (Fin.last (k' + 1))))).1 hξmem
  exact hne ξ hξU hξ

/-! ### The counting estimate -/

/-- A set that is convex inside an interval has measure at most the bound on the length of the
intervals it contains. -/
theorem volume_le_of_ordConnected {a b : ℝ} {S : Set ℝ} {L : ℝ} (_hL : 0 ≤ L)
    (hSab : S ⊆ Ioo a b) (hconv : ∀ x ∈ S, ∀ y ∈ S, x < y → Ioo x y ⊆ S)
    (hlen : ∀ u v : ℝ, Ioo u v ⊆ S → v - u ≤ L) :
    volume S ≤ ENNReal.ofReal L := by
  rcases Set.eq_empty_or_nonempty S with rfl | ⟨x₀, hx₀⟩
  · simp
  · have hbdd : BddAbove S := ⟨b, fun y hy => (hSab hy).2.le⟩
    have hbdd' : BddBelow S := ⟨a, fun y hy => (hSab hy).1.le⟩
    set u := sInf S with hu
    set v := sSup S with hv
    have hIoo : Ioo u v ⊆ S := by
      intro w hw
      obtain ⟨x, hxS, hxw⟩ := exists_lt_of_csInf_lt ⟨x₀, hx₀⟩ hw.1
      obtain ⟨y, hyS, hwy⟩ := exists_lt_of_lt_csSup ⟨x₀, hx₀⟩ hw.2
      exact hconv x hxS y hyS (lt_trans hxw hwy) ⟨hxw, hwy⟩
    have hsub : S ⊆ Icc u v := fun y hy => ⟨csInf_le hbdd' hy, le_csSup hbdd hy⟩
    calc volume S ≤ volume (Icc u v) := measure_mono hsub
      _ = ENNReal.ofReal (v - u) := Real.volume_Icc
      _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal (hlen u v hIoo)

/-- **The counting estimate.**  `S` is a union of at most `|Z| + 1` intervals. -/
theorem volume_le_of_cuts :
    ∀ (p : ℕ) (a b : ℝ) (Z : Finset ℝ), Z.card ≤ p → (∀ z ∈ Z, z ∈ Ioo a b) →
      ∀ (S : Set ℝ) (L : ℝ), 0 ≤ L → S ⊆ Ioo a b → (∀ z ∈ Z, z ∉ S) →
        (∀ x ∈ S, ∀ y ∈ S, x < y → (∀ w ∈ Ioo x y, w ∉ Z) → Ioo x y ⊆ S) →
        (∀ u v : ℝ, Ioo u v ⊆ S → v - u ≤ L) →
        volume S ≤ ENNReal.ofReal (((Z.card : ℝ) + 1) * L) := by
  intro p
  induction p with
  | zero =>
    intro a b Z hcard _ S L hL hSab _ hconv hlen
    have hZ : Z = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hZ
    refine le_trans (volume_le_of_ordConnected hL hSab ?_ hlen) ?_
    · intro x hx y hy hxy
      exact hconv x hx y hy hxy (fun w _ hw => by simp at hw)
    · simp
  | succ p ih =>
    intro a b Z hcard hZab S L hL hSab hZS hconv hlen
    classical
    rcases Finset.eq_empty_or_nonempty Z with rfl | ⟨z, hz⟩
    · refine le_trans (volume_le_of_ordConnected hL hSab ?_ hlen) ?_
      · intro x hx y hy hxy
        exact hconv x hx y hy hxy (fun w _ hw => by simp at hw)
      · simp
    set Z' := Z.erase z with hZ'
    have hzcard : 1 ≤ Z.card := Finset.card_pos.mpr ⟨z, hz⟩
    have hZ'card : Z'.card + 1 = Z.card := by
      rw [hZ', Finset.card_erase_of_mem hz]
      omega
    set Z₁ := Z'.filter (· < z) with hZ₁
    set Z₂ := Z'.filter (fun w => z < w) with hZ₂
    have hsplit : Z₁.card + Z₂.card = Z'.card := by
      have hun : Z₁ ∪ Z₂ = Z' := by
        ext w
        simp only [Finset.mem_union, Finset.mem_filter, hZ₁, hZ₂]
        constructor
        · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
        · intro hw
          rcases lt_trichotomy w z with h | h | h
          · exact Or.inl ⟨hw, h⟩
          · exact absurd h (Finset.ne_of_mem_erase hw)
          · exact Or.inr ⟨hw, h⟩
      have hdisj : Disjoint Z₁ Z₂ := by
        refine Finset.disjoint_left.mpr fun w hw1 hw2 => ?_
        have h1 := (Finset.mem_filter.mp hw1).2
        have h2 := (Finset.mem_filter.mp hw2).2
        exact absurd h1 (not_lt.mpr h2.le)
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hun] at hcu
      omega
    have hzab : z ∈ Ioo a b := hZab z hz
    have hzS : z ∉ S := hZS z hz
    have hcover : S ⊆ (S ∩ Ioo a z) ∪ (S ∩ Ioo z b) := by
      intro y hy
      have hyab := hSab hy
      rcases lt_trichotomy y z with h | h | h
      · exact Or.inl ⟨hy, hyab.1, h⟩
      · exact absurd (h ▸ hy) hzS
      · exact Or.inr ⟨hy, h, hyab.2⟩
    have h1 : volume (S ∩ Ioo a z) ≤ ENNReal.ofReal (((Z₁.card : ℝ) + 1) * L) := by
      refine ih a z Z₁ (by omega) ?_ (S ∩ Ioo a z) L hL Set.inter_subset_right ?_ ?_
        (fun u v huv => hlen u v (huv.trans Set.inter_subset_left))
      · intro w hw
        have hwZ : w ∈ Z := Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
        exact ⟨(hZab w hwZ).1, (Finset.mem_filter.mp hw).2⟩
      · intro w hw hwS
        exact hZS w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1) hwS.1
      · rintro x ⟨hxS, hxI⟩ y ⟨hyS, hyI⟩ hxy hnoZ
        have hnoZ' : ∀ w ∈ Ioo x y, w ∉ Z := by
          intro w hw hwZ
          have hwlt : w < z := lt_trans hw.2 hyI.2
          refine hnoZ w hw ?_
          rw [hZ₁, Finset.mem_filter, hZ']
          exact ⟨Finset.mem_erase.mpr ⟨ne_of_lt hwlt, hwZ⟩, hwlt⟩
        intro w hw
        exact ⟨hconv x hxS y hyS hxy hnoZ' hw,
          lt_of_le_of_lt hxI.1.le hw.1, lt_trans hw.2 hyI.2⟩
    have h2 : volume (S ∩ Ioo z b) ≤ ENNReal.ofReal (((Z₂.card : ℝ) + 1) * L) := by
      refine ih z b Z₂ (by omega) ?_ (S ∩ Ioo z b) L hL Set.inter_subset_right ?_ ?_
        (fun u v huv => hlen u v (huv.trans Set.inter_subset_left))
      · intro w hw
        have hwZ : w ∈ Z := Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
        exact ⟨(Finset.mem_filter.mp hw).2, (hZab w hwZ).2⟩
      · intro w hw hwS
        exact hZS w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1) hwS.1
      · rintro x ⟨hxS, hxI⟩ y ⟨hyS, hyI⟩ hxy hnoZ
        have hnoZ' : ∀ w ∈ Ioo x y, w ∉ Z := by
          intro w hw hwZ
          have hwgt : z < w := lt_trans hxI.1 hw.1
          refine hnoZ w hw ?_
          rw [hZ₂, Finset.mem_filter, hZ']
          exact ⟨Finset.mem_erase.mpr ⟨(ne_of_lt hwgt).symm, hwZ⟩, hwgt⟩
        intro w hw
        exact ⟨hconv x hxS y hyS hxy hnoZ' hw,
          lt_trans hxI.1 hw.1, lt_of_lt_of_le hw.2 hyI.2.le⟩
    calc volume S ≤ volume ((S ∩ Ioo a z) ∪ (S ∩ Ioo z b)) := measure_mono hcover
      _ ≤ volume (S ∩ Ioo a z) + volume (S ∩ Ioo z b) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (((Z₁.card : ℝ) + 1) * L)
          + ENNReal.ofReal (((Z₂.card : ℝ) + 1) * L) := add_le_add h1 h2
      _ = ENNReal.ofReal ((((Z₁.card : ℝ) + 1) * L) + (((Z₂.card : ℝ) + 1) * L)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (((Z.card : ℝ) + 1) * L) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hc : (Z₁.card : ℝ) + (Z₂.card : ℝ) + 1 = (Z.card : ℝ) := by
            have : Z₁.card + Z₂.card + 1 = Z.card := by omega
            exact_mod_cast this
          nlinarith

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
