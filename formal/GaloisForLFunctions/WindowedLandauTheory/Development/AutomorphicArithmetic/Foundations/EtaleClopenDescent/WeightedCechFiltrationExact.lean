import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechFiltration

/-! Exactness below a given level lets one remove successive levels of a
weighted Čech cocycle or fill the lower levels of a partial cocycle. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι M : Type*} [Field k] [LinearOrder ι] [Fintype ι] [AddCommGroup M] [Module k M]
  {A : Finset ι → Submodule k M} {w : ι → Module.End k M} {Q : Finset ι} {d n : ℤ}

private theorem boundary_sub_primitive
    (hcx : (acx A w).IsCx) {c y : Finset ι → M} (hc : c ∈ (acx A w).Z n)
    (hy : y ∈ (acx A w).C (n - 1)) :
    c - wd w y ∈ (acx A w).Z n := by
  obtain ⟨hmem, hzero⟩ := hcx (n - 1) y hy
  change wd w y ∈ (acx A w).C (n - 1 + 1) at hmem
  rw [sub_add_cancel] at hmem
  refine ⟨sub_mem hc.1 hmem, ?_⟩
  change wd w (c - wd w y) = 0
  rw [map_sub, show wd w c = 0 from hc.2, show wd w (wd w y) = 0 from hzero, sub_zero]

private theorem boundary_of_sub_primitive {c y : Finset ι → M}
    (hy : y ∈ (acx A w).C (n - 1)) (h : c - wd w y ∈ (acx A w).B n) :
    c ∈ (acx A w).B n := by
  have hy' : wd w y ∈ (acx A w).B n := Submodule.mem_map_of_mem hy
  rw [← sub_add_cancel c (wd w y)]
  exact add_mem h hy'

private theorem strip_level {m : ℤ} {c y : Finset ι → M}
    (hc : Lev Q (· ≤ m) c) (hy : Lev Q (· = m - 1) y)
    (hdy : ∀ s, ((s ∩ Q).card : ℤ) = m → wd (wOn Q w) y s = c s) :
    Lev Q (· < m) (c - wd w y) := by
  intro s hs
  have hright := wd_compl_support w hy s (by omega)
  have hleft := wd_on_support w hy
  have e := wd_on_split w Q y
  simp only [e, Pi.sub_apply, Pi.add_apply, hright, add_zero]
  by_cases ht : ((s ∩ Q).card : ℤ) = m
  · rw [hdy s ht, sub_self]
  · rw [hleft s (by omega), hc s (by omega), sub_zero]

private theorem top_part_is_closed {m : ℤ} {c : Finset ι → M}
    (hc : Lev Q (· ≤ m) c) (hzc : wd w c = 0) :
    wd (wOn Q w) (levelPart Q m c) = 0 := by
  rw [wd_on_levelPart]
  have hpart : levelPart Q (m + 1) c = 0 :=
    levelPart_eq_zero (fun t ht => hc t (by omega))
  have hzero : levelPart Q (m + 1) (wd (wOn Qᶜ w) c) = 0 := by
    rw [← wd_compl_levelPart, hpart, map_zero]
  apply levelPart_eq_zero
  intro t ht
  have hright : wd (wOn Qᶜ w) c t = 0 := by
    simpa only [levelPart, if_pos ht, Pi.zero_apply] using congrFun hzero t
  have e := congrFun (wd_on_split w Q c) t
  rw [hzc, Pi.zero_apply, Pi.add_apply, hright, add_zero] at e
  exact e.symm

private theorem boundary_below (hcx : (acx A w).IsCx) (hQ : QEx A w Q d) :
    ∀ j : ℕ, j ≤ d.toNat → ∀ c ∈ (acx A w).Z n, Lev Q (· < (j : ℤ)) c →
      c ∈ (acx A w).B n := by
  intro j
  induction j with
  | zero =>
    intro _ c _ hc
    have e : c = 0 := funext fun s => hc s (by omega)
    rw [e]
    exact zero_mem _
  | succ j ih =>
    intro hj c hc hl
    have hm : (j : ℤ) < d := by omega
    have hl' : Lev Q (· ≤ (j : ℤ)) c := fun s hs => hl s (by omega)
    obtain ⟨y, hy, hyl, hdy⟩ := hQ n j hm (levelPart Q j c) (levelPart_mem Q hc.1)
      (levelPart_support Q j c) (top_part_is_closed hl' hc.2)
    have hdy' (s : Finset ι) (hs : ((s ∩ Q).card : ℤ) = j) : wd (wOn Q w) y s = c s :=
      (congrFun hdy s).trans (if_pos hs)
    exact boundary_of_sub_primitive hy
      (ih (by omega) _ (boundary_sub_primitive hcx hc hy) (strip_level hl' hyl hdy'))

/-- A cocycle supported up to level `d` is a boundary if its top
level has a primitive for the differential on the selected indices. -/
theorem boundary_of_top_level_boundary (hcx : (acx A w).IsCx) (hQ : QEx A w Q d)
    {c y : Finset ι → M} (hc : c ∈ (acx A w).Z n) (hl : Lev Q (· ≤ d) c)
    (hy : y ∈ (acx A w).C (n - 1)) (hyl : Lev Q (· = d - 1) y)
    (hdy : ∀ s, ((s ∩ Q).card : ℤ) = d → wd (wOn Q w) y s = c s) :
    c ∈ (acx A w).B n := by
  refine boundary_of_sub_primitive hy
    (boundary_below hcx hQ d.toNat le_rfl _ (boundary_sub_primitive hcx hc hy) ?_)
  exact fun s hs => strip_level hl hyl hdy s (by omega)

/-- Extend a cochain at level `d` to a cocycle after the first obstruction
has a primitive. The remaining corrections are supported below `d`. -/
theorem exists_cocycle_of_top_level
    (hw : ∀ i j, Commute (w i) (w j))
    (hA : ∀ t i, i ∉ t → A t ≤ (A (insert i t)).comap (w i)) (hQ : QEx A w Q d)
    {c₀ y : Finset ι → M} (hc₀ : c₀ ∈ (acx A w).C n)
    (hvertical : wd (wOn Q w) c₀ = 0)
    (hy : y ∈ (acx A w).C n) (hyl : Lev Q (· = d - 1) y)
    (hdy : wd (wOn Q w) y = wd (wOn Qᶜ w) c₀) :
    ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c₀) := by
  have hcross := wd_anticommute (wOn Q w) (wOn Qᶜ w) (wOn_commute hw Q Qᶜ)
  have hsq := wd_wd (wOn Qᶜ w) (wOn_commute hw Qᶜ Qᶜ)
  have correct : ∀ j : ℕ, ∀ m : ℤ, m < j → m < d → ∀ (a b : Finset ι → M),
      a ∈ (acx A w).C n → Lev Q (· < d) (a - c₀) → b ∈ (acx A w).C n →
      Lev Q (· = m) b → wd w a = -wd (wOn Qᶜ w) b →
      wd (wOn Q w) (wd (wOn Qᶜ w) b) = 0 →
      ∃ c ∈ (acx A w).Z n, Lev Q (· < d) (c - c₀) := by
    intro j
    induction j with
    | zero =>
      intro m hm _ a b ha hal _ hb hda _
      have hb₀ : b = 0 := funext fun t => hb t (by omega)
      rw [hb₀, map_zero, neg_zero] at hda
      exact ⟨a, ⟨ha, hda⟩, hal⟩
    | succ j ih =>
      intro m hm hmd a b ha hal hb hbl hda hdb
      have he : -wd (wOn Qᶜ w) b ∈ (acx A w).C (n + 1) :=
        neg_mem (wd_on_mem hw hA Qᶜ hb)
      have hel : Lev Q (· = m) (-wd (wOn Qᶜ w) b) := fun s hs => by
        rw [Pi.neg_apply, wd_compl_support w hbl s hs, neg_zero]
      have hez : wd (wOn Q w) (-wd (wOn Qᶜ w) b) = 0 := by rw [map_neg, hdb, neg_zero]
      obtain ⟨b', hb', hb'l, hdb'⟩ := hQ (n + 1) m hmd _ he hel hez
      rw [add_sub_cancel_right] at hb'
      refine ih (m - 1) (by omega) (by omega) (a - b') b' (sub_mem ha hb') ?_ hb' hb'l ?_ ?_
      · intro s hs
        have hz := hb'l s (by omega)
        rw [Pi.sub_apply, Pi.sub_apply, hz, sub_zero, ← Pi.sub_apply]
        exact hal s hs
      · rw [map_sub, hda, wd_on_split w Q b', hdb']
        abel
      · have h := hcross b'
        rwa [hdb', map_neg, hsq, neg_zero, add_zero] at h
  refine correct d.toNat (d - 1) (by omega) (by omega) (c₀ - y) y
    (sub_mem hc₀ hy) ?_ hy hyl ?_ ?_
  · intro s hs
    rw [Pi.sub_apply, Pi.sub_apply, hyl s (by omega), sub_zero, sub_self]
  · rw [map_sub, wd_on_split w Q c₀, wd_on_split w Q y, hvertical, zero_add, hdy]
    abel
  · have h := hcross y
    rwa [hdy, hsq, add_zero] at h

end GlobalTheory.WH
