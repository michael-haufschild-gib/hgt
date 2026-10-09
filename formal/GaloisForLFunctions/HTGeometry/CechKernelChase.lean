import GaloisForLFunctions.HTGeometry.FinsetCechDatum

/-!
# Sections in the kernel of a map of Čech data

Let `F → G → Q` be morphisms of Čech data, exact in the middle on single members and injective on
pairs, with `F` exact in degree `0`.  A section `y` of `G` over the covered set killed in `Q` agrees,
on every member of the cover, with the image of a section of `F` over the covered set (it suffices
that `y` is killed in `Q` on every member).  (Restricted to
the members, `y` lifts to a `0`-cochain of `F`; it is a cocycle because `ι` is injective on pairs,
so it comes from the covered set.)

* `HTGeometry.FinsetCechDatum.exists_bot_of_kernel`.
-/

namespace HTGeometry

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace FinsetCechDatum

universe v

variable {T : Type*} [DecidableEq T] [LinearOrder T] {F G Q : FinsetCechDatum.{v} T}
  (ι : Hom F G) (π : Hom G Q)

omit [DecidableEq T] in
theorem cechSign_singleton (i : T) : (cechSign ({i} : Finset T) i : ℤ) = 1 := by
  simp [cechSign, belowCard, Finset.filter_singleton]

/-- `d` of a degree-`-1` cochain on a single member is the restriction. -/
theorem d_singleton_of_isBot (D : FinsetCechDatum.{v} T) (c : D.Cochain) (i : T) :
    D.d c {i} = D.res (Finset.empty_subset {i}) (c ∅) := by
  rw [d, Finset.sum_singleton, res_cochain_congr c (Finset.erase_singleton i) _
    (Finset.empty_subset _), cechSign_singleton, one_smul]

/-- **A section in the kernel comes, on the members, from the first datum.** -/
theorem exists_bot_of_kernel
    (hexact : ∀ s : Finset T, s.card = 1 → ∀ y, π.app s y = 0 → ∃ x, ι.app s x = y)
    (hinj : ∀ s : Finset T, s.card = 2 → Function.Injective (ι.app s))
    (hF : F.ExactAt 0) (y : G.obj ∅)
    (hy : ∀ i : T, π.app {i} (G.res (Finset.empty_subset {i}) y) = 0) :
    ∃ b : F.obj ∅, ∀ i : T, G.res (Finset.empty_subset {i}) (ι.app ∅ b)
      = G.res (Finset.empty_subset {i}) y := by
  classical
  let ybot : G.Cochain := fun s => if hs : s = ∅ then hs ▸ y else 0
  have hybot : G.IsBot ybot := fun s hs => dif_neg hs.ne_empty
  have hy0 : ybot ∅ = y := dif_pos rfl
  have hlift : ∀ s : Finset T, s.card = 1 → ∃ x, ι.app s x = G.d ybot s := by
    intro s hs
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    refine hexact {i} hs _ ?_
    rw [d_singleton_of_isBot, hy0]
    exact hy i
  let c : F.Cochain := fun s => if hs : s.card = 1 then Classical.choose (hlift s hs) else 0
  have hc : F.IsDeg c 0 := fun s hs => dif_neg hs
  have hιc : ι.onCochain c = G.d ybot := by
    funext s
    by_cases hs : s.card = 1
    · change ι.app s (c s) = _
      simp only [c, dif_pos hs]
      exact Classical.choose_spec (hlift s hs)
    · change ι.app s (c s) = _
      rw [hc s hs, map_zero, G.d_isDeg_of_isBot hybot s hs]
  have hdc : F.d c = 0 := by
    funext s
    by_cases hs : s.card = 2
    · apply hinj s hs
      change ι.app s (F.d c s) = ι.app s 0
      rw [map_zero]
      have := congrFun (ι.d_onCochain c) s
      change G.d (ι.onCochain c) s = ι.app s (F.d c s) at this
      rw [← this, hιc, G.d_d]
      rfl
    · exact F.d_isDeg hc s hs
  obtain ⟨b', hb', hdb'⟩ := hF c hc hdc
  refine ⟨b' ∅, fun i => ?_⟩
  have h1 : c {i} = F.res (Finset.empty_subset {i}) (b' ∅) := by
    rw [← hdb', d_singleton_of_isBot]
  have h2 := congrFun hιc {i}
  change ι.app {i} (c {i}) = G.d ybot {i} at h2
  rw [h1, ← ι.comm, d_singleton_of_isBot, hy0] at h2
  exact h2

end FinsetCechDatum

end HTGeometry
