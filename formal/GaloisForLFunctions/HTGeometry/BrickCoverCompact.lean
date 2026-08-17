import GaloisForLFunctions.HTGeometry.BrickCover

/-!
# A finite, enumerated brick cover of a compact set

Compactness turns the brick cover of `ℝ^k` into a finite subfamily, which is then enumerated by an
initial segment of `ℕ`.  Enumerating an injective list keeps the order bound `k + 1`: distinct
enumeration indices name distinct bricks.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- **An enumerated finite brick cover of a compact set.** -/
theorem exists_enumerated_brick_cover {k : ℕ} (hk : 0 < k) {K : Set (EuclideanSpace ℝ (Fin k))}
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (B : ℕ → Set (EuclideanSpace ℝ (Fin k))),
      (∀ p, IsOpen (B p)) ∧
      (∀ p, (B p)ᶜ.Nonempty) ∧
      (∀ y ∈ K, ∃ p, p < N ∧ y ∈ B p) ∧
      (∀ p, ∀ y ∈ B p, ∀ y' ∈ B p, dist y y' ≤ Real.sqrt k * δ) ∧
      (∀ (y : EuclideanSpace ℝ (Fin k)) (t : Finset ℕ), (∀ p ∈ t, p < N) →
        (∀ p ∈ t, y ∈ B p) → t.card ≤ k + 1) := by
  classical
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover
    (fun i : Fin (k + 1) × (Fin k → ℤ) => brick k δ i.1 i.2)
    (fun i => isOpen_brick k δ i.1 i.2)
    (by
      intro y _
      obtain ⟨s, z, hsz⟩ := exists_mem_brick k hδ y
      exact Set.mem_iUnion.mpr ⟨(s, z), hsz⟩)
  set L : List (Fin (k + 1) × (Fin k → ℤ)) := T.toList with hL
  have hLnodup : L.Nodup := T.nodup_toList
  set idx : ℕ → Fin (k + 1) × (Fin k → ℤ) := fun p => L.getD p (0, fun _ => 0) with hidx
  have hidxget : ∀ p (hp : p < L.length), idx p = L[p] := fun p hp => List.getD_eq_getElem _ _ hp
  have hidxinj : ∀ p < L.length, ∀ q < L.length, idx p = idx q → p = q := by
    intro p hp q hq hpq
    rw [hidxget p hp, hidxget q hq] at hpq
    exact (hLnodup.getElem_inj_iff).mp hpq
  refine ⟨L.length, fun p => brick k δ (idx p).1 (idx p).2, fun p => isOpen_brick _ _ _ _,
    fun p => compl_brick_nonempty hk hδ _ _, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hy)
    obtain ⟨hiT, hyi⟩ := Set.mem_iUnion.mp hi
    have hmem : i ∈ L := by
      rw [hL, Finset.mem_toList]
      exact hiT
    obtain ⟨p, hp, hpi⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨p, hp, ?_⟩
    show y ∈ brick k δ (idx p).1 (idx p).2
    rw [hidxget p hp, hpi]
    exact hyi
  · intro p y hy y' hy'
    exact dist_le_of_mem_brick hδ (s := (idx p).1) (z := (idx p).2) hy hy'
  · intro y t htlt htmem
    have hinj : Set.InjOn idx (t : Set ℕ) := by
      intro p hp q hq hpq
      exact hidxinj p (htlt p hp) q (htlt q hq) hpq
    have hcard : (t.image idx).card = t.card := Finset.card_image_of_injOn hinj
    have hall : ∀ i ∈ t.image idx, y ∈ brick k δ i.1 i.2 := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      exact htmem p hp
    have := brick_card_le hδ y (t.image idx) hall
    omega

end GaloisForLFunctions.HTGeometry
