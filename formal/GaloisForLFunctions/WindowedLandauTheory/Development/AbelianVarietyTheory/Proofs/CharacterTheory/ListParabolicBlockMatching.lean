import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicSplitRadical

/-! When neither flag splits a block of the other, the blocks and their
coordinates match by equivalences. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem listBlockOfAt_surjective (L : List (Pc g)) (hL : degL L = n)
    (hpos : ∀ k : Fin L.length, 0 < (L.get k).1) :
    Function.Surjective (listBlockOfAt L hL) := fun k =>
  ⟨listBlockEmbeddingAt L hL k ⟨0, hpos k⟩, listBlockOfAt_embedding L hL k _⟩

/-- Mutual constancy on fibres forces the two positive-width block partitions to match. -/
theorem exists_listBlockEquiv (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (σ : Equiv.Perm (Fin n)) (hLpos : ∀ k : Fin L.length, 0 < (L.get k).1)
    (hMpos : ∀ k : Fin M.length, 0 < (M.get k).1)
    (hf : ∀ i j, listBlockOfAt L hL i = listBlockOfAt L hL j →
      permutedListBlockOf M hM σ i = permutedListBlockOf M hM σ j)
    (hr : ∀ i j, permutedListBlockOf M hM σ i = permutedListBlockOf M hM σ j →
      listBlockOfAt L hL i = listBlockOfAt L hL j) :
    ∃ e : Fin L.length ≃ Fin M.length,
      ∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i := by
  let f := listBlockOfAt L hL
  let r := permutedListBlockOf M hM σ
  have hfs : Function.Surjective f := listBlockOfAt_surjective L hL hLpos
  have hrs : Function.Surjective r := (listBlockOfAt_surjective M hM hMpos).comp σ.symm.surjective
  let s (k : Fin L.length) := Classical.choose (hfs k)
  have hs : ∀ k, f (s k) = k := fun k => Classical.choose_spec (hfs k)
  let E (k : Fin L.length) := r (s k)
  have he (i : Fin n) : E (f i) = r i := hf (s (f i)) i (hs (f i))
  have hi : Function.Injective E := fun i j hij => (hs i).symm.trans ((hr (s i) (s j) hij).trans (hs j))
  have hsurj : Function.Surjective E := by
    intro k
    obtain ⟨i, rfl⟩ := hrs k
    exact ⟨f i, he i⟩
  exact ⟨Equiv.ofBijective E ⟨hi, hsurj⟩, he⟩

private def listBlockFibreEquiv (L : List (Pc g)) (hL : degL L = n) (k : Fin L.length) :
    Fin (L.get k).1 ≃ {i : Fin n // listBlockOfAt L hL i = k} :=
  Equiv.ofBijective
    (fun j => ⟨listBlockEmbeddingAt L hL k j, listBlockOfAt_embedding L hL k j⟩)
    ⟨fun i j h => (listBlockEmbeddingAt L hL k).injective (congrArg Subtype.val h),
      fun i => by
        obtain ⟨x, hx⟩ := exists_listBlockCoordinateAt_of_eq L hL i.property
        exact ⟨x, Subtype.ext hx⟩⟩

/-- A matched pair of blocks has an invertible correspondence of its coordinates. -/
def matchedBlockCoordinates (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (σ : Equiv.Perm (Fin n)) (e : Fin L.length ≃ Fin M.length)
    (he : ∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i) (k : Fin L.length) :
    Fin (L.get k).1 ≃ Fin (M.get (e k)).1 :=
  (listBlockFibreEquiv L hL k).trans ((σ.symm.subtypeEquiv (fun i => by
    change listBlockOfAt L hL i = k ↔ permutedListBlockOf M hM σ i = e k
    rw [← he i]
    exact e.injective.eq_iff.symm)).trans (listBlockFibreEquiv M hM (e k)).symm)

theorem matchedBlockCoordinates_apply (L M : List (Pc g)) (hL : degL L = n) (hM : degL M = n)
    (σ : Equiv.Perm (Fin n)) (e : Fin L.length ≃ Fin M.length)
    (he : ∀ i, e (listBlockOfAt L hL i) = permutedListBlockOf M hM σ i)
    (k : Fin L.length) (i : Fin (L.get k).1) :
    σ (listBlockEmbeddingAt M hM (e k) (matchedBlockCoordinates L M hL hM σ e he k i)) =
      listBlockEmbeddingAt L hL k i := by
  apply σ.symm.injective
  rw [σ.symm_apply_apply]
  let v : {j : Fin n // listBlockOfAt M hM j = e k} :=
    ⟨σ.symm (listBlockEmbeddingAt L hL k i), by
      change permutedListBlockOf M hM σ (listBlockEmbeddingAt L hL k i) = e k
      rw [← he, listBlockOfAt_embedding]⟩
  exact congrArg Subtype.val ((listBlockFibreEquiv M hM (e k)).apply_symm_apply v)

end GlobalTheory.GLq
