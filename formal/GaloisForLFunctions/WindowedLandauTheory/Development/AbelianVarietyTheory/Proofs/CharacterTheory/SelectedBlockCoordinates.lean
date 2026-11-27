import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicLevi
import Mathlib.Data.Finset.Sort

/-! Selecting indices from a block list gives the corresponding coordinate
subspace with the original order of blocks. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ}

/-- A coordinate is specified by its block and its location within that block. -/
def listBlockCoordinateEquiv (L : List (Pc g)) (hL : degL L = n) :
    (Σ k : Fin L.length, Fin (L.get k).1) ≃ Fin n := by
  let f (x : Σ k : Fin L.length, Fin (L.get k).1) := listBlockEmbeddingAt L hL x.1 x.2
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have he : i = j := by
      have h' := congrArg (listBlockOfAt L hL) h
      simpa only [f, listBlockOfAt_embedding] using h'
    subst j
    have hab : a = b := (listBlockEmbeddingAt L hL i).injective h
    subst b
    rfl
  · intro i
    obtain ⟨a, ha⟩ := exists_listBlockCoordinateAt L hL i
    exact ⟨⟨listBlockOfAt L hL i, a⟩, ha⟩

@[simp] theorem listBlockCoordinateEquiv_apply (L : List (Pc g)) (hL : degL L = n)
    (k : Fin L.length) (i : Fin (L.get k).1) :
    listBlockCoordinateEquiv L hL ⟨k, i⟩ = listBlockEmbeddingAt L hL k i := rfl

/-- Keep the indicated blocks in their original order. -/
def selectBlocks (L : List (Pc g)) (S : Finset (Fin L.length)) : List (Pc g) :=
  S.sort.map L.get

theorem degL_selectBlocks (L : List (Pc g)) (S : Finset (Fin L.length)) :
    degL (selectBlocks L S) = ∑ j ∈ S, (L.get j).1 := by
  unfold degL selectBlocks
  rw [List.map_map, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rfl

/-- Each selected block retains its old index as an order embedding. -/
def selectedBlockIndex (L : List (Pc g)) (S : Finset (Fin L.length)) :
    Fin (selectBlocks L S).length ↪o Fin L.length :=
  S.orderEmbOfFin (by simp [selectBlocks])

@[simp] theorem selectedBlockIndex_mem (L : List (Pc g)) (S : Finset (Fin L.length))
    (k : Fin (selectBlocks L S).length) : selectedBlockIndex L S k ∈ S :=
  Finset.orderEmbOfFin_mem _ _ _

theorem selectBlocks_get (L : List (Pc g)) (S : Finset (Fin L.length))
    (k : Fin (selectBlocks L S).length) :
    (selectBlocks L S).get k = L.get (selectedBlockIndex L S k) := by
  have hk : k.val < S.sort.length := by simpa [selectBlocks] using k.isLt
  have he : selectedBlockIndex L S k = S.sort[k.val]'hk :=
    Finset.orderEmbOfFin_apply S (by simp [selectBlocks]) k
  rw [he]
  simp only [selectBlocks, List.get_eq_getElem, List.getElem_map]

theorem prod_selectedBlockIndex {A : Type*} [CommMonoid A] (L : List (Pc g))
    (S : Finset (Fin L.length)) (f : Fin L.length → A) :
    (∏ k : Fin (selectBlocks L S).length, f (selectedBlockIndex L S k)) = ∏ k ∈ S, f k := by
  rw [Finset.prod_subtype (p := fun k => k ∈ S) S (fun _ => Iff.rfl) f]
  exact Equiv.prod_comp (S.orderIsoOfFin (by simp [selectBlocks])).toEquiv (fun k : S => f k.val)

/-- Coordinates of selected blocks embed into the full coordinate space. -/
def selectBlockCoordinate (L : List (Pc g)) (hL : degL L = n)
    (S : Finset (Fin L.length)) {m : ℕ} (hS : degL (selectBlocks L S) = m) : Fin m → Fin n :=
  fun i =>
    let x := (listBlockCoordinateEquiv (selectBlocks L S) hS).symm i
    listBlockEmbeddingAt L hL (selectedBlockIndex L S x.1)
      (Fin.cast (congrArg Sigma.fst (selectBlocks_get L S x.1)) x.2)

theorem selectBlockCoordinate_apply (L : List (Pc g)) (hL : degL L = n)
    (S : Finset (Fin L.length)) {m : ℕ} (hS : degL (selectBlocks L S) = m)
    (k : Fin (selectBlocks L S).length) (i : Fin ((selectBlocks L S).get k).1) :
    selectBlockCoordinate L hL S hS (listBlockEmbeddingAt (selectBlocks L S) hS k i) =
      listBlockEmbeddingAt L hL (selectedBlockIndex L S k)
        (Fin.cast (congrArg Sigma.fst (selectBlocks_get L S k)) i) := by
  let e := listBlockCoordinateEquiv (selectBlocks L S) hS
  let f (x : Σ k : Fin (selectBlocks L S).length, Fin ((selectBlocks L S).get k).1) :=
    listBlockEmbeddingAt L hL (selectedBlockIndex L S x.1)
      (Fin.cast (congrArg Sigma.fst (selectBlocks_get L S x.1)) x.2)
  exact congrArg f (e.symm_apply_apply ⟨k, i⟩)

theorem listBlockOfAt_selectBlockCoordinate (L : List (Pc g)) (hL : degL L = n)
    (S : Finset (Fin L.length)) {m : ℕ} (hS : degL (selectBlocks L S) = m) (i : Fin m) :
    listBlockOfAt L hL (selectBlockCoordinate L hL S hS i) =
      selectedBlockIndex L S (listBlockOfAt (selectBlocks L S) hS i) := by
  obtain ⟨j, hj⟩ := exists_listBlockCoordinateAt (selectBlocks L S) hS i
  conv_lhs => rw [← hj, selectBlockCoordinate_apply, listBlockOfAt_embedding]

theorem selectBlockCoordinate_injective (L : List (Pc g)) (hL : degL L = n)
    (S : Finset (Fin L.length)) {m : ℕ} (hS : degL (selectBlocks L S) = m) :
    Function.Injective (selectBlockCoordinate L hL S hS) := by
  let T := selectBlocks L S
  let e := listBlockCoordinateEquiv T hS
  intro x y h
  obtain ⟨⟨k, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨l, j⟩, rfl⟩ := e.surjective y
  change selectBlockCoordinate L hL S hS (listBlockEmbeddingAt T hS k i) =
    selectBlockCoordinate L hL S hS (listBlockEmbeddingAt T hS l j) at h
  rw [selectBlockCoordinate_apply, selectBlockCoordinate_apply] at h
  have he := congrArg (listBlockOfAt L hL) h
  simp only [listBlockOfAt_embedding] at he
  have hkl := (selectedBlockIndex L S).injective he
  subst l
  have hij := (listBlockEmbeddingAt L hL (selectedBlockIndex L S k)).injective h
  have h' : i = j := (finCongr (congrArg Sigma.fst (selectBlocks_get L S k))).injective hij
  subst j
  rfl

theorem mem_range_selectBlockCoordinate (L : List (Pc g)) (hL : degL L = n)
    (S : Finset (Fin L.length)) {m : ℕ} (hS : degL (selectBlocks L S) = m) (i : Fin n) :
    i ∈ Set.range (selectBlockCoordinate L hL S hS) ↔ listBlockOfAt L hL i ∈ S := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [listBlockOfAt_selectBlockCoordinate]
    exact selectedBlockIndex_mem _ _ _
  · intro hi
    let k := listBlockOfAt L hL i
    let e := S.orderIsoOfFin (show S.card = (selectBlocks L S).length by simp [selectBlocks])
    let j := e.symm ⟨k, hi⟩
    have hj : selectedBlockIndex L S j = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hi⟩)
    obtain ⟨y, hy⟩ : ∃ y : Fin (L.get (selectedBlockIndex L S j)).1,
        listBlockEmbeddingAt L hL (selectedBlockIndex L S j) y = i := by
      rw [hj]
      exact exists_listBlockCoordinateAt L hL i
    let h : ((selectBlocks L S).get j).1 = (L.get (selectedBlockIndex L S j)).1 :=
      congrArg Sigma.fst (selectBlocks_get L S j)
    refine ⟨listBlockEmbeddingAt (selectBlocks L S) hS j (Fin.cast h.symm y), ?_⟩
    rw [selectBlockCoordinate_apply]
    have hz : Fin.cast h (Fin.cast h.symm y) = y := Fin.ext rfl
    rw [hz, hy]

variable {a b : ℕ}

/-- Group the selected blocks in the first segment, preserving the order
of the blocks within each segment. -/
def splitBlockPermutation (L : List (Pc g)) (hL : degL L = a + b)
    (S : Finset (Fin L.length)) (hA : degL (selectBlocks L S) = a)
    (hB : degL (selectBlocks L Sᶜ) = b) : Equiv.Perm (Fin (a + b)) := by
  let A := selectBlockCoordinate L hL S hA
  let B := selectBlockCoordinate L hL Sᶜ hB
  let f : Fin (a + b) → Fin (a + b) := Fin.addCases A B
  have hmemA (i : Fin a) : listBlockOfAt L hL (A i) ∈ S :=
    (mem_range_selectBlockCoordinate L hL S hA _).mp ⟨i, rfl⟩
  have hmemB (j : Fin b) : listBlockOfAt L hL (B j) ∉ S :=
    Finset.mem_compl.mp ((mem_range_selectBlockCoordinate L hL Sᶜ hB _).mp ⟨j, rfl⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [f, Fin.addCases_left, Fin.addCases_right]
    · intro h
      exact congrArg (Fin.castAdd b) (selectBlockCoordinate_injective L hL S hA h)
    · intro h
      exact (hmemB j (h ▸ hmemA i)).elim
    · intro h
      exact (hmemB i (h.symm ▸ hmemA j)).elim
    · intro h
      exact congrArg (Fin.natAdd a) (selectBlockCoordinate_injective L hL Sᶜ hB h)
  · intro i
    by_cases hi : listBlockOfAt L hL i ∈ S
    · obtain ⟨j, hj⟩ := (mem_range_selectBlockCoordinate L hL S hA i).mpr hi
      exact ⟨Fin.castAdd b j, (Fin.addCases_left j).trans hj⟩
    · obtain ⟨j, hj⟩ := (mem_range_selectBlockCoordinate L hL Sᶜ hB i).mpr (Finset.mem_compl.mpr hi)
      exact ⟨Fin.natAdd a j, (Fin.addCases_right j).trans hj⟩

@[simp] theorem splitBlockPermutation_castAdd (L : List (Pc g)) (hL : degL L = a + b)
    (S : Finset (Fin L.length)) (hA : degL (selectBlocks L S) = a)
    (hB : degL (selectBlocks L Sᶜ) = b) (i : Fin a) :
    splitBlockPermutation L hL S hA hB (Fin.castAdd b i) = selectBlockCoordinate L hL S hA i := by
  change Fin.addCases (motive := fun _ : Fin (a + b) => Fin (a + b))
    (selectBlockCoordinate L hL S hA) (selectBlockCoordinate L hL Sᶜ hB)
    (Fin.castAdd b i) = selectBlockCoordinate L hL S hA i
  exact Fin.addCases_left i

@[simp] theorem splitBlockPermutation_natAdd (L : List (Pc g)) (hL : degL L = a + b)
    (S : Finset (Fin L.length)) (hA : degL (selectBlocks L S) = a)
    (hB : degL (selectBlocks L Sᶜ) = b) (i : Fin b) :
    splitBlockPermutation L hL S hA hB (Fin.natAdd a i) = selectBlockCoordinate L hL Sᶜ hB i := by
  change Fin.addCases (motive := fun _ : Fin (a + b) => Fin (a + b))
    (selectBlockCoordinate L hL S hA) (selectBlockCoordinate L hL Sᶜ hB)
    (Fin.natAdd a i) = selectBlockCoordinate L hL Sᶜ hB i
  exact Fin.addCases_right i

end GlobalTheory.GLq
