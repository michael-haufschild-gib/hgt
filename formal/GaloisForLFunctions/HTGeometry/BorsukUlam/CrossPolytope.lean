import GaloisForLFunctions.HTGeometry.BorsukUlam.FlagComplex
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# The octahedral (cross-polytope) complex

The boundary of the cross-polytope `conv {±e₀, …, ±e_n}` is triangulated by its orthant faces: a
face is a nonempty set of signed basis vectors with pairwise distinct indices.  Taking the level of
`(i, ε)` to be `i` and its sign to be `ε`, the hemispheres are
`± H_d = {x : x_{d+1} = ⋯ = 0, ± x_d ≥ 0}` and all `FlagComplex` axioms hold.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.BorsukUlam

open Finset

namespace CrossPolytope

variable (n : ℕ)

/-- Vertices of the cross-polytope: a coordinate index with a sign. -/
abbrev Vtx : Type := Fin (n + 1) × Bool

variable {n}

/-- The index of a vertex, as a natural number. -/
def idx (x : Vtx n) : ℕ := (x.1 : ℕ)

/-- Faces: nonempty sets of vertices with pairwise distinct indices. -/
def faces : Finset (Finset (Vtx n)) :=
  Finset.univ.filter (fun S => S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → x = y)

theorem mem_faces {S : Finset (Vtx n)} :
    S ∈ faces ↔ (S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → x = y) := by
  rw [faces, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem idx_inj_of_face {S : Finset (Vtx n)} (hS : S ∈ faces) {x y : Vtx n} (hx : x ∈ S)
    (hy : y ∈ S) (h : idx x = idx y) : x = y :=
  (mem_faces.mp hS).2 x hx y hy (Fin.ext h)

theorem card_le_sup {S : Finset (Vtx n)} (hS : S ∈ faces) :
    S.card ≤ S.sup idx + 1 := by
  have hmaps : ∀ x ∈ S, idx x ∈ Finset.range (S.sup idx + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have : idx x ≤ S.sup idx := Finset.le_sup hx
    omega
  have hmapsTo : Set.MapsTo idx (S : Set (Vtx n)) (Finset.range (S.sup idx + 1) : Set ℕ) := by
    intro x hx
    exact hmaps x (Finset.mem_coe.mp hx)
  have hinj : Set.InjOn idx (S : Set (Vtx n)) := by
    intro x hx y hy h
    exact idx_inj_of_face hS (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) h
  have := Finset.card_le_card_of_injOn idx hmapsTo hinj
  simpa using this

theorem idx_image_subset {S : Finset (Vtx n)} :
    S.image idx ⊆ Finset.range (S.sup idx + 1) := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hk
  rw [Finset.mem_range]
  have : idx x ≤ S.sup idx := Finset.le_sup hx
  omega

theorem card_idx_image {S : Finset (Vtx n)} (hS : S ∈ faces) :
    (S.image idx).card = S.card :=
  card_image_of_injOn (fun x hx y hy h =>
    idx_inj_of_face hS (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) h)

theorem sup_mem_image {S : Finset (Vtx n)} (hne : S.Nonempty) : S.sup idx ∈ S.image idx := by
  obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup S hne idx
  exact mem_image.mpr ⟨x, hx, hxeq.symm⟩

theorem sup_idx_le {S : Finset (Vtx n)} : S.sup idx ≤ n := by
  refine Finset.sup_le fun x _ => ?_
  have := x.1.isLt
  simp only [idx]
  omega

/-- The two extensions of a face that misses one index below its top. -/
theorem facets_two_cp {S : Finset (Vtx n)} (hS : S ∈ faces) (hcard : S.card = S.sup idx) :
    ∃ τ₁ ∈ faces, ∃ τ₂ ∈ faces, τ₁ ≠ τ₂ ∧
      (S ⊆ τ₁ ∧ τ₁.card = S.card + 1 ∧ τ₁.sup idx = S.sup idx) ∧
      (S ⊆ τ₂ ∧ τ₂.card = S.card + 1 ∧ τ₂.sup idx = S.sup idx) ∧
      ∀ τ ∈ faces, S ⊆ τ → τ.card = S.card + 1 → τ.sup idx = S.sup idx → τ = τ₁ ∨ τ = τ₂ := by
  classical
  set D := S.sup idx with hD
  have hsub : S.image idx ⊆ Finset.range (D + 1) := idx_image_subset
  have hcardim : (S.image idx).card = D := by rw [card_idx_image hS, hcard]
  have hd1 : ((Finset.range (D + 1)) \ (S.image idx)).card = 1 := by
    rw [card_sdiff_of_subset hsub, Finset.card_range]
    omega
  obtain ⟨j, hj⟩ := card_eq_one.mp hd1
  have hjmem : j ∈ Finset.range (D + 1) ∧ j ∉ S.image idx := by
    have : j ∈ (Finset.range (D + 1)) \ (S.image idx) := by rw [hj]; exact mem_singleton_self j
    exact mem_sdiff.mp this
  have hjle : j ≤ D := by
    have := hjmem.1
    rw [Finset.mem_range] at this
    omega
  have hjn : j < n + 1 := by
    have := sup_idx_le (S := S)
    omega
  set v : Fin (n + 1) := ⟨j, hjn⟩ with hv
  have hvval : (v : ℕ) = j := by rw [hv]
  have hidxv : ∀ ε : Bool, idx ((v, ε) : Vtx n) = j := fun ε => hvval
  have hnotmem : ∀ ε : Bool, ((v, ε) : Vtx n) ∉ S := by
    intro ε hmem
    exact hjmem.2 (mem_image.mpr ⟨(v, ε), hmem, hidxv ε⟩)
  have hface : ∀ ε : Bool, insert ((v, ε) : Vtx n) S ∈ faces := by
    intro ε
    refine mem_faces.mpr ⟨⟨(v, ε), mem_insert_self _ _⟩, ?_⟩
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
    · rfl
    · exact absurd (mem_image.mpr ⟨y, hy', by rw [idx, ← hxy]⟩) hjmem.2
    · exact absurd (mem_image.mpr ⟨x, hx', by rw [idx, hxy]⟩) hjmem.2
    · exact (mem_faces.mp hS).2 x hx' y hy' hxy
  have hsupins : ∀ ε : Bool, (insert ((v, ε) : Vtx n) S).sup idx = D := by
    intro ε
    rw [Finset.sup_insert, hidxv ε]
    omega
  refine ⟨insert ((v, true) : Vtx n) S, hface true, insert ((v, false) : Vtx n) S, hface false,
    ?_, ⟨subset_insert _ _, card_insert_of_notMem (hnotmem true), hsupins true⟩,
    ⟨subset_insert _ _, card_insert_of_notMem (hnotmem false), hsupins false⟩, ?_⟩
  · intro hcon
    have h1 : ((v, true) : Vtx n) ∈ insert ((v, false) : Vtx n) S := by
      rw [← hcon]; exact mem_insert_self _ _
    rcases mem_insert.mp h1 with heq | hmem
    · simp at heq
    · exact hnotmem true hmem
  · intro τ hτ hsubτ hcardτ hsupτ
    obtain ⟨x, hxnot, rfl⟩ := exists_insert hsubτ hcardτ
    have hidxle : idx x ≤ D := by
      have : idx x ≤ (insert x S).sup idx := Finset.le_sup (mem_insert_self _ _)
      omega
    have hidxnot : idx x ∉ S.image idx := by
      intro hmem
      obtain ⟨y, hy, hyidx⟩ := mem_image.mp hmem
      have := idx_inj_of_face hτ (mem_insert_self x S) (mem_insert_of_mem hy) hyidx.symm
      rw [this] at hxnot
      exact hxnot hy
    have hidxj : idx x = j := by
      have hmem : idx x ∈ Finset.range (D + 1) := by
        rw [Finset.mem_range]; omega
      have : idx x ∈ (Finset.range (D + 1)) \ (S.image idx) := mem_sdiff.mpr ⟨hmem, hidxnot⟩
      rw [hj, mem_singleton] at this
      exact this
    have hx1 : x.1 = v := Fin.ext hidxj
    rcases Bool.eq_false_or_eq_true x.2 with h2 | h2
    · exact Or.inl (by rw [show x = ((v, true) : Vtx n) from Prod.ext hx1 h2])
    · exact Or.inr (by rw [show x = ((v, false) : Vtx n) from Prod.ext hx1 h2])


/-- The unique extension of a full face into the next hemisphere of a given sign. -/
theorem facets_one_cp {S : Finset (Vtx n)} (hS : S ∈ faces) (hcard : S.card = S.sup idx + 1)
    (hlt : S.sup idx < n) (ε : Bool) :
    ∃ τ ∈ faces, (S ⊆ τ ∧ τ.card = S.card + 1 ∧ τ.sup idx = S.sup idx + 1 ∧
        ∃ v ∈ τ, idx v = τ.sup idx ∧ v.2 = ε) ∧
      ∀ τ' ∈ faces, S ⊆ τ' → τ'.card = S.card + 1 → τ'.sup idx = S.sup idx + 1 →
        (∃ v ∈ τ', idx v = τ'.sup idx ∧ v.2 = ε) → τ' = τ := by
  classical
  set D := S.sup idx with hD
  have himg : S.image idx = Finset.range (D + 1) := by
    refine eq_of_subset_of_card_le idx_image_subset ?_
    rw [Finset.card_range, card_idx_image hS, hcard]
  have hDn : D + 1 < n + 1 := by omega
  set w : Vtx n := (⟨D + 1, hDn⟩, ε) with hw
  have hidxw : idx w = D + 1 := rfl
  have hwnot : w ∉ S := by
    intro hmem
    have : idx w ∈ S.image idx := mem_image.mpr ⟨w, hmem, rfl⟩
    rw [himg, Finset.mem_range, hidxw] at this
    omega
  have hnotidx : ∀ x ∈ S, idx x ≤ D := fun x hx => Finset.le_sup hx
  have hfaceτ : insert w S ∈ faces := by
    refine mem_faces.mpr ⟨⟨w, mem_insert_self _ _⟩, ?_⟩
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
    · rfl
    · exfalso
      have h1 : idx y = D + 1 := by rw [idx, ← hxy]
      have := hnotidx y hy'
      omega
    · exfalso
      have h1 : idx x = D + 1 := by rw [idx, hxy]
      have := hnotidx x hx'
      omega
    · exact (mem_faces.mp hS).2 x hx' y hy' hxy
  have hsupτ : (insert w S).sup idx = D + 1 := by
    rw [Finset.sup_insert, hidxw]
    omega
  refine ⟨insert w S, hfaceτ, ⟨subset_insert _ _, card_insert_of_notMem hwnot, hsupτ,
    ⟨w, mem_insert_self _ _, by rw [hsupτ, hidxw], rfl⟩⟩, ?_⟩
  intro τ' hτ' hsub' hcard' hsup' hex
  obtain ⟨x, hxnot, rfl⟩ := exists_insert hsub' hcard'
  have hidxx : idx x = D + 1 := by
    rw [Finset.sup_insert] at hsup'
    have hle : ∀ y ∈ S, idx y ≤ D := hnotidx
    have hsupS : S.sup idx = D := hD.symm
    omega
  obtain ⟨v, hv, hvidx, hvsgn⟩ := hex
  have hvx : v = x := by
    rcases mem_insert.mp hv with h | h
    · exact h
    · exfalso
      rw [hsup'] at hvidx
      have := hnotidx v h
      omega
  have hx2 : x.2 = ε := by rw [← hvx]; exact hvsgn
  have hx1 : x.1 = (⟨D + 1, hDn⟩ : Fin (n + 1)) := Fin.ext hidxx
  rw [show x = w from Prod.ext hx1 hx2]

/-- The cross-polytope as a flag complex. -/
def cross (n : ℕ) : FlagComplex n where
  V := Vtx n
  decEq := inferInstance
  neg := fun x => (x.1, !x.2)
  lev := idx
  sgn := fun x => x.2
  faces := faces
  base := ((0 : Fin (n + 1)), true)
  neg_neg := fun x => by simp
  lev_le := fun x => by
    have := x.1.isLt
    simp only [idx]
    omega
  lev_neg := fun x => rfl
  sgn_neg := fun x => rfl
  faces_nonempty := fun S hS => (mem_faces.mp hS).1
  faces_down := by
    intro S hS T hsub hne
    exact mem_faces.mpr ⟨hne, fun x hx y hy h => (mem_faces.mp hS).2 x (hsub hx) y (hsub hy) h⟩
  faces_neg := by
    intro S hS
    obtain ⟨hne, hdist⟩ := mem_faces.mp hS
    refine mem_faces.mpr ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨(x.1, !x.2), mem_image_of_mem _ hx⟩
    · intro x hx y hy hxy
      obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
      have : x' = y' := hdist x' hx' y' hy' hxy
      rw [this]
  coherent := by
    intro S hS u hu v hv hulev hvlev
    have : u = v := idx_inj_of_face hS hu hv (by rw [hulev, hvlev])
    rw [this]
  card_le := fun S hS => card_le_sup hS
  facets_two := by
    intro S hS hcard
    exact facets_two_cp hS hcard
  facets_one := by
    intro S hS hcard hlt ε
    exact facets_one_cp hS hcard hlt ε
  base_face := by
    refine mem_faces.mpr ⟨⟨_, mem_singleton_self _⟩, ?_⟩
    intro x hx y hy _
    rw [mem_singleton] at hx hy
    rw [hx, hy]
  base_lev := rfl
  lev_zero := by
    intro S hS v hv hlev
    have h1 : v.1 = (0 : Fin (n + 1)) := Fin.ext hlev
    rcases Bool.eq_false_or_eq_true v.2 with h2 | h2
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 (by rw [h2]; simp))

end CrossPolytope

end GaloisForLFunctions.BorsukUlam
