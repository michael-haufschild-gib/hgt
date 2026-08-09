import Mathlib

/-!
# The Gram-labelled terminal nerve

A labelled simplex is an ordered tuple of source experiments together with a Hermitian Gram label.
It belongs to the nerve of an observer when every vertex has a stable primitive and one common
source synchronization realizes the whole Gram label.  Deleting a label removes its row and column,
and repeating a label repeats them, so the whole structure is stable under arbitrary reindexing and
therefore forms a simplicial set.

This file proves:

* the labelled realizability data assemble into a simplicial set;
* a strengthening of the observer induces a simplicial map, so the nerve is a persistence object;
* death regions are upward closed and contained in the death region of every face, whence the
  numerical face cut is no larger than the numerical cut of the simplex.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open CategoryTheory Simplicial Filter Topology

universe u

/-- A labelled simplex: an ordered tuple of experiments together with a Gram label. -/
abbrev GramSimplex (A : Type u) (n : ℕ) := (Fin n → A) × Matrix (Fin n) (Fin n) ℂ

/-- Reindexing a labelled simplex deletes, repeats or permutes labels together with the
corresponding rows and columns. -/
def gramReindex {A : Type u} {n m : ℕ} (α : Fin n → Fin m) (p : GramSimplex A m) :
    GramSimplex A n := (p.1 ∘ α, fun r s => p.2 (α r) (α s))

@[simp] theorem gramReindex_id {A : Type u} {n : ℕ} (p : GramSimplex A n) :
    gramReindex id p = p := rfl

@[simp] theorem gramReindex_comp {A : Type u} {n m k : ℕ} (α : Fin n → Fin m) (β : Fin m → Fin k)
    (p : GramSimplex A k) : gramReindex α (gramReindex β p) = gramReindex (β ∘ α) p := rfl

/-- The realizability datum of a Gram-labelled terminal nerve at one observer. -/
structure GramNerveDatum (A : Type u) where
  /-- The experiments whose source cocycle has a stable primitive. -/
  vertex : A → Prop
  /-- The labelled tuples realized by one common source synchronization. -/
  realized : ∀ n : ℕ, GramSimplex A n → Prop
  /-- Realizability survives deletion, repetition and permutation of labels. -/
  realized_reindex : ∀ {n m : ℕ} (α : Fin n → Fin m) (p : GramSimplex A m),
    realized m p → realized n (gramReindex α p)

namespace GramNerveDatum

variable {A : Type u} (D : GramNerveDatum A)

/-- A labelled simplex lies in the nerve when every vertex is stable and the whole label is
realized by one common synchronization. -/
def Realizes {n : ℕ} (p : GramSimplex A n) : Prop :=
  (∀ r, D.vertex (p.1 r)) ∧ D.realized n p

theorem Realizes.reindex {n m : ℕ} (α : Fin n → Fin m) {p : GramSimplex A m}
    (h : D.Realizes p) : D.Realizes (gramReindex α p) :=
  ⟨fun r => h.1 (α r), D.realized_reindex α p h.2⟩

/-- Reindexing of realized labelled simplices along a simplex-category morphism. -/
def nerveMapFun {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (p : {p : GramSimplex A (n.unop.len + 1) // D.Realizes p}) :
    {q : GramSimplex A (m.unop.len + 1) // D.Realizes q} :=
  ⟨gramReindex (fun r => α.unop.toOrderHom r) p.1, p.2.reindex D _⟩

/-- **The Gram-labelled terminal nerve is a simplicial set.** -/
def nerve : SSet.{u} where
  obj n := {p : GramSimplex A (n.unop.len + 1) // D.Realizes p}
  map α := ↾(D.nerveMapFun α)
  map_id n := by
    ext p <;> rfl
  map_comp α β := by
    ext p <;> rfl

end GramNerveDatum

namespace GramNerveDatum

variable {A : Type u}

/-! ## Persistence -/

/-- Observer strengthening: more stable vertices and more realized labels. -/
def LE (D D' : GramNerveDatum A) : Prop :=
  (∀ a, D.vertex a → D'.vertex a) ∧ ∀ n p, D.realized n p → D'.realized n p

theorem Realizes.mono {D D' : GramNerveDatum A} (h : LE D D') {n : ℕ} {p : GramSimplex A n}
    (hp : D.Realizes p) : D'.Realizes p :=
  ⟨fun r => h.1 _ (hp.1 r), h.2 n p hp.2⟩

/-- **Persistence.**  Observer strengthening induces a simplicial map of nerves. -/
def nerveMap {D₁ D₂ : GramNerveDatum A} (h : LE D₁ D₂) : nerve D₁ ⟶ nerve D₂ where
  app n := ↾fun p => ⟨p.1, Realizes.mono h p.2⟩
  naturality {n m} α := by
    ext p
    rfl

end GramNerveDatum

/-! ## Death regions -/

section Death

variable {A : Type u} {O : Type*} [Preorder O] (D : O → GramNerveDatum A)

/-- The death region of a labelled simplex: the observers realizing it. -/
def gramDeathRegion {n : ℕ} (p : GramSimplex A n) : Set O := {o | (D o).Realizes p}

/-- **Death regions are upward closed.** -/
theorem isUpperSet_gramDeathRegion (hD : ∀ {o o' : O}, o ≤ o' → GramNerveDatum.LE (D o) (D o'))
    {n : ℕ} (p : GramSimplex A n) : IsUpperSet (gramDeathRegion D p) :=
  fun _ _ hoo hp => GramNerveDatum.Realizes.mono (hD hoo) hp

omit [Preorder O] in
/-- **Every face dies no later than the simplex.** -/
theorem gramDeathRegion_subset_face {n m : ℕ} (α : Fin n → Fin m) (p : GramSimplex A m) :
    gramDeathRegion D p ⊆ gramDeathRegion D (gramReindex α p) :=
  fun _ hp => GramNerveDatum.Realizes.reindex _ α hp

end Death

section NumericalCut

variable {A : Type u} (D : ℝ → GramNerveDatum A)

/-- On a calibrated numerical observer line the infimum cut of a face is no larger than the
infimum cut of the simplex. -/
theorem csInf_face_le_csInf {n m : ℕ} (α : Fin n → Fin m) (p : GramSimplex A m)
    (hne : (gramDeathRegion D p).Nonempty)
    (hbdd : BddBelow (gramDeathRegion D (gramReindex α p))) :
    sInf (gramDeathRegion D (gramReindex α p)) ≤ sInf (gramDeathRegion D p) :=
  csInf_le_csInf hbdd hne (gramDeathRegion_subset_face D α p)

end NumericalCut

/-! ## The concrete nerve of clocked overlaps -/

section Overlaps

variable {A : Type u} {I : Type*}

/-- The realizability datum of a family of clocked overlaps: a labelled tuple is realized when one
allowed synchronization drives the whole overlap matrix to the label. -/
def overlapDatum (stable : A → Prop) (ov : A → A → I → ℂ) (sync : Set (Filter I)) :
    GramNerveDatum A where
  vertex := stable
  realized _ p := ∃ σ ∈ sync, ∀ r s, Tendsto (fun i => ov (p.1 r) (p.1 s) i) σ (𝓝 (p.2 r s))
  realized_reindex := by
    rintro n m α p ⟨σ, hσ, h⟩
    exact ⟨σ, hσ, fun r s => h (α r) (α s)⟩

@[simp] theorem overlapDatum_realized (stable : A → Prop) (ov : A → A → I → ℂ)
    (sync : Set (Filter I)) (n : ℕ) (p : GramSimplex A n) :
    (overlapDatum stable ov sync).realized n p ↔
      ∃ σ ∈ sync, ∀ r s, Tendsto (fun i => ov (p.1 r) (p.1 s) i) σ (𝓝 (p.2 r s)) := Iff.rfl

@[simp] theorem overlapDatum_vertex (stable : A → Prop) (ov : A → A → I → ℂ)
    (sync : Set (Filter I)) (a : A) : (overlapDatum stable ov sync).vertex a ↔ stable a := Iff.rfl

end Overlaps

end GaloisForLFunctions.HTGeometry.Interfinity
