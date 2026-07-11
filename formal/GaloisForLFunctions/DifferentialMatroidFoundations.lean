import GaloisForLFunctions.DifferentialIndependence
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Foundations for the differential-transcendence matroid

The elliptic-gamma structural-matroid cards state differential-transcendence-degree formulas, so the
gluing engine's abstract `Rank` must be differential transcendence degree, i.e. the rank of the
differential-dependence matroid on a differential field.  Unlike the algebraic matroid (already in
mathlib), the differential matroid is genuinely coarser: a hypertranscendental element is a single
independent element although all its jets are algebraically independent.

This file establishes the ground-level structure — the set-relative differential-independence
predicate `DiffIndepOn` and the matroid independence axioms that hold *without* the exchange law:
the empty set is independent, independence passes to subsets, and it is finitary.  The remaining
axiom — differential Steinitz exchange (the card augmentation of `IndepMatroid.ofFinitaryCardAugment`)
— is the differential-algebra theorem that turns this into a matroid; it is developed separately.
-/

open scoped Classical

namespace GaloisForLFunctions

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Differential K]

/-- A subset of a differential field is differentially independent over `k` when the family of all
jets of its elements is algebraically independent — the set form of `DifferentialIndependent`. -/
def DiffIndepOn (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K] [Differential K]
    (s : Set K) : Prop :=
  DifferentialIndependent k (Subtype.val : s → K)

/-- The empty set is differentially independent. -/
theorem diffIndepOn_empty : DiffIndepOn k (∅ : Set K) := by
  unfold DiffIndepOn DifferentialIndependent
  have : IsEmpty ((∅ : Set K) × ℕ) := by
    constructor; rintro ⟨⟨x, hx⟩, _⟩; exact hx.elim
  exact algebraicIndependent_empty_type

/-- Differential independence passes to subsets. -/
theorem DiffIndepOn.subset {s t : Set K} (hs : DiffIndepOn k s) (hts : t ⊆ s) :
    DiffIndepOn k t := by
  unfold DiffIndepOn DifferentialIndependent at hs ⊢
  exact hs.comp (fun p : t × ℕ => (⟨p.1.1, hts p.1.2⟩, p.2)) (by
    rintro ⟨⟨a, ha⟩, m⟩ ⟨⟨b, hb⟩, n⟩ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl)

/-- Differential independence is finitary: if every finite subset is differentially independent, so
is the whole set. -/
theorem diffIndepOn_of_forall_finite {s : Set K}
    (H : ∀ t : Set K, t ⊆ s → t.Finite → DiffIndepOn k t) : DiffIndepOn k s := by
  unfold DiffIndepOn DifferentialIndependent at H ⊢
  -- reduce to finitely-generated subfamilies of the jet family
  apply algebraicIndependent_of_finite_type
  intro F hF
  -- `F : Set (s × ℕ)` finite; its element-projection is a finite subset `t ⊆ s`
  set t : Set K := (fun p : s × ℕ => (p.1 : K)) '' F with ht
  have htsub : t ⊆ s := by
    rintro x ⟨p, -, rfl⟩; exact p.1.2
  have htfin : t.Finite := hF.image _
  have hti := H t htsub htfin
  -- the jets of `t` include every jet indexed by `F`; restrict
  have hemb : ∀ p : s × ℕ, p ∈ F → differentialJet p.2 (p.1 : K) ∈
      Set.range (fun q : t × ℕ => differentialJet q.2 (q.1 : K)) := by
    intro p hp
    exact ⟨(⟨(p.1 : K), ⟨p, hp, rfl⟩⟩, p.2), rfl⟩
  -- build the reindexing `F → t × ℕ`
  have : AlgebraicIndependent k
      (fun p : F => differentialJet (p.1.2) ((p.1.1 : K))) := by
    have hcomp := hti.comp
      (fun p : F => (⟨(p.1.1 : K), ⟨p.1, p.2, rfl⟩⟩, p.1.2) : F → t × ℕ) (by
        rintro ⟨⟨⟨a, ha⟩, m⟩, hmem⟩ ⟨⟨⟨b, hb⟩, n⟩, hmem'⟩ h
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl)
    simpa using hcomp
  simpa using this

end GaloisForLFunctions
