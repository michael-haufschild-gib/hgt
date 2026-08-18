import GaloisForLFunctions.HTGeometry.WeightedComplexLink
import GaloisForLFunctions.HTGeometry.IncidenceDesignBound
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum

/-!
# Incidence complexes as weighted complexes

The rank-two spherical building of a projective plane is a bipartite incidence complex.  This file
places that exact combinatorial object in the `WeightedComplex` interface consumed by Garland
localization.  The weight of a point-line pair is one exactly when it is incident.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L] [Membership P L]

local instance (p : P) (l : L) : Decidable (p ∈ l) := Classical.propDecidable _

/-- The unit-weighted one-dimensional complex whose top faces are the incident point-line pairs. -/
noncomputable def incidenceWeightedComplex : WeightedComplex (P ⊕ L) := by
  classical
  exact unitComplex ((univ : Finset (P ⊕ L)).powerset.filter fun s =>
    ∃ p : P, ∃ l : L, p ∈ l ∧ s = {Sum.inl p, Sum.inr l})

/-- The top faces of the incidence weighted complex are exactly its incident point-line pairs. -/
theorem mem_incidenceWeightedComplex_top_iff {s : Finset (P ⊕ L)} :
    s ∈ (incidenceWeightedComplex (P := P) (L := L)).top ↔
      ∃ p : P, ∃ l : L, p ∈ l ∧ s = {Sum.inl p, Sum.inr l} := by
  classical
  simp [incidenceWeightedComplex]

/-- An incidence top face containing a specified point-line pair is that pair itself. -/
theorem incidenceWeightedComplex_top_containing_pair {p : P} {l : L} {s : Finset (P ⊕ L)}
    (hs : s ∈ (incidenceWeightedComplex (P := P) (L := L)).top)
    (hsub : {Sum.inl p, Sum.inr l} ⊆ s) : p ∈ l ∧ s = {Sum.inl p, Sum.inr l} := by
  obtain ⟨p', l', hp'l', hs'⟩ := mem_incidenceWeightedComplex_top_iff.mp hs
  have hp : Sum.inl p ∈ s := hsub (by simp)
  have hl : Sum.inr l ∈ s := hsub (by simp)
  rw [hs'] at hp hl
  have hpp' : p = p' := by simpa using hp
  have hll' : l = l' := by simpa using hl
  subst p'
  subst l'
  exact ⟨hp'l', hs'⟩

/-- No face of an incidence complex contains two distinct point vertices. -/
theorem incidenceWeightedComplex_not_isFace_inl_inl_of_ne (p p' : P) (hne : p ≠ p') :
    ¬ (incidenceWeightedComplex (P := P) (L := L)).IsFace {Sum.inl p, Sum.inl p'} := by
  rintro ⟨s, hs, hsub⟩
  obtain ⟨q, l, -, hs'⟩ := mem_incidenceWeightedComplex_top_iff.mp hs
  have hp : Sum.inl p ∈ s := hsub (by simp)
  have hp' : Sum.inl p' ∈ s := hsub (by simp)
  rw [hs'] at hp hp'
  have hpq : p = q := by simpa using hp
  have hp'q : p' = q := by simpa using hp'
  exact hne (hpq.trans hp'q.symm)

/-- No face of an incidence complex contains two distinct line vertices. -/
theorem incidenceWeightedComplex_not_isFace_inr_inr_of_ne (l l' : L) (hne : l ≠ l') :
    ¬ (incidenceWeightedComplex (P := P) (L := L)).IsFace {Sum.inr l, Sum.inr l'} := by
  rintro ⟨s, hs, hsub⟩
  obtain ⟨p, q, -, hs'⟩ := mem_incidenceWeightedComplex_top_iff.mp hs
  have hl : Sum.inr l ∈ s := hsub (by simp)
  have hl' : Sum.inr l' ∈ s := hsub (by simp)
  rw [hs'] at hl hl'
  have hlq : l = q := by simpa using hl
  have hl'q : l' = q := by simpa using hl'
  exact hne (hlq.trans hl'q.symm)

/-- The induced face weight of a point-line pair is the incidence indicator. -/
theorem incidenceWeightedComplex_m_pair (p : P) (l : L) :
    (incidenceWeightedComplex (P := P) (L := L)).m {Sum.inl p, Sum.inr l}
      = if p ∈ l then 1 else 0 := by
  classical
  let T : Finset (Finset (P ⊕ L)) := (univ : Finset (P ⊕ L)).powerset.filter fun s =>
    ∃ p : P, ∃ l : L, p ∈ l ∧ s = {Sum.inl p, Sum.inr l}
  change (unitComplex T).m {Sum.inl p, Sum.inr l} = if p ∈ l then 1 else 0
  rw [unitComplex_m]
  by_cases hpl : p ∈ l
  · have hmem : {Sum.inl p, Sum.inr l} ∈ T.filter (fun s => {Sum.inl p, Sum.inr l} ⊆ s) := by
      refine Finset.mem_filter.2 ⟨?_, subset_rfl⟩
      dsimp [T]
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
      exact ⟨p, l, hpl, rfl⟩
    have hsingle : T.filter (fun s => {Sum.inl p, Sum.inr l} ⊆ s) =
        {{Sum.inl p, Sum.inr l}} := by
      ext s
      constructor
      · intro hs
        have hsT : s ∈ (incidenceWeightedComplex (P := P) (L := L)).top := by
          change s ∈ T
          exact (Finset.mem_filter.1 hs).1
        have hsub : {Sum.inl p, Sum.inr l} ⊆ s := (Finset.mem_filter.1 hs).2
        exact Finset.mem_singleton.mpr (incidenceWeightedComplex_top_containing_pair hsT hsub).2
      · intro hs
        have hs' : s = {Sum.inl p, Sum.inr l} := Finset.mem_singleton.mp hs
        subst s
        exact hmem
    rw [hsingle, if_pos hpl]
    norm_num
  · have hempty : T.filter (fun s => {Sum.inl p, Sum.inr l} ⊆ s) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨s, hs⟩
      have hsT : s ∈ (incidenceWeightedComplex (P := P) (L := L)).top := by
        change s ∈ T
        exact (Finset.mem_filter.1 hs).1
      have hsub : {Sum.inl p, Sum.inr l} ⊆ s := (Finset.mem_filter.1 hs).2
      exact hpl (incidenceWeightedComplex_top_containing_pair hsT hsub).1
    rw [hempty, if_neg hpl]
    norm_num

/-- The incidence weighted complex is pure of dimension one. -/
theorem incidenceWeightedComplex_pure :
    ∀ s ∈ (incidenceWeightedComplex (P := P) (L := L)).top, s.card = 2 := by
  intro s hs
  obtain ⟨p, l, -, rfl⟩ := mem_incidenceWeightedComplex_top_iff.mp hs
  simp

/-- On the point-to-line component of the empty link, the induced graph weight is exactly the
incidence indicator. -/
theorem incidenceWeightedComplex_linkGraph_empty_w_inl_inr (p : P) (l : L) :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).w (Sum.inl p) (Sum.inr l)
      = if p ∈ l then 1 else 0 := by
  rw [WeightedComplex.linkGraph_w_eq, if_neg (by simp)]
  simpa only [Finset.insert_empty] using incidenceWeightedComplex_m_pair p l

/-- The reverse point-line edge of the empty link has the same incidence weight. -/
theorem incidenceWeightedComplex_linkGraph_empty_w_inr_inl (p : P) (l : L) :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).w (Sum.inr l) (Sum.inl p)
      = if p ∈ l then 1 else 0 := by
  rw [WeightedComplex.linkGraph_w_eq, if_neg (by simp)]
  rw [Finset.insert_empty]
  have hpair : ({Sum.inr l, Sum.inl p} : Finset (P ⊕ L)) = {Sum.inl p, Sum.inr l} := by
    ext x
    simp [or_comm]
  rw [hpair]
  exact incidenceWeightedComplex_m_pair p l

/-- Same-side point weights in the empty link vanish. -/
theorem incidenceWeightedComplex_linkGraph_empty_w_inl_inl (p p' : P) :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).w (Sum.inl p) (Sum.inl p') = 0 := by
  by_cases h : p = p'
  · subst p'
    rw [WeightedComplex.linkGraph_w_eq, if_pos (Or.inl rfl)]
  · rw [WeightedComplex.linkGraph_w_eq, if_neg (by simp [h])]
    simpa only [Finset.insert_empty] using
      (WeightedComplex.m_eq_zero_of_not_isFace (incidenceWeightedComplex (P := P) (L := L))
        (incidenceWeightedComplex_not_isFace_inl_inl_of_ne p p' h))

/-- Same-side line weights in the empty link vanish. -/
theorem incidenceWeightedComplex_linkGraph_empty_w_inr_inr (l l' : L) :
    ((incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅).w (Sum.inr l) (Sum.inr l') = 0 := by
  by_cases h : l = l'
  · subst l'
    rw [WeightedComplex.linkGraph_w_eq, if_pos (Or.inl rfl)]
  · rw [WeightedComplex.linkGraph_w_eq, if_neg (by simp [h])]
    simpa only [Finset.insert_empty] using
      (WeightedComplex.m_eq_zero_of_not_isFace (incidenceWeightedComplex (P := P) (L := L))
        (incidenceWeightedComplex_not_isFace_inr_inr_of_ne l l' h))

/-- The empty link of the incidence weighted complex is exactly its bipartite incidence graph. -/
theorem incidenceWeightedComplex_linkGraph_empty_eq_incidenceGraph :
    (incidenceWeightedComplex (P := P) (L := L)).linkGraph ∅ =
      incidenceGraph (fun p : P => fun l : L => if p ∈ l then 1 else 0)
        (fun p l => by split_ifs <;> norm_num) := by
  ext u v
  cases u with
  | inl p =>
    cases v with
    | inl p' =>
      simpa [incidenceGraph, incW] using incidenceWeightedComplex_linkGraph_empty_w_inl_inl p p'
    | inr l =>
      simpa [incidenceGraph, incW] using incidenceWeightedComplex_linkGraph_empty_w_inl_inr p l
  | inr l =>
    cases v with
    | inl p =>
      simpa [incidenceGraph, incW] using incidenceWeightedComplex_linkGraph_empty_w_inr_inl p l
    | inr l' =>
      simpa [incidenceGraph, incW] using incidenceWeightedComplex_linkGraph_empty_w_inr_inr l l'

end

end GaloisForLFunctions.HTGeometry
