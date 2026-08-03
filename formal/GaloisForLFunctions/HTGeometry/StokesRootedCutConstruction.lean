import GaloisForLFunctions.HTGeometry.StokesContactTomography
import GaloisForLFunctions.HTGeometry.StokesEnergyTree

/-!
# Canonical positive cuts constructed from a finite rooted contact tree

Every nonroot vertex supplies its descendant-leaf cut.  Its length is the drop of the strictly
antitone contact potential from its predecessor.  Finite predecessor induction proves the exact
telescoping identity, so polarization needs no independently supplied cut certificate.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

namespace RootedContactTree

variable {n : ℕ}

/-- Vertices on the nonroot path from the root to `x`. -/
noncomputable def nonRootAncestors (t : RootedContactTree n) (x : t.tree) : Finset t.tree := by
  classical
  exact Finset.univ.filter fun v => v ≠ ⊥ ∧ v ≤ x

/-- Drop of contact height across the incoming edge; the unused root coordinate gets length one. -/
noncomputable def vertexLength (t : RootedContactTree n) (v : t.tree) : ℝ := by
  classical
  exact if v = ⊥ then 1 else t.kappa (Order.pred v) - t.kappa v

/-- Sum of incoming-edge drops on the root path to `x`. -/
noncomputable def pathLoss (t : RootedContactTree n) (x : t.tree) : ℝ :=
  ∑ v ∈ t.nonRootAncestors x, t.vertexLength v

@[simp] theorem nonRootAncestors_root (t : RootedContactTree n) :
    t.nonRootAncestors (⊥ : t.tree) = ∅ := by
  classical
  ext v
  simp [nonRootAncestors]

@[simp] theorem pathLoss_root (t : RootedContactTree n) :
    t.pathLoss (⊥ : t.tree) = 0 := by
  simp [pathLoss]

/-- The ancestor path to a nonroot vertex is that vertex followed by the path to its predecessor. -/
theorem nonRootAncestors_eq_insert_pred (t : RootedContactTree n) {x : t.tree}
    (hx : x ≠ ⊥) :
    t.nonRootAncestors x = insert x (t.nonRootAncestors (Order.pred x)) := by
  classical
  ext v
  simp only [nonRootAncestors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨hvroot, hvx⟩
    rcases (Order.le_iff_eq_or_le_pred.mp hvx) with rfl | hvpred
    · exact Or.inl rfl
    · exact Or.inr ⟨hvroot, hvpred⟩
  · rintro (rfl | ⟨hvroot, hvpred⟩)
    · exact ⟨hx, le_rfl⟩
    · exact ⟨hvroot, hvpred.trans (Order.pred_le x)⟩

/-- Root-path loss obeys the incoming-edge recurrence. -/
theorem pathLoss_eq_vertexLength_add_pred (t : RootedContactTree n) {x : t.tree}
    (hx : x ≠ ⊥) :
    t.pathLoss x = t.vertexLength x + t.pathLoss (Order.pred x) := by
  classical
  rw [pathLoss, t.nonRootAncestors_eq_insert_pred hx, Finset.sum_insert]
  · rfl
  · simp [nonRootAncestors, hx]

/-- Exact potential-drop law on every finite rooted path. -/
theorem pathLoss_eq_root_sub (t : RootedContactTree n) (x : t.tree) :
    t.pathLoss x = t.kappa ⊥ - t.kappa x := by
  classical
  let P : (v : t.tree) → v ≤ x → Prop := fun v _ =>
    t.pathLoss x = t.kappa v - t.kappa x + t.pathLoss v
  have hbot : (⊥ : t.tree) ≤ x := bot_le
  have hP : P (⊥ : t.tree) hbot := by
    refine Pred.rec (m := x) (P := P) ?_ ?_ hbot
    · simp [P]
    · intro v hvx ih
      by_cases hvroot : v = ⊥
      · subst v
        simpa [P] using ih
      · have hrec := t.pathLoss_eq_vertexLength_add_pred hvroot
        simp only [P] at ih ⊢
        rw [ih, hrec]
        simp [vertexLength, hvroot]
        ring
  simpa [P] using hP

/-- Canonical finite coordinate equivalence for tree vertices. -/
noncomputable def vertexEquiv (t : RootedContactTree n) :
    t.tree ≃ Fin (Fintype.card t.tree) :=
  Fintype.equivFin t.tree

/-- Vertex represented by a canonical finite coordinate. -/
noncomputable def vertexAt (t : RootedContactTree n)
    (e : Fin (Fintype.card t.tree)) : t.tree :=
  t.vertexEquiv.symm e

/-- Descendant indicator for a nonroot vertex. -/
noncomputable def vertexSide (t : RootedContactTree n)
    (e : Fin (Fintype.card t.tree)) (i : Fin n) : ℝ :=
  by
    classical
    exact if t.vertexAt e = ⊥ then 0 else if t.vertexAt e ≤ t.leaf i then 1 else 0

/-- Coordinate of a labelled pendant vertex. -/
noncomputable def pendantVertex (t : RootedContactTree n) (i : Fin n) :
    Fin (Fintype.card t.tree) :=
  t.vertexEquiv (t.leaf i)

@[simp] theorem vertexAt_pendantVertex (t : RootedContactTree n) (i : Fin n) :
    t.vertexAt (t.pendantVertex i) = t.leaf i := by
  simp [vertexAt, pendantVertex, vertexEquiv]

/-- Each pendant coordinate is the singleton indicator of its labelled leaf. -/
theorem vertexSide_pendant (t : RootedContactTree n) (i j : Fin n) :
    t.vertexSide (t.pendantVertex i) j = if j = i then 1 else 0 := by
  classical
  rw [vertexSide, t.vertexAt_pendantVertex]
  simp only [t.leaf_ne_root i, if_false]
  by_cases hji : j = i
  · subst j
    simp
  · have hnot : ¬t.leaf i ≤ t.leaf j := t.leaf_antichain i j (Ne.symm hji)
    simp [hji, hnot]

/-- Every canonical vertex length is strictly positive. -/
theorem vertexLength_pos (t : RootedContactTree n) (v : t.tree) :
    0 < t.vertexLength v := by
  classical
  by_cases hv : v = ⊥
  · simp [vertexLength, hv]
  · simp only [vertexLength, hv, if_false]
    exact sub_pos.mpr (t.kappa_strictAnti (Order.pred_lt_iff_ne_bot.mpr hv))

/-- Canonical positive rooted cut family constructed from the rooted tree alone. -/
noncomputable def canonicalCuts (t : RootedContactTree n) :
    RootedCutContact n (Fintype.card t.tree) := by
  classical
  exact {
    length := fun e => t.vertexLength (t.vertexAt e)
    side := fun e i => t.vertexSide e i
    length_pos := fun e => t.vertexLength_pos (t.vertexAt e)
    pendant := t.pendantVertex
    pendant_side := t.vertexSide_pendant
    root := t.kappa ⊥
    side_idempotent := by
      intro e i
      simp [vertexSide] }

/-- Canonical cut bilinear sum is exactly root-path loss to the least common ancestor. -/
theorem canonicalCutSum_eq_pathLoss (t : RootedContactTree n) (i j : Fin n) :
    (∑ e, t.canonicalCuts.length e *
      (t.canonicalCuts.side e i * t.canonicalCuts.side e j)) =
        t.pathLoss (t.leaf i ⊓ t.leaf j) := by
  classical
  let g : t.tree → ℝ := fun v =>
    t.vertexLength v * (if v ≠ ⊥ ∧ v ≤ t.leaf i ⊓ t.leaf j then 1 else 0)
  calc
    (∑ e, t.canonicalCuts.length e *
      (t.canonicalCuts.side e i * t.canonicalCuts.side e j)) =
        ∑ e, g (t.vertexAt e) := by
          apply Finset.sum_congr rfl
          intro e _
          simp only [canonicalCuts]
          by_cases hroot : t.vertexAt e = ⊥
          · simp [g, vertexSide, hroot]
          · by_cases hi : t.vertexAt e ≤ t.leaf i
            · by_cases hj : t.vertexAt e ≤ t.leaf j
              · simp [g, vertexSide, hroot, hi, hj]
              · simp [g, vertexSide, hroot, hi, hj]
            · simp [g, vertexSide, hroot, hi]
    _ = ∑ v : t.tree, g v := Equiv.sum_comp t.vertexEquiv.symm g
    _ = t.pathLoss (t.leaf i ⊓ t.leaf j) := by
      rw [pathLoss, nonRootAncestors, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      change t.vertexLength v *
          (if v ≠ ⊥ ∧ v ≤ t.leaf i ⊓ t.leaf j then 1 else 0) =
        if v ≠ ⊥ ∧ v ≤ t.leaf i ⊓ t.leaf j then t.vertexLength v else 0
      by_cases h : v ≠ ⊥ ∧ v ≤ t.leaf i ⊓ t.leaf j
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring

/-- The constructed cuts recover the original complementary-contact matrix exactly. -/
theorem canonicalCuts_contact_eq (t : RootedContactTree n) (i j : Fin n) :
    t.canonicalCuts.contact i j = t.contact i j := by
  rw [RootedCutContact.contact, t.canonicalCutSum_eq_pathLoss,
    t.pathLoss_eq_root_sub]
  simp [canonicalCuts, contact]

/-- Constructed cut energy equals polarization of rooted contact. -/
theorem canonicalCuts_energy_eq (t : RootedContactTree n) (i j : Fin n) :
    t.canonicalCuts.energy i j = t.energy i j := by
  simp only [RootedCutContact.energy, energy]
  rw [t.canonicalCuts_contact_eq, t.canonicalCuts_contact_eq,
    t.canonicalCuts_contact_eq]

/-- Every finite rooted contact tree has an unconditional explicit squared-Euclidean energy
embedding; no separate cut certificate is assumed. -/
theorem energy_has_canonical_sqEmbedding (t : RootedContactTree n) (i j : Fin n) :
    (∑ e, (t.canonicalCuts.toPositivePendantCutFamily.feature i e -
      t.canonicalCuts.toPositivePendantCutFamily.feature j e) ^ 2) = t.energy i j := by
  rw [← t.canonicalCuts_energy_eq]
  exact t.canonicalCuts.energy_has_explicit_sqEmbedding i j

/-- Every finite rooted contact energy has strict negative type, derived from its canonical
pendant cuts. -/
theorem energy_strict_negative_type (t : RootedContactTree n) {x : Fin n → ℝ}
    (hsum : ∑ i, x i = 0) (hx : x ≠ 0) :
    (∑ i, ∑ j, x i * x j * t.energy i j) < 0 := by
  simp_rw [← t.canonicalCuts_energy_eq]
  exact t.canonicalCuts.energy_strict_negative_type hsum hx

/-- Rooted contact energy strictly separates distinct leaves without auxiliary certificates. -/
theorem energy_pos_of_ne (t : RootedContactTree n) {i j : Fin n} (hij : i ≠ j) :
    0 < t.energy i j := by
  rw [← t.canonicalCuts_energy_eq]
  exact t.canonicalCuts.energy_pos_of_ne hij

end RootedContactTree

end IrregularStokes
end GaloisForLFunctions
