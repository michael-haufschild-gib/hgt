import GaloisForLFunctions.HTGeometry.WeightedMatroidGreedyStability

/-!
# Positive-support invariance of weighted matroid greedy

Zero and negative coordinates never enter the positive-weight greedy set and never precede a
positive selected coordinate. Hence greedy depends only on the visible positive support. This is
the formal oracle-locality mechanism behind Observation 3.2 in the matroid secretary reduction.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*}

/-- Positive-weight part of the available ground set. -/
noncomputable def positiveWeightSupport (V : Finset α) (w : α → ℝ) : Finset α := by
  classical
  exact V.filter fun e => 0 < w e

@[simp] theorem mem_positiveWeightSupport (V : Finset α) (w : α → ℝ) (e : α) :
    e ∈ positiveWeightSupport V w ↔ e ∈ V ∧ 0 < w e := by
  classical
  simp [positiveWeightSupport]

variable [LinearOrder α]

/-- For a positive element, discarding all nonpositive available elements does not change its
greedy predecessor set. -/
theorem weightedPredecessors_positiveWeightSupport_eq
    (V : Finset α) (w : α → ℝ) {e : α} (he : 0 < w e) :
    weightedPredecessors (positiveWeightSupport V w) w e =
      weightedPredecessors V w e := by
  ext f
  constructor
  · rintro ⟨hfV, hbefore⟩
    exact ⟨(mem_positiveWeightSupport V w f).mp hfV |>.1, hbefore⟩
  · rintro ⟨hfV, hbefore⟩
    refine ⟨(mem_positiveWeightSupport V w f).mpr ⟨hfV, ?_⟩, hbefore⟩
    rcases hbefore with hlt | ⟨hEq, _⟩
    · exact lt_trans he hlt
    · simpa [← hEq] using he

/-- Deterministic weighted matroid greedy depends only on the positive-weight support. -/
theorem matroidGreedySet_positiveWeightSupport
    (M : Matroid α) (V : Finset α) (w : α → ℝ) :
    matroidGreedySet M (positiveWeightSupport V w) w = matroidGreedySet M V w := by
  ext e
  by_cases he : 0 < w e
  · rw [mem_matroidGreedySet, mem_matroidGreedySet,
      weightedPredecessors_positiveWeightSupport_eq V w he]
    simp [he]
  · simp [mem_matroidGreedySet, he]

/-- Two available sets with the same positive-weight support produce the same greedy set. -/
theorem matroidGreedySet_eq_of_positiveWeightSupport_eq
    (M : Matroid α) {V W : Finset α} (w : α → ℝ)
    (h : positiveWeightSupport V w = positiveWeightSupport W w) :
    matroidGreedySet M V w = matroidGreedySet M W w := by
  rw [← matroidGreedySet_positiveWeightSupport M V w,
    ← matroidGreedySet_positiveWeightSupport M W w, h]

/-- Every positive available element is spanned by the greedy set. The proof chooses the first
unspanned positive element in greedy order; all of its predecessors are then already spanned,
contradicting its rejection by greedy. -/
theorem positiveWeightSupport_subset_closure_matroidGreedySet
    (M : Matroid α) (V : Finset α) (w : α → ℝ) (hVE : (V : Set α) ⊆ M.E) :
    (positiveWeightSupport V w : Set α) ⊆
      M.closure (matroidGreedySet M V w : Set α) := by
  classical
  let G := matroidGreedySet M V w
  let P := positiveWeightSupport V w
  let bad := P.filter fun e => e ∉ M.closure (G : Set α)
  have hGind : M.Indep (G : Set α) := matroidGreedySet_indep M V w hVE
  intro e heP
  by_contra heCl
  have heBad : e ∈ bad := by
    simp only [bad, Finset.mem_filter]
    exact ⟨heP, heCl⟩
  obtain ⟨a, haBad, hmin⟩ :=
    Finset.exists_min_image bad (weightedGreedyKey w) ⟨e, heBad⟩
  have haP : a ∈ P := (Finset.mem_filter.mp haBad).1
  have haNotCl : a ∉ M.closure (G : Set α) := (Finset.mem_filter.mp haBad).2
  have haNotG : a ∉ G := by
    intro haG
    exact haNotCl (M.subset_closure (G : Set α) hGind.subset_ground haG)
  have haData : a ∈ V ∧ 0 < w a := by
    simpa [P] using (mem_positiveWeightSupport V w a).mp haP
  have haPredCl : a ∈ M.closure (weightedPredecessors V w a) := by
    by_contra haPred
    exact haNotG ((mem_matroidGreedySet M V w a).mpr ⟨haData.1, haData.2, haPred⟩)
  have hPredSub : weightedPredecessors V w a ⊆ M.closure (G : Set α) := by
    intro f hf
    have hfKey : weightedGreedyKey w f < weightedGreedyKey w a :=
      ((mem_weightedPredecessors_iff_key_lt V w a f).mp hf).2
    have hfData : f ∈ V ∧ 0 < w f := by
      rcases hf with ⟨hfV, hbefore⟩
      refine ⟨hfV, ?_⟩
      rcases hbefore with hlt | ⟨heq, _⟩
      · exact lt_trans haData.2 hlt
      · simpa [← heq] using haData.2
    have hfP : f ∈ P := by
      simpa [P] using (mem_positiveWeightSupport V w f).mpr hfData
    by_contra hfCl
    have hfBad : f ∈ bad := by
      simp only [bad, Finset.mem_filter]
      exact ⟨hfP, hfCl⟩
    exact (not_lt_of_ge (hmin f hfBad)) hfKey
  have haDouble : a ∈ M.closure (M.closure (G : Set α)) :=
    M.closure_mono hPredSub haPredCl
  exact haNotCl (by simpa using haDouble)

/-- Weighted greedy is a basis of the positive-weight support, not just an independent subset. -/
theorem matroidGreedySet_isBasis_positiveWeightSupport
    (M : Matroid α) (V : Finset α) (w : α → ℝ) (hVE : (V : Set α) ⊆ M.E) :
    M.IsBasis (matroidGreedySet M V w : Set α) (positiveWeightSupport V w : Set α) := by
  refine (matroidGreedySet_indep M V w hVE).isBasis_of_subset_of_subset_closure ?_ ?_
  · intro e he
    have he' : e ∈ matroidGreedySet M V w := he
    rw [mem_matroidGreedySet] at he'
    exact (mem_positiveWeightSupport V w e).mpr ⟨he'.1, he'.2.1⟩
  · exact positiveWeightSupport_subset_closure_matroidGreedySet M V w hVE

/-- If changing one still-positive coordinate changes another greedy membership, the two greedy
bases exchange exactly those two elements. This is the sharp form of one-coordinate sensitivity. -/
theorem matroidGreedySet_exchange_of_greedyMembershipChanged
    (M : Matroid α) (V : Finset α) (w w' : α → ℝ) (e : α)
    (hVE : (V : Set α) ⊆ M.E) (hoff : ∀ x, x ≠ e → w x = w' x)
    (hepos : 0 < w e) (hepos' : 0 < w' e) {f : α} (hfe : f ≠ e)
    (hfchange : GreedyMembershipChanged M V w w' f) :
    ((f ∈ matroidGreedySet M V w ∧ f ∉ matroidGreedySet M V w') ∧
        (e ∉ matroidGreedySet M V w ∧ e ∈ matroidGreedySet M V w') ∧
        (matroidGreedySet M V w).erase f = (matroidGreedySet M V w').erase e) ∨
      ((f ∉ matroidGreedySet M V w ∧ f ∈ matroidGreedySet M V w') ∧
        (e ∈ matroidGreedySet M V w ∧ e ∉ matroidGreedySet M V w') ∧
        (matroidGreedySet M V w).erase e = (matroidGreedySet M V w').erase f) := by
  classical
  let G := matroidGreedySet M V w
  let G' := matroidGreedySet M V w'
  let P := positiveWeightSupport V w
  have hPsupport : positiveWeightSupport V w = positiveWeightSupport V w' := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [hepos, hepos']
    · simp [hoff x hxe]
  have hB : M.IsBasis (G : Set α) (P : Set α) := by
    simpa [G, P] using matroidGreedySet_isBasis_positiveWeightSupport M V w hVE
  have hB' : M.IsBasis (G' : Set α) (P : Set α) := by
    simpa [G', P, hPsupport] using matroidGreedySet_isBasis_positiveWeightSupport M V w' hVE
  have hchangedSub := greedyMembershipChanged_off_coordinate_subsingleton M V w w' e hoff
  have hsame : ∀ {x}, x ≠ e → x ≠ f → (x ∈ G ↔ x ∈ G') := by
    intro x hxe hxf
    by_contra hne
    have hxchange : x ∈ {y | y ≠ e ∧ GreedyMembershipChanged M V w w' y} :=
      ⟨hxe, (xor_iff_not_iff _ _).mpr hne⟩
    have hfmem : f ∈ {y | y ≠ e ∧ GreedyMembershipChanged M V w w' y} :=
      ⟨hfe, hfchange⟩
    exact hxf (hchangedSub hxchange hfmem)
  have hresult :
      ((f ∈ G ∧ f ∉ G') ∧ (e ∉ G ∧ e ∈ G') ∧ G.erase f = G'.erase e) ∨
        ((f ∉ G ∧ f ∈ G') ∧ (e ∈ G ∧ e ∉ G') ∧ G.erase e = G'.erase f) := by
    rcases hfchange with hf | hf
    · left
      have heG' : e ∈ G' := by
        by_contra heG'
        have hsub : (G' : Set α) ⊆ (G : Set α) := by
          intro x hx
          by_cases hxe : x = e
          · subst x
            exact (heG' hx).elim
          by_cases hxf : x = f
          · subst x
            exact (hf.2 hx).elim
          exact (hsame hxe hxf).mpr hx
        have hEq : (G' : Set α) = (G : Set α) :=
          hB'.eq_of_subset_indep hB.indep hsub hB.subset
        have hEqFin : G' = G := Finset.coe_injective hEq
        exact hf.2 (by simpa [hEqFin] using hf.1)
      have heG : e ∉ G := by
        intro heG
        have hsub : (G' : Set α) ⊆ (G : Set α) := by
          intro x hx
          by_cases hxe : x = e
          · simpa [hxe] using heG
          by_cases hxf : x = f
          · subst x
            exact (hf.2 hx).elim
          exact (hsame hxe hxf).mpr hx
        have hEq : (G' : Set α) = (G : Set α) :=
          hB'.eq_of_subset_indep hB.indep hsub hB.subset
        have hEqFin : G' = G := Finset.coe_injective hEq
        exact hf.2 (by simpa [hEqFin] using hf.1)
      refine ⟨hf, ⟨heG, heG'⟩, ?_⟩
      ext x
      simp only [Finset.mem_erase]
      by_cases hxe : x = e
      · subst x
        simp only [heG, and_false, ne_eq, not_true_eq_false, false_and]
      by_cases hxf : x = f
      · subst x
        simp only [ne_eq, not_true_eq_false, false_and, hf.2, and_false]
      simpa only [hxf, hxe, not_false_eq_true, true_and] using hsame hxe hxf
    · right
      have heG : e ∈ G := by
        by_contra heG
        have hsub : (G : Set α) ⊆ (G' : Set α) := by
          intro x hx
          by_cases hxe : x = e
          · subst x
            exact (heG hx).elim
          by_cases hxf : x = f
          · subst x
            exact (hf.2 hx).elim
          exact (hsame hxe hxf).mp hx
        have hEq : (G : Set α) = (G' : Set α) :=
          hB.eq_of_subset_indep hB'.indep hsub hB'.subset
        have hEqFin : G = G' := Finset.coe_injective hEq
        exact hf.2 (by simpa [hEqFin] using hf.1)
      have heG' : e ∉ G' := by
        intro heG'
        have hsub : (G : Set α) ⊆ (G' : Set α) := by
          intro x hx
          by_cases hxe : x = e
          · simpa [hxe] using heG'
          by_cases hxf : x = f
          · subst x
            exact (hf.2 hx).elim
          exact (hsame hxe hxf).mp hx
        have hEq : (G : Set α) = (G' : Set α) :=
          hB.eq_of_subset_indep hB'.indep hsub hB'.subset
        have hEqFin : G = G' := Finset.coe_injective hEq
        exact hf.2 (by simpa [hEqFin] using hf.1)
      refine ⟨⟨hf.2, hf.1⟩, ⟨heG, heG'⟩, ?_⟩
      ext x
      simp only [Finset.mem_erase]
      by_cases hxe : x = e
      · subst x
        simp only [ne_eq, not_true_eq_false, false_and, heG', and_false]
      by_cases hxf : x = f
      · subst x
        simp only [hf.2, and_false, ne_eq, not_true_eq_false, false_and]
      simpa only [hxe, hxf, not_false_eq_true, true_and] using hsame hxe hxf
  simpa [G, G'] using hresult

/-- Adding a constant to every weight preserves all predecessor sets. -/
theorem weightedPredecessors_add_const
    (V : Finset α) (w : α → ℝ) (c : ℝ) (e : α) :
    weightedPredecessors V (fun x => w x + c) e = weightedPredecessors V w e := by
  ext f
  simp [weightedPredecessors]

/-- A nonnegative uniform shift cannot remove any previously selected greedy element. -/
theorem matroidGreedySet_subset_add_const
    (M : Matroid α) (V : Finset α) (w : α → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    matroidGreedySet M V w ⊆ matroidGreedySet M V (fun x => w x + c) := by
  intro e he
  rw [mem_matroidGreedySet] at he ⊢
  rw [weightedPredecessors_add_const]
  exact ⟨he.1, add_pos_of_pos_of_nonneg he.2.1 hc, he.2.2⟩

/-- Unit-shift form used to reduce nonnegative values to strictly positive values. -/
theorem matroidGreedySet_subset_add_one
    (M : Matroid α) (V : Finset α) (w : α → ℝ) :
    matroidGreedySet M V w ⊆ matroidGreedySet M V (fun x => w x + 1) := by
  exact matroidGreedySet_subset_add_const M V w zero_le_one

end GaloisForLFunctions.HTGeometry
