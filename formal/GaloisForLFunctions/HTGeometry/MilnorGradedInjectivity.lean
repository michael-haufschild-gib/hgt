import GaloisForLFunctions.HTGeometry.MilnorClassProduct

/-!
# The total residue is injective on a graded piece of Milnor's filtration

The sections at the distinct places of degree `d` have ranges that meet only in zero: the residue at
a place inverts its own section and kills the sections at all the others.  Hence an element of
`L_d / L_{d−1}` with vanishing residue at every place of degree `d` is zero — the injectivity half
of Milnor's exact sequence.

* `degPlace` : the monic irreducible polynomials of degree `d`.
* `placeSection`, `placeResidue` : the section and the residue at such a place.
* `eq_zero_of_placeResidue_eq_zero` : **injectivity of the total residue.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- The places of degree `d`: the monic irreducible polynomials of that degree. -/
abbrev degPlace (F : Type*) [Field F] (d : ℕ) :=
  {q : Polynomial F // Irreducible q ∧ q.natDegree = d ∧ q.Monic}

theorem degPlace_not_associated {d : ℕ} {p q : degPlace F d} (h : p ≠ q) :
    ¬ Associated p.1 q.1 := by
  intro hassoc
  exact h (Subtype.ext (Polynomial.eq_of_monic_of_associated p.2.2.2 q.2.2.2 hassoc))

/-- Milnor's section at a place of degree `d`. -/
noncomputable def placeSection {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (p : degPlace F d) :
    MilnorKDeg (polyResidueField p.2.1) n →+
      (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1)) :=
  sectionMapAt p.2.1 (by rw [p.2.2.1]; exact hd) (by rw [p.2.2.1]) n

/-- The residue at a place of degree `d`, on the graded piece. -/
noncomputable def placeResidue {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (p : degPlace F d) :
    (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1))
      →+ MilnorKDeg (polyResidueField p.2.1) n :=
  residueQuotAt p.2.1 (by rw [p.2.2.1]; omega) n

theorem sectionRange_eq_range {d n : ℕ} (hd : 1 ≤ d) (p : degPlace F d) :
    sectionRange (F := F) d n hd p = (placeSection hd n p).range := rfl

theorem placeResidue_placeSection {d n : ℕ} (hd : 1 ≤ d) (p : degPlace F d)
    (y : MilnorKDeg (polyResidueField p.2.1) n) :
    placeResidue hd n p (placeSection hd n p y) = y :=
  residueQuotAt_sectionMapAt p.2.1 _ _ _ n y

theorem placeResidue_placeSection_of_ne {d n : ℕ} (hd : 1 ≤ d) {p q : degPlace F d}
    (hne : p ≠ q) (y : MilnorKDeg (polyResidueField p.2.1) n) :
    placeResidue hd n q (placeSection hd n p y) = 0 :=
  residueQuotAt_sectionMapAt_of_ne p.2.1 q.2.1 (degPlace_not_associated hne)
    (by rw [p.2.2.1, q.2.2.1]) _ _ _ n y

/-- The finite-sum representation of an element of the sum of the ranges. -/
private def sumRep {d n : ℕ} (hd : 1 ≤ d)
    (z : MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1)) : Prop :=
  ∃ (T : Finset (degPlace F d))
    (f : degPlace F d → MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1)),
    (∀ i, f i ∈ (placeSection hd n i).range) ∧ (∀ i ∉ T, f i = 0) ∧ z = ∑ i ∈ T, f i

private theorem sumRep_of_mem_iSup {d n : ℕ} (hd : 1 ≤ d)
    {z : MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1)}
    (hz : z ∈ ⨆ p : degPlace F d, sectionRange (F := F) d n hd p) : sumRep hd z := by
  classical
  refine AddSubgroup.iSup_induction (C := fun w => sumRep hd w) _ hz ?_ ?_ ?_
  · intro i x hx
    refine ⟨{i}, fun j => if j = i then x else 0, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj
        show (if j = j then x else 0) ∈ _
        rw [if_pos rfl]
        exact hx
      · simp [hj]
    · intro j hj
      have hne : j ≠ i := by simpa using hj
      simp [hne]
    · simp
  · exact ⟨∅, fun _ => 0, fun _ => zero_mem _, fun _ _ => rfl, by simp⟩
  · rintro x y ⟨T₁, f₁, hf₁, hout₁, hx⟩ ⟨T₂, f₂, hf₂, hout₂, hy⟩
    refine ⟨T₁ ∪ T₂, f₁ + f₂, fun i => add_mem (hf₁ i) (hf₂ i), ?_, ?_⟩
    · intro i hi
      simp only [Pi.add_apply, hout₁ i (fun h => hi (Finset.mem_union_left _ h)),
        hout₂ i (fun h => hi (Finset.mem_union_right _ h)), add_zero]
    · rw [hx, hy]
      have h₁ : ∑ i ∈ T₁, f₁ i = ∑ i ∈ T₁ ∪ T₂, f₁ i :=
        Finset.sum_subset Finset.subset_union_left (fun i _ hi => hout₁ i hi)
      have h₂ : ∑ i ∈ T₂, f₂ i = ∑ i ∈ T₁ ∪ T₂, f₂ i :=
        Finset.sum_subset Finset.subset_union_right (fun i _ hi => hout₂ i hi)
      rw [h₁, h₂, ← Finset.sum_add_distrib]
      rfl

/-- **The total residue is injective on the graded piece.** -/
theorem eq_zero_of_placeResidue_eq_zero {d n : ℕ} (hd : 1 ≤ d)
    {z : MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1)}
    (hz : z ∈ ⨆ p : degPlace F d, sectionRange (F := F) d n hd p)
    (hres : ∀ p : degPlace F d, placeResidue hd n p z = 0) : z = 0 := by
  classical
  obtain ⟨T, f, hf, hout, rfl⟩ := sumRep_of_mem_iSup hd hz
  refine Finset.sum_eq_zero ?_
  intro i hi
  obtain ⟨y, hy⟩ := hf i
  have hsum : placeResidue hd n i (∑ j ∈ T, f j) = y := by
    rw [map_sum]
    rw [Finset.sum_eq_single i]
    · rw [← hy, placeResidue_placeSection]
    · intro j _ hji
      obtain ⟨w, hw⟩ := hf j
      rw [← hw, placeResidue_placeSection_of_ne hd hji]
    · intro hnot
      exact absurd hi hnot
  rw [hres i] at hsum
  rw [← hy, ← hsum, map_zero]

/-- **Exactness in the middle of Milnor's sequence.**  A class of `L_d` whose residue vanishes at
every place of degree `d` already lies in `L_{d−1}`.

Together with `milnorKDegMap_ratFuncConstHom_injective` (left exactness),
`milnorResidueAtPlace_surjective` (right exactness) and
`exists_mem_degreeFiltrationOnlyAt_milnorResidue_eq` (surjectivity of each graded piece), this is
Milnor's exact sequence

`0 → K_n^M(F) → K_n^M(F(t)) --(⊕ ∂_π)--> ⊕_π K_{n−1}^M(F[X]/π) → 0`

for every field `F` and every degree, proved unconditionally. -/
theorem mem_degreeFiltration_pred_of_residues_zero {d n : ℕ} (hd : 1 ≤ d)
    {x : MilnorKDeg (RatFunc F) (n + 1)} (hx : x ∈ degreeFiltration (F := F) d (n + 1))
    (hres : ∀ p : degPlace F d, milnorResidue (polyResidueData p.2.1) (n + 1) x = 0) :
    x ∈ degreeFiltration (F := F) (d - 1) (n + 1) := by
  classical
  have hmk : (QuotientAddGroup.mk' (degreeFiltration (F := F) (d - 1) (n + 1))) x
      ∈ ⨆ p : degPlace F d, sectionRange (F := F) d n hd p :=
    degreeFiltration_map_le_iSup hd ⟨x, hx, rfl⟩
  have hz : (QuotientAddGroup.mk' (degreeFiltration (F := F) (d - 1) (n + 1))) x = 0 := by
    refine eq_zero_of_placeResidue_eq_zero hd hmk ?_
    intro p
    show residueQuotAt p.2.1 _ n
      ((QuotientAddGroup.mk' (degreeFiltration (F := F) (d - 1) (n + 1))) x) = 0
    rw [QuotientAddGroup.mk'_apply, residueQuotAt_mk]
    exact hres p
  rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hz

end GaloisForLFunctions.HTGeometry
