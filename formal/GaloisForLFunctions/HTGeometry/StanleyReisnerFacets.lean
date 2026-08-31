import GaloisForLFunctions.HTGeometry.StanleyReisnerLink

/-!
# Facets and cone points

The Stanley–Reisner ideal is an intersection over all faces, but only the maximal ones matter: a
smaller face gives a larger coordinate ideal.  Every face sits inside a facet, so the intersection
over the facets is the same ideal.

```text
faceFacets F                     the maximal faces
exists_facet_superset            every face is contained in a facet
faceFamilyIdeal_eq_facets        ** the ideal only sees the facets **
IsConePoint F v                  a vertex that can be added to every face
mem_of_isConePoint               a cone point lies in every facet
isRegularOn_X_of_isConePoint
    ** the variable at a cone point is a nonzerodivisor on the Stanley–Reisner ring **
```

Restricting to the facets is what makes the nonzerodivisor criterion usable: over all faces the
empty face is present and every variable lies in its coordinate prime, so nothing would ever be
regular.  The cone-point case is the base case of the Cohen–Macaulay induction — `K[Δ]` is then a
polynomial extension of `K[del(v)]`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

open scoped Classical in
/-- The facets: the maximal faces of a family. -/
noncomputable def faceFacets (F : Finset (Finset σ)) : Finset (Finset σ) :=
  F.filter (fun S => ∀ T ∈ F, S ⊆ T → S = T)

open scoped Classical in
theorem mem_faceFacets {F : Finset (Finset σ)} {S : Finset σ} :
    S ∈ faceFacets F ↔ S ∈ F ∧ ∀ T ∈ F, S ⊆ T → S = T := by
  simp [faceFacets]

/-- Every face is contained in a facet. -/
theorem exists_facet_superset {F : Finset (Finset σ)} {S : Finset σ} (hS : S ∈ F) :
    ∃ T ∈ faceFacets F, S ⊆ T := by
  classical
  obtain ⟨T, hmax⟩ := Finset.exists_maximal
    (s := F.filter (fun T => S ⊆ T)) ⟨S, by simp [hS]⟩
  have hT : T ∈ F.filter (fun T => S ⊆ T) := hmax.1
  rw [Finset.mem_filter] at hT
  refine ⟨T, mem_faceFacets.mpr ⟨hT.1, ?_⟩, hT.2⟩
  intro U hU hTU
  have hUmem : U ∈ F.filter (fun T => S ⊆ T) := by
    rw [Finset.mem_filter]
    exact ⟨hU, hT.2.trans hTU⟩
  exact Finset.Subset.antisymm hTU (hmax.2 hUmem hTU)

/-- **The Stanley–Reisner ideal only sees the facets.** -/
theorem faceFamilyIdeal_eq_facets (K : Type u) [Field K] {F : Finset (Finset σ)} :
    faceFamilyIdeal K F = faceFamilyIdeal K (faceFacets F) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [faceFamilyIdeal, faceFamilyIdeal]
    exact Finset.inf_mono (Finset.filter_subset _ _)
  · rw [faceFamilyIdeal, faceFamilyIdeal, Finset.le_inf_iff]
    intro S hS
    obtain ⟨T, hT, hsub⟩ := exists_facet_superset hS
    refine le_trans (Finset.inf_le hT) ?_
    refine Ideal.span_mono (Set.image_mono ?_)
    intro x hx
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hx ⊢
    exact fun hxS => hx (hsub hxS)

/-- A cone point of a face family: a vertex that can be added to every face. -/
def IsConePoint (F : Finset (Finset σ)) (v : σ) : Prop :=
  ∀ S ∈ F, insert v S ∈ F

theorem mem_of_isConePoint {F : Finset (Finset σ)} {v : σ} (hv : IsConePoint F v)
    {T : Finset σ} (hT : T ∈ faceFacets F) : v ∈ T := by
  classical
  rw [mem_faceFacets] at hT
  have hins : insert v T ∈ F := hv T hT.1
  have heq : T = insert v T := hT.2 (insert v T) hins (Finset.subset_insert v T)
  rw [heq]
  exact Finset.mem_insert_self v T

/-- **The variable at a cone point is a nonzerodivisor on the Stanley–Reisner ring.** -/
theorem isRegularOn_X_of_isConePoint (K : Type u) [Field K] {F : Finset (Finset σ)} {v : σ}
    (hv : IsConePoint F v) :
    IsRegularOn (faceFamilyIdeal K F) (X v) := by
  classical
  rw [faceFamilyIdeal_eq_facets K]
  refine isRegularOn_faceFamilyIdeal K ?_
  intro T hT hmem
  rw [mem_span_X_compl_iff'] at hmem
  refine hmem (Finsupp.single v 1) ?_ ?_
  · have hX : (X v : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single v 1) 1 := rfl
    rw [hX, MvPolynomial.support_monomial, if_neg (one_ne_zero)]
    simp
  · intro w hw
    have : w = v := by
      simpa using Finsupp.support_single_subset hw
    rw [this]
    exact mem_of_isConePoint hv hT


end GaloisForLFunctions.HTGeometry
