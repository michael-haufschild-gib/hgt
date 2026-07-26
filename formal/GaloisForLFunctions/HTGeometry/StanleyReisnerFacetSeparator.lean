import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation
import GaloisForLFunctions.HTGeometry.SimplicialConstraintTower
import GaloisForLFunctions.HTGeometry.BoundaryWedgeTwoThick

/-!
# The Stanley–Reisner facet separator

The algebraic step at which a combinatorial facet becomes an analytic period carrier: for every facet
`A` of a finite facet antichain, the squarefree monomial `∏_{w ∈ A} x_w` has **nonzero** class in the
Stanley–Reisner ring, yet is **annihilated** by the vertex coordinate of every vertex outside `A`.

* `isFaceOf_of_mem_facets`, `not_isFaceOf_insert_of_mem_facets` — a facet is a face, and facet
  maximality: adjoining an outside vertex leaves the complex (this is where the antichain hypothesis
  enters).
* `srProd_facet_ne_zero` — nonzero class, read off by the face detector, which is `1` on the facet
  monomial.
* `srVertexX_mul_srProd_facet_eq_zero` — annihilation, because `insert v A` is a nonface.
* `exists_facetSeparator` — the two together.

In the scalar Stanley–Reisner principalization argument the separator is built as a product over the
*other* facets of one chosen vertex per facet; with the corpus's characterization of the
Stanley–Reisner ideal by monomial supports the facet monomial itself already does the job, and the
choice disappears.

The boundary wedge is packaged as a finite facet family (`boundaryWedgeFacetFinset`) so the separator
applies to it directly: `boundaryWedge_facetSeparator`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {R α : Type*} [CommRing R] [DecidableEq α]

omit [DecidableEq α] in
/-- A facet is a face. -/
theorem isFaceOf_of_mem_facets {facets : Finset (Finset α)} {A : Finset α} (hA : A ∈ facets) :
    IsFaceOf (↑facets : Set (Finset α)) A :=
  ⟨A, Finset.mem_coe.mpr hA, Finset.Subset.refl A⟩

/-- **Facet maximality.**  In a facet antichain, adjoining a vertex outside a facet leaves the
complex. -/
theorem not_isFaceOf_insert_of_mem_facets {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {A : Finset α} (hA : A ∈ facets)
    {v : α} (hv : v ∉ A) : ¬ IsFaceOf (↑facets : Set (Finset α)) (insert v A) := by
  rintro ⟨B, hB, hsub⟩
  apply hv
  have hAB : A ⊆ B := (Finset.subset_insert v A).trans hsub
  have hAeq : A = B := hanti (Finset.mem_coe.mpr hA) hB hAB
  have hvB : v ∈ B := hsub (Finset.mem_insert_self v A)
  rwa [← hAeq] at hvB

/-- **The facet monomial has nonzero class.**  Its face detector is `1`. -/
theorem srProd_facet_ne_zero [Nontrivial R] (facets : Finset (Finset α)) {A : Finset α}
    (hA : A ∈ facets) : ∏ w ∈ A, srVertexX R facets w ≠ 0 := by
  intro h
  have hdet := srFaceDetector_prod (R := R) facets A (isFaceOf_of_mem_facets hA)
  rw [h, map_zero] at hdet
  exact zero_ne_one hdet

/-- **The facet monomial is annihilated by every outside vertex.**  Adjoining such a vertex produces
a nonface, whose monomial vanishes. -/
theorem srVertexX_mul_srProd_facet_eq_zero (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {A : Finset α} (hA : A ∈ facets)
    {v : α} (hv : v ∉ A) :
    srVertexX R facets v * ∏ w ∈ A, srVertexX R facets w = 0 := by
  rw [← Finset.prod_insert hv]
  exact srProd_eq_zero_of_not_isFace facets (not_isFaceOf_insert_of_mem_facets hanti hA hv)

/-- **The Stanley–Reisner facet separator.**  Every facet of a finite facet antichain carries a
nonzero class of the Stanley–Reisner ring that is killed by exactly the vertex coordinates the facet
omits.  This is the algebraic input of the isolated-facet-carrier step: transported through a
realization, the class becomes a nonconstant function and the annihilations become its periods. -/
theorem exists_facetSeparator [Nontrivial R] (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {A : Finset α} (hA : A ∈ facets) :
    ∃ q : stanleyReisnerRing R facets, q ≠ 0 ∧ ∀ v ∉ A, srVertexX R facets v * q = 0 :=
  ⟨∏ w ∈ A, srVertexX R facets w, srProd_facet_ne_zero facets hA,
    fun _ hv => srVertexX_mul_srProd_facet_eq_zero facets hanti hA hv⟩

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry

variable {r s : ℕ}

/-- The boundary-wedge facet family as a finite family, so that the Stanley–Reisner machinery
applies to it. -/
def boundaryWedgeFacetFinset (r s : ℕ) : Finset (Finset (BoundaryWedgeVertex r s)) :=
  (leftBlock r s).image (fun u => (leftBlock r s).erase u) ∪
    (rightBlock r s).image (fun v => (rightBlock r s).erase v)

@[simp]
theorem mem_boundaryWedgeFacetFinset {F : Finset (BoundaryWedgeVertex r s)} :
    F ∈ boundaryWedgeFacetFinset r s ↔ F ∈ boundaryWedgeFacets r s := by
  simp only [boundaryWedgeFacetFinset, Finset.mem_union, Finset.mem_image, boundaryWedgeFacets,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr ⟨u, hu, rfl⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr ⟨u, hu, rfl⟩

theorem coe_boundaryWedgeFacetFinset :
    (↑(boundaryWedgeFacetFinset r s) : Set (Finset (BoundaryWedgeVertex r s)))
      = boundaryWedgeFacets r s :=
  Set.ext fun _ => mem_boundaryWedgeFacetFinset

/-- **The boundary wedge carries a facet separator at every facet.**  Applied to the facet
`leftBlock ∖ {centre}`, the omitted vertices are the whole right block together with the centre —
at least three of them. -/
theorem boundaryWedge_facetSeparator {R : Type*} [CommRing R] [Nontrivial R]
    (hr : 2 ≤ r) (hs : 2 ≤ s) {A : Finset (BoundaryWedgeVertex r s)}
    (hA : A ∈ boundaryWedgeFacetFinset r s) :
    ∃ q : stanleyReisnerRing R (boundaryWedgeFacetFinset r s), q ≠ 0 ∧
      ∀ v ∉ A, srVertexX R (boundaryWedgeFacetFinset r s) v * q = 0 := by
  refine exists_facetSeparator (boundaryWedgeFacetFinset r s) ?_ hA
  rw [coe_boundaryWedgeFacetFinset]
  exact facetAntichain hr hs

end GaloisForLFunctions.UniformBoundaryWedge
