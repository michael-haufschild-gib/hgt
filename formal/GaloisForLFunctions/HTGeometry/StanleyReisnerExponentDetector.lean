import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetSeparator

/-!
# Reading a general monomial in the Stanley--Reisner ring

The corpus face detector reads the coefficient of a **squarefree** monomial `∏_{v ∈ J} x_v`.  The
same construction works for an arbitrary exponent whose support is a face, because the criterion it
rests on -- that a member of the Stanley--Reisner ideal has vanishing coefficient at every exponent
with face support -- never used squarefreeness.

The gain is the converse half of the facet separator.  A facet monomial multiplied by a vertex
coordinate **inside** the facet stays nonzero, since the resulting exponent still has the facet as
support; multiplied by a vertex outside the facet it vanishes.  So the separator's annihilator is
exactly the complement of the facet, not merely contained in it.
-/

open Finset MvPolynomial

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]

/-- **General exponent detector.**  The coefficient reader at any exponent with face support
descends to the Stanley--Reisner ring. -/
noncomputable def srExponentDetector (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (e : α →₀ ℕ) (he : IsFaceOf (↑facets : Set (Finset α)) e.support) :
    stanleyReisnerRing R facets →ₗ[R] R :=
  Submodule.liftQ ((stanleyReisnerIdeal R facets).restrictScalars R)
    (MvPolynomial.lcoeff R e)
    (by
      intro P hP
      rw [Submodule.restrictScalars_mem] at hP
      rw [LinearMap.mem_ker, MvPolynomial.lcoeff_apply]
      exact coeff_eq_zero_of_isFace_support facets he hP)

@[simp]
theorem srExponentDetector_mk (facets : Finset (Finset α)) (e : α →₀ ℕ)
    (he : IsFaceOf (↑facets : Set (Finset α)) e.support) (P : MvPolynomial α R) :
    srExponentDetector R facets e he (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P)
      = MvPolynomial.coeff e P := rfl

/-- **A monomial with face support is nonzero in the Stanley--Reisner ring.** -/
theorem srMonomial_ne_zero [Nontrivial R] (facets : Finset (Finset α)) (e : α →₀ ℕ)
    (he : IsFaceOf (↑facets : Set (Finset α)) e.support) :
    Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (MvPolynomial.monomial e (1 : R)) ≠ 0 := by
  intro h
  have hdet := srExponentDetector_mk (R := R) facets e he (MvPolynomial.monomial e (1 : R))
  rw [h, map_zero] at hdet
  rw [MvPolynomial.coeff_monomial, if_pos rfl] at hdet
  exact zero_ne_one hdet

/-- **The facet monomial survives multiplication by a vertex it contains.** -/
theorem srVertexX_mul_srProd_facet_ne_zero [Nontrivial R] (facets : Finset (Finset α))
    {A : Finset α} (hA : A ∈ facets) {v : α} (hv : v ∈ A) :
    srVertexX R facets v * ∏ w ∈ A, srVertexX R facets w ≠ 0 := by
  set e : α →₀ ℕ := Finsupp.single v 1 + indicatorExponent A with he
  have hsuppA : ∀ x : α, (indicatorExponent A) x ≠ 0 ↔ x ∈ A := by
    intro x
    rw [← Finsupp.mem_support_iff, support_indicatorExponent]
  have hsupp : e.support = A := by
    ext x
    rw [he, Finsupp.mem_support_iff, Finsupp.add_apply]
    constructor
    · intro hx
      by_cases hxv : x = v
      · exact hxv ▸ hv
      · have h1 : (Finsupp.single v 1 : α →₀ ℕ) x = 0 := by
          rw [Finsupp.single_apply, if_neg (fun h => hxv h.symm)]
        rw [h1, zero_add] at hx
        exact (hsuppA x).mp hx
    · intro hx
      have h2 : (indicatorExponent A) x ≠ 0 := (hsuppA x).mpr hx
      omega
  have hface : IsFaceOf (↑facets : Set (Finset α)) e.support := by
    rw [hsupp]
    exact isFaceOf_of_mem_facets hA
  have hprod : (∏ w ∈ A, srVertexX R facets w)
      = Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (∏ w ∈ A, X w) := by
    rw [map_prod]
    rfl
  have hX : (MvPolynomial.X v : MvPolynomial α R) * (∏ w ∈ A, X w)
      = MvPolynomial.monomial e (1 : R) := by
    rw [GaloisForLFunctions.VeroneseIdeal.prod_X_eq_monomial, he, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]
    rfl
  have hmon : srVertexX R facets v * ∏ w ∈ A, srVertexX R facets w
      = Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (MvPolynomial.monomial e (1 : R)) := by
    rw [srVertexX, hprod, ← map_mul, hX]
  rw [hmon]
  exact srMonomial_ne_zero facets e hface

/-- **The exact annihilator of the facet separator.**  A vertex coordinate kills the facet monomial
precisely when the vertex lies outside the facet. -/
theorem srVertexX_mul_srProd_facet_eq_zero_iff [Nontrivial R] (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {A : Finset α} (hA : A ∈ facets) (v : α) :
    srVertexX R facets v * ∏ w ∈ A, srVertexX R facets w = 0 ↔ v ∉ A := by
  constructor
  · intro h hv
    exact srVertexX_mul_srProd_facet_ne_zero facets hA hv h
  · intro hv
    exact srVertexX_mul_srProd_facet_eq_zero facets hanti hA hv

end GaloisForLFunctions.HTGeometry
