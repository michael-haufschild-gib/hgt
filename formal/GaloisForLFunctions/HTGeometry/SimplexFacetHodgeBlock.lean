import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# The monomial block of a coordinate-facet descent complex

Every monomial block of an augmented coordinate-facet descent complex is the augmented cochain
complex of the full simplex on the facets containing the monomial's support.  In the exterior
model the coboundary is exterior multiplication by the all-facet vector `u = ∑ e_A`, and its
Hermitian adjoint is contraction by the dual of `u`.  The creation--annihilation identity then gives

`d d* + d* d = ⟪u,u⟫ · id = n · id`,

with `n` the number of facets in the block.  Since every surviving support lies in some facet,
`n ≥ 1`, so the block Hodge operator is bounded below by one: a uniform spectral gap, hence
exactness with a norm-one Hermitian contracting homotopy.

Contracting by the dual of a *single* facet coordinate instead gives the cone homotopy: its matrix
coefficients are `0`, `1`, `-1`, so it preserves the integral monomial lattice.  The two homotopies
are different objects on the same complex.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable (F : Type*) [Fintype F] [DecidableEq F]

/-- The all-facet vector of a monomial block. -/
def facetVector : F → ℝ := fun _ => 1

/-- The facet coboundary of a monomial block: exterior multiplication by the all-facet vector. -/
def facetCoboundary : ExteriorAlgebra ℝ (F → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (F → ℝ) :=
  LinearMap.mulLeft ℝ (ExteriorAlgebra.ι ℝ (facetVector F))

/-- The dual functional summing all facet coordinates: the metric dual of the all-facet vector. -/
def facetDual : Module.Dual ℝ (F → ℝ) := ∑ i : F, LinearMap.proj i

/-- The dual functional reading a single facet coordinate. -/
def coordDual (a : F) : Module.Dual ℝ (F → ℝ) := LinearMap.proj a

omit [DecidableEq F] in
@[simp] theorem facetDual_facetVector : facetDual F (facetVector F) = (Fintype.card F : ℝ) := by
  simp [facetDual, facetVector, Finset.card_univ]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem coordDual_facetVector (a : F) : coordDual F a (facetVector F) = 1 := by
  simp [coordDual, facetVector]

/-! ### The creation--annihilation identity -/

omit [Fintype F] [DecidableEq F] in
/-- **The creation--annihilation identity on a monomial block.**  For every dual functional `d`,
contraction by `d` and exterior multiplication by the all-facet vector anticommute up to the scalar
`d(u)`. -/
theorem contract_facetCoboundary_add (d : Module.Dual ℝ (F → ℝ))
    (x : ExteriorAlgebra ℝ (F → ℝ)) :
    CliffordAlgebra.contractLeft d (facetCoboundary F x)
        + facetCoboundary F (CliffordAlgebra.contractLeft d x)
      = d (facetVector F) • x := by
  rw [facetCoboundary, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
    CliffordAlgebra.contractLeft_ι_mul]
  abel

omit [DecidableEq F] in
/-- **The block Hodge operator is the facet count.**  `d d* + d* d = n · id`. -/
theorem facetHodge_apply (x : ExteriorAlgebra ℝ (F → ℝ)) :
    CliffordAlgebra.contractLeft (facetDual F) (facetCoboundary F x)
        + facetCoboundary F (CliffordAlgebra.contractLeft (facetDual F) x)
      = (Fintype.card F : ℝ) • x := by
  rw [contract_facetCoboundary_add, facetDual_facetVector]

omit [Fintype F] [DecidableEq F] in
/-- **The integral cone contraction.**  Contracting by a single facet coordinate is a contracting
homotopy with coefficients in `{0, 1, -1}`. -/
theorem facetCone_apply (a : F) (x : ExteriorAlgebra ℝ (F → ℝ)) :
    CliffordAlgebra.contractLeft (coordDual F a) (facetCoboundary F x)
        + facetCoboundary F (CliffordAlgebra.contractLeft (coordDual F a) x)
      = x := by
  rw [contract_facetCoboundary_add, coordDual_facetVector, one_smul]

/-! ### Gap and exactness -/

omit [DecidableEq F] in
/-- The block facet count is at least one whenever the block is nonempty. -/
theorem one_le_facetCard [Nonempty F] : 1 ≤ (Fintype.card F : ℝ) := by
  exact_mod_cast Fintype.card_pos

omit [DecidableEq F] in
/-- **The Hermitian contracting homotopy.**  Dividing the codifferential by the facet count gives a
contraction of the block complex. -/
theorem facetHermitianHomotopy [Nonempty F] (x : ExteriorAlgebra ℝ (F → ℝ)) :
    CliffordAlgebra.contractLeft (facetDual F)
          (facetCoboundary F ((Fintype.card F : ℝ)⁻¹ • x))
        + facetCoboundary F
          ((Fintype.card F : ℝ)⁻¹ • CliffordAlgebra.contractLeft (facetDual F) x)
      = x := by
  have hne : (Fintype.card F : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  rw [map_smul, map_smul, map_smul, ← smul_add, facetHodge_apply, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

omit [Fintype F] [DecidableEq F] in
/-- **Exactness of the block complex, integrally.**  Every cocycle is the coboundary of its cone
contraction, whose coefficients are integral. -/
theorem facetCoboundary_eq_of_facetCoboundary_eq_zero (a : F) {x : ExteriorAlgebra ℝ (F → ℝ)}
    (hx : facetCoboundary F x = 0) :
    facetCoboundary F (CliffordAlgebra.contractLeft (coordDual F a) x) = x := by
  have h := facetCone_apply F a x
  rw [hx, map_zero, zero_add] at h
  exact h

omit [DecidableEq F] in
/-- **Exactness of the block complex, Hermitially.** -/
theorem facetCoboundary_eq_of_facetCoboundary_eq_zero' [Nonempty F]
    {x : ExteriorAlgebra ℝ (F → ℝ)} (hx : facetCoboundary F x = 0) :
    facetCoboundary F ((Fintype.card F : ℝ)⁻¹ • CliffordAlgebra.contractLeft (facetDual F) x)
      = x := by
  have h := facetHermitianHomotopy F x
  rw [map_smul, hx, smul_zero, map_zero, zero_add] at h
  exact h

/-! ### Every surviving monomial has a nonempty block -/

/-- Every face of a facet family is contained in a facet, so the block of a surviving monomial is
never empty. -/
theorem exists_facet_of_isFaceOf {α : Type*} [DecidableEq α] {facets : Set (Finset α)}
    {J : Finset α} (h : IsFaceOf facets J) : ∃ A ∈ facets, J ⊆ A := h

end GaloisForLFunctions.HTGeometry
