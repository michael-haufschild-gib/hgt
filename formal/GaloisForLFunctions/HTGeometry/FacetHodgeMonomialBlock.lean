import GaloisForLFunctions.HTGeometry.SimplexFacetHodgeBlock
import GaloisForLFunctions.HTGeometry.MultipleSineSkeletonIdeal

/-!
# The monomial blocks of a facet family, and the multiple-sine skeleton

The augmented coordinate-facet descent complex splits as an orthogonal direct sum over surviving
monomials, and the block of a monomial is the full simplex on the facets containing its support.
This file records that block, proves it is nonempty exactly for surviving monomials, and assembles
the block Hodge identity with its uniform gap.

It then instantiates the assembly at the multiple-sine / multiple-gamma skeleton facet family,
whose Stanley--Reisner ideal is the squarefree Veronese ideal of the reflection layer: every face
of that complex has a nonempty block, so the block Hodge operator is a positive scalar there.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {α : Type*} [DecidableEq α]

/-- The monomial block of a facet family at a support: the facets containing it. -/
def monomialBlock (facets : Finset (Finset α)) (J : Finset α) : Finset (Finset α) :=
  facets.filter (fun A => J ⊆ A)

theorem mem_monomialBlock {facets : Finset (Finset α)} {J A : Finset α} :
    A ∈ monomialBlock facets J ↔ A ∈ facets ∧ J ⊆ A := by
  simp [monomialBlock]

/-- **The block of a surviving monomial is nonempty.**  A support is a face exactly when some
facet contains it. -/
theorem monomialBlock_nonempty_iff (facets : Finset (Finset α)) (J : Finset α) :
    (monomialBlock facets J).Nonempty ↔ IsFaceOf (↑facets : Set (Finset α)) J := by
  constructor
  · rintro ⟨A, hA⟩
    rw [mem_monomialBlock] at hA
    exact ⟨A, hA.1, hA.2⟩
  · rintro ⟨A, hA, hJA⟩
    exact ⟨A, mem_monomialBlock.mpr ⟨hA, hJA⟩⟩

theorem one_le_card_monomialBlock {facets : Finset (Finset α)} {J : Finset α}
    (h : IsFaceOf (↑facets : Set (Finset α)) J) : 1 ≤ (monomialBlock facets J).card :=
  Finset.card_pos.mpr ((monomialBlock_nonempty_iff facets J).mpr h)

/-- **The block Hodge identity with its uniform gap.**  On the block of a surviving monomial the
Hodge operator is multiplication by the number of facets containing the support, a positive
integer. -/
theorem monomialBlock_hodge {facets : Finset (Finset α)} {J : Finset α}
    (_h : IsFaceOf (↑facets : Set (Finset α)) J)
    (x : ExteriorAlgebra ℝ (↥(monomialBlock facets J) → ℝ)) :
    CliffordAlgebra.contractLeft (facetDual ↥(monomialBlock facets J))
          (facetCoboundary ↥(monomialBlock facets J) x)
        + facetCoboundary ↥(monomialBlock facets J)
          (CliffordAlgebra.contractLeft
            (facetDual ↥(monomialBlock facets J)) x)
      = (Fintype.card ↥(monomialBlock facets J) : ℝ) • x :=
  facetHodge_apply _ x

theorem one_le_monomialBlock_card_real {facets : Finset (Finset α)} {J : Finset α}
    (h : IsFaceOf (↑facets : Set (Finset α)) J) :
    (1 : ℝ) ≤ (Fintype.card ↥(monomialBlock facets J) : ℝ) := by
  have hcard : Fintype.card ↥(monomialBlock facets J)
      = (monomialBlock facets J).card := Fintype.card_coe _
  rw [hcard]
  exact_mod_cast one_le_card_monomialBlock h

/-! ### The multiple-sine skeleton -/

variable {σ : Type*} [DecidableEq σ] [Fintype σ]

/-- **Every face of the multiple-sine skeleton has a nonempty block.**  The skeleton facet family
is the one whose Stanley--Reisner ideal is the squarefree Veronese ideal of the reflection layer. -/
theorem one_le_card_monomialBlock_skeletonFacets {k : ℕ} (hk : k ≤ Fintype.card σ)
    {J : Finset σ} (hJ : J.card ≤ k) :
    1 ≤ (monomialBlock (skeletonFacets σ k) J).card :=
  one_le_card_monomialBlock ((isFaceOf_skeletonFacets_iff hk J).mpr hJ)

/-- **The block Hodge gap on the multiple-sine skeleton.** -/
theorem monomialBlock_hodge_skeletonFacets {k : ℕ} (hk : k ≤ Fintype.card σ)
    {J : Finset σ} (hJ : J.card ≤ k)
    (x : ExteriorAlgebra ℝ (↥(monomialBlock (skeletonFacets σ k) J) → ℝ)) :
    CliffordAlgebra.contractLeft
          (facetDual ↥(monomialBlock (skeletonFacets σ k) J))
          (facetCoboundary ↥(monomialBlock (skeletonFacets σ k) J) x)
        + facetCoboundary ↥(monomialBlock (skeletonFacets σ k) J)
          (CliffordAlgebra.contractLeft
            (facetDual ↥(monomialBlock (skeletonFacets σ k) J)) x)
      = (Fintype.card ↥(monomialBlock (skeletonFacets σ k) J) : ℝ) • x :=
  monomialBlock_hodge ((isFaceOf_skeletonFacets_iff hk J).mpr hJ) x

end GaloisForLFunctions.HTGeometry
