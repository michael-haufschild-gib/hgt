import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpIntegerPrincipal
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLattice

/-!
# Coordinate splitting for completed pseudodifferential valuation lattices

A finitely generated submodule of a finite power of the completed skew field has a finitely
generated coordinate image.  The fractional-ideal theorem for the completed valuation ring makes
that image principal.  Lifting its generator gives an exact coordinate splitting: every vector is
an integral left multiple of the lift plus a vector whose selected coordinate vanishes.

This is the induction step for constructing bases and Cartan normal forms of arbitrary completed
pseudodifferential lattices.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {ι : Type*}

/-- Coordinate projection from the completed skew vector space, linear over its valuation ring. -/
def completedPseudoDiffOpProjCoord (i₀ : ι) :
    (ι → CompletedPseudoDiffOp K) →ₗ[CompletedPseudoDiffOpInteger (K := K)]
      CompletedPseudoDiffOp K where
  toFun y := y i₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem completedPseudoDiffOpProjCoord_apply
    (i₀ : ι) (y : ι → CompletedPseudoDiffOp K) :
    completedPseudoDiffOpProjCoord (K := K) i₀ y = y i₀ := rfl

/-- A lift of a principal coordinate image splits every vector along that coordinate. -/
theorem exists_completedPseudoDiffOp_coord_generator
    (i₀ : ι)
    (N : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (ι → CompletedPseudoDiffOp K)) (hN : N.FG) :
    ∃ x ∈ N, ∀ y ∈ N, ∃ r : CompletedPseudoDiffOpInteger (K := K),
      (y - r • x) i₀ = 0 ∧ y - r • x ∈ N := by
  classical
  let P := completedPseudoDiffOpProjCoord (K := K) i₀
  have hmap : (N.map P).FG := hN.map P
  obtain ⟨b, hb⟩ := fg_completedPseudoDiffOp_submodule_eq_span_singleton (N.map P) hmap
  have hbmem : b ∈ N.map P := by
    rw [hb]
    exact Submodule.mem_span_singleton_self b
  obtain ⟨x, hxN, hxb⟩ := hbmem
  refine ⟨x, hxN, fun y hy => ?_⟩
  have hyimg : y i₀ ∈ N.map P := ⟨y, hy, rfl⟩
  rw [hb] at hyimg
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyimg
  refine ⟨r, ?_, N.sub_mem hy (N.smul_mem r hxN)⟩
  show y i₀ - (r • x) i₀ = 0
  have hrx : (r • x) i₀ = r • x i₀ := rfl
  have hxb' : x i₀ = b := hxb
  rw [hrx, hxb', hr, sub_self]

/-- A nonzero coordinate of the splitting generator separates its scalar coefficient. -/
theorem completedPseudoDiffOp_smul_eq_zero_of_coord_eq_zero
    {x : ι → CompletedPseudoDiffOp K} {i₀ : ι} (hx : x i₀ ≠ 0)
    {r : CompletedPseudoDiffOpInteger (K := K)} (h : (r • x) i₀ = 0) : r = 0 := by
  have hr : (r : CompletedPseudoDiffOp K) * x i₀ = 0 := h
  have hrc : (r : CompletedPseudoDiffOp K) = 0 := (mul_eq_zero.mp hr).resolve_right hx
  exact Subtype.ext hrc

/-- Ambient left-linear operation that removes the component parallel to `x` at coordinate
`i₀`.  Right multiplication by `(x i₀)⁻¹ * x j` is left-linear even in the skew field. -/
def completedPseudoDiffOpCoordRemainder (i₀ : ι)
    (x : ι → CompletedPseudoDiffOp K) :
    (ι → CompletedPseudoDiffOp K) →ₗ[CompletedPseudoDiffOpInteger (K := K)]
      (ι → CompletedPseudoDiffOp K) where
  toFun y j := y j - (y i₀ * (x i₀)⁻¹) * x j
  map_add' y z := by
    funext j
    simp only [Pi.add_apply, add_mul, sub_eq_add_neg]
    noncomm_ring
  map_smul' c y := by
    funext j
    change (c : CompletedPseudoDiffOp K) * y j -
        (((c : CompletedPseudoDiffOp K) * y i₀) * (x i₀)⁻¹) * x j =
      (c : CompletedPseudoDiffOp K) *
        (y j - (y i₀ * (x i₀)⁻¹) * x j)
    noncomm_ring

@[simp] theorem completedPseudoDiffOpCoordRemainder_apply
    (i₀ : ι) (x y : ι → CompletedPseudoDiffOp K) (j : ι) :
    completedPseudoDiffOpCoordRemainder (K := K) i₀ x y j =
      y j - (y i₀ * (x i₀)⁻¹) * x j := rfl

theorem completedPseudoDiffOpCoordRemainder_coord
    (i₀ : ι) (x y : ι → CompletedPseudoDiffOp K) (hx : x i₀ ≠ 0) :
    completedPseudoDiffOpCoordRemainder (K := K) i₀ x y i₀ = 0 := by
  rw [completedPseudoDiffOpCoordRemainder_apply, mul_assoc,
    inv_mul_cancel₀ hx, mul_one, sub_self]

theorem completedPseudoDiffOpCoordRemainder_eq_self_of_coord_eq_zero
    (i₀ : ι) (x y : ι → CompletedPseudoDiffOp K) (hy : y i₀ = 0) :
    completedPseudoDiffOpCoordRemainder (K := K) i₀ x y = y := by
  funext j
  rw [completedPseudoDiffOpCoordRemainder_apply, hy, zero_mul, zero_mul, sub_zero]

/-- The kernel remainder after splitting one coordinate is still finitely generated. -/
theorem fg_inf_ker_completedPseudoDiffOpProjCoord
    (i₀ : ι)
    (N : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (ι → CompletedPseudoDiffOp K)) (hN : N.FG) :
    (N ⊓ LinearMap.ker (completedPseudoDiffOpProjCoord (K := K) i₀)).FG := by
  classical
  obtain ⟨x, hxN, hsplit⟩ := exists_completedPseudoDiffOp_coord_generator i₀ N hN
  by_cases hx0 : x i₀ = 0
  · have hle : N ≤ LinearMap.ker (completedPseudoDiffOpProjCoord (K := K) i₀) := by
      intro y hy
      obtain ⟨r, hcoord, -⟩ := hsplit y hy
      change y i₀ = 0
      have hrx : (r • x) i₀ = 0 := by
        change (r : CompletedPseudoDiffOp K) * x i₀ = 0
        rw [hx0, mul_zero]
      change y i₀ - (r • x) i₀ = 0 at hcoord
      rw [hrx, sub_zero] at hcoord
      exact hcoord
    rw [inf_eq_left.mpr hle]
    exact hN
  · let T := completedPseudoDiffOpCoordRemainder (K := K) i₀ x
    have hmap : N.map T =
        N ⊓ LinearMap.ker (completedPseudoDiffOpProjCoord (K := K) i₀) := by
      apply le_antisymm
      · rintro z ⟨y, hy, rfl⟩
        obtain ⟨r, hcoord, hmem⟩ := hsplit y hy
        have hyi : y i₀ = (r : CompletedPseudoDiffOp K) * x i₀ := by
          change y i₀ - (r : CompletedPseudoDiffOp K) * x i₀ = 0 at hcoord
          exact sub_eq_zero.mp hcoord
        have hcoef : y i₀ * (x i₀)⁻¹ = (r : CompletedPseudoDiffOp K) := by
          rw [hyi, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
        have hTy : T y = y - r • x := by
          funext j
          change y j - (y i₀ * (x i₀)⁻¹) * x j =
            y j - (r : CompletedPseudoDiffOp K) * x j
          rw [hcoef]
        refine ⟨?_, ?_⟩
        · rw [hTy]
          exact hmem
        · change T y i₀ = 0
          exact completedPseudoDiffOpCoordRemainder_coord i₀ x y hx0
      · intro z hz
        have hzi : z i₀ = 0 := hz.2
        refine ⟨z, hz.1, ?_⟩
        exact completedPseudoDiffOpCoordRemainder_eq_self_of_coord_eq_zero i₀ x z hzi
    rw [← hmap]
    exact hN.map T

end

end DiffOp

end GaloisForLFunctions.HTGeometry
