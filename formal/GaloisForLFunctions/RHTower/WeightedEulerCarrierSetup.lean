import GaloisForLFunctions.HTGeometry.CompactOpenDualCarrier
import GaloisForLFunctions.HTGeometry.CarrierComplexFunctional
import GaloisForLFunctions.HTGeometry.QuadrantRestrictionSchwarz

/-!
# The rectangular carrier and complex functional attached to a quadrant functional

A continuous real functional on the holomorphic functions of the critical quadrant is dominated by
the supremum norm on one compact subset; that compact set sits inside a closed rectangle still
contained in the quadrant, and the domination passes to the restriction map to that rectangle.
Hahn–Banach and complexification then produce a complex functional on the rectangle whose real part
reproduces the given functional on every restriction.

* `RHTower.QuadrantCarrierData`, `RHTower.exists_quadrantCarrierData`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- A rectangular carrier inside the critical quadrant together with a complex functional realizing
a given real functional on restrictions. -/
structure QuadrantCarrierData (f₂ : holoQuadrant →L[ℝ] ℝ) where
  /-- Left edge. -/ a : ℝ
  /-- Right edge. -/ b : ℝ
  /-- Bottom edge. -/ c : ℝ
  /-- Top edge. -/ d : ℝ
  /-- The rectangle starts inside the critical strip. -/ ha : 1 / 2 < a
  /-- The rectangle is nondegenerate horizontally. -/ hab : a ≤ b
  /-- The rectangle ends inside the critical strip. -/ hb : b < 1
  /-- The rectangle stays in the upper half plane. -/ hc : 0 < c
  /-- The rectangle is nondegenerate vertically. -/ hcd : c ≤ d
  /-- The rectangle lies in the quadrant. -/ hquad : rect a b c d ⊆ criticalQuadrant
  /-- The complexified functional. -/ L : C(rect a b c d, ℂ) →L[ℂ] ℂ
  /-- Its real part reproduces the given functional. -/
  hL : ∀ g : holoQuadrant, (L (quadrantRestrict hquad g)).re = f₂ g

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Every continuous functional on the quadrant's holomorphic space arises as the real part of a
complex functional on a rectangular carrier inside the quadrant.** -/
theorem exists_quadrantCarrierData (f₂ : holoQuadrant →L[ℝ] ℝ) :
    Nonempty (QuadrantCarrierData f₂) := by
  classical
  obtain ⟨K₀, C₀, hK₀, hC₀, hbnd⟩ := exists_compact_dual_bound holoQuadrant f₂
  have hK₀im : IsCompact ((Subtype.val : ↥criticalQuadrant → ℂ) '' K₀) :=
    hK₀.image continuous_subtype_val
  have hK₀sub : ((Subtype.val : ↥criticalQuadrant → ℂ) '' K₀) ⊆ criticalQuadrant := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨a, b, c, d, ha, hab, hb, hc, hcd, hK₀rect, hrectQ⟩ :=
    exists_rect_of_isCompact_subset_criticalQuadrant hK₀im hK₀sub
  haveI : CompactSpace (rect a b c d) :=
    isCompact_iff_compactSpace.mp (isCompact_rect a b c d)
  have hbd : ∀ g : holoQuadrant,
      |f₂.toLinearMap g| ≤ C₀ * ‖quadrantRestrict hrectQ g‖ := by
    intro g
    refine hbnd g ‖quadrantRestrict hrectQ g‖ (norm_nonneg _) ?_
    intro x hx
    have hmem : ((x : ℂ)) ∈ rect a b c d := hK₀rect ⟨x, hx, rfl⟩
    have hxeq : (⟨(x : ℂ), hrectQ hmem⟩ : (criticalQuadrant : Set ℂ)) = x := Subtype.ext rfl
    have hval : (g : C((criticalQuadrant : Set ℂ), ℂ)) x
        = quadrantRestrict hrectQ g ⟨(x : ℂ), hmem⟩ := by
      rw [quadrantRestrict_apply, hxeq]
    rw [hval]
    exact (quadrantRestrict hrectQ g).norm_coe_le_norm _
  obtain ⟨L, hL⟩ := exists_complex_functional_of_bound (M := ↥holoQuadrant)
    (K := ↥(rect a b c d)) (quadrantRestrict hrectQ) f₂.toLinearMap C₀ hbd
  exact ⟨{ a := a, b := b, c := c, d := d, ha := ha, hab := hab, hb := hb, hc := hc, hcd := hcd
           hquad := hrectQ, L := L, hL := hL }⟩

end RHTower
