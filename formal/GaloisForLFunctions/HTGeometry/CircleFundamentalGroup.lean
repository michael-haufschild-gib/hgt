/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples

/-!
# Integer classification of circle loops

The quotient cover of the real line by integer translations, composed with
the standard circle homeomorphism, identifies the circle fundamental group
with the integers. This uses the covering directly, so no intermediate
homotopy-equivalence transport layer is required.

The covering argument is adapted from DifferentialGeometry's
`Topology/FundamentalGroup/Circle.lean` (Apache-2.0).
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def integerPeriodEquiv : ℤ ≃+ AddSubgroup.zmultiples (1 : ℝ) :=
  AddEquiv.ofBijective
    ((Int.castAddHom ℝ).codRestrict (AddSubgroup.zmultiples (1 : ℝ))
      (fun n ↦ AddSubgroup.intCast_mem_zmultiples_one (R := ℝ) n)) <| by
    constructor
    · intro m n h
      exact Int.cast_injective (congrArg Subtype.val h : (m : ℝ) = (n : ℝ))
    · rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      exact ⟨n, Subtype.ext (by simpa using hn)⟩

/-- Circle loop classes are classified exactly by integer winding. -/
def circleFundamentalGroupEquivInt :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ := by
  let e := AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num)
  have hcover := (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).homeomorph_comp e
  have hzero : (e ∘ ((↑) : ℝ → AddCircle (1 : ℝ))) 0 = 1 := by
    change AddCircle.homeomorphCircle _ 0 = 1
    rw [AddCircle.homeomorphCircle_apply]
    exact AddCircle.toCircle_zero
  exact (hcover.fundamentalGroupEquiv ⟨0, hzero⟩).trans
    (MulOpposite.opMulEquiv.symm.trans integerPeriodEquiv.toMultiplicative.symm)

/-- Winding is a complete invariant of circle-loop homotopy. -/
theorem circle_loops_homotopic_iff_winding_eq (p q : Path (1 : Circle) 1) :
    p.Homotopic q ↔
      circleFundamentalGroupEquivInt (Path.Homotopic.Quotient.mk p) =
        circleFundamentalGroupEquivInt (Path.Homotopic.Quotient.mk q) := by
  rw [circleFundamentalGroupEquivInt.injective.eq_iff]
  exact Path.Homotopic.Quotient.eq.symm

end

end GaloisForLFunctions.HTGeometry
