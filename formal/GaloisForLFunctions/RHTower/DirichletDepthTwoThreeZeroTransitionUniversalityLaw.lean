import GaloisForLFunctions.RHTower.CarrierDepthTwoRigidity
import GaloisForLFunctions.RHTower.DepthThreeDirichletHighZeros

/-!
# Dirichlet depth-two/three zero-transition universality

The two terminal mechanisms meet in the same finite Dirichlet family.  The depth-two factor is
zero-free throughout the open right half-plane, and its completed high strip zeros are forced onto
the critical line and are simple.  Adding the single prime `3` changes the direct factor sharply:
depth three has zeros cofinally high inside the open critical strip.
-/

namespace RHTower

noncomputable section

/-- The explicit depth-three factor is the standard depth-three Dirichlet polynomial. -/
theorem dirichletPoly_three (s : ℂ) :
    dirichletPoly 3 s = 1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s) := by
  norm_num [dirichletPoly, Finset.sum_Icc_succ_top]

/-- **Dirichlet depth-two/three zero-transition universality law.**

* depth two has no zero at any positive real part;
* above one absolute height, every completed depth-two strip zero is critical-line aligned and
  simple;
* depth three has direct-factor zeros at arbitrarily large positive heights in the open strip.

Thus the prime `3` is the first finite-aperture source capable of recurrent interior cancellation;
the two-prime phase is rigid, while the three-prime phase is cofinally non-rigid. -/
theorem dirichletDepth_two_three_zeroTransition_universality :
    (∀ s : ℂ, 0 < s.re → dirichletPoly 2 s ≠ 0) ∧
      (∃ A > 0, ∀ s : ℂ, 0 < s.re → s.re < 1 → A ≤ |s.im| →
        completedGN 2 s = 0 →
          s.re = 1 / 2 ∧ deriv (completedGN 2) s ≠ 0) ∧
      (∀ B : ℝ, ∃ s : ℂ,
        0 < s.re ∧ s.re < 1 ∧ B ≤ s.im ∧ dirichletPoly 3 s = 0) := by
  refine ⟨fun s hs => dirichletPoly_two_ne_zero hs,
    exists_height_completedGN_two_zero_simple_of_abs_im_ge, fun B => ?_⟩
  obtain ⟨s, hs0, hs1, hsB, hzero⟩ := exists_depthThreeDirichletFactor_zero_high B
  refine ⟨s, hs0, hs1, hsB, ?_⟩
  rw [dirichletPoly_three]
  exact hzero

end


end RHTower
