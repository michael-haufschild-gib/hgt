import GaloisForLFunctions.RHTower.RadialPSWFSpeedMonotone
import Mathlib.Analysis.Convex.Deriv

/-!
# Radial PSWF exterior-phase concavity and secant universality

The exact exterior phase derivative and the independently proved monotonicity of its speed close
into a global finite-interval law.  Throughout the physical turning range the phase is concave,
and every secant lies between its endpoint speeds and above the free speed.  Away from the boundary
turning parameter the speed is strictly decreasing, so the phase and both secant bounds are strict.
-/

open Set

namespace RHTower

noncomputable section

theorem continuousOn_radialPSWFExteriorPhase_Ioi (sigma : ℝ) :
    ContinuousOn (radialPSWFExteriorPhase sigma) (Ioi 1) := by
  intro z hz
  exact (hasDerivAt_radialPSWFExteriorPhase sigma hz).continuousAt.continuousWithinAt

theorem deriv_radialPSWFExteriorPhase_eq (sigma : ℝ) {z : ℝ} (hz : 1 < z) :
    deriv (radialPSWFExteriorPhase sigma) z = radialPSWFExteriorSpeed sigma z :=
  (hasDerivAt_radialPSWFExteriorPhase sigma hz).deriv

/-- The integrated exterior phase is concave because its exact derivative is the antitone
exterior speed. -/
theorem concaveOn_radialPSWFExteriorPhase {sigma : ℝ} (hsigma : sigma ^ (2 : ℕ) ≤ 1) :
    ConcaveOn ℝ (Ioi 1) (radialPSWFExteriorPhase sigma) := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 1)
    (continuousOn_radialPSWFExteriorPhase_Ioi sigma) ?_ ?_
  · rw [interior_Ioi]
    intro z hz
    exact (hasDerivAt_radialPSWFExteriorPhase sigma hz).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx y hy hxy
    rw [deriv_radialPSWFExteriorPhase_eq sigma hx,
      deriv_radialPSWFExteriorPhase_eq sigma hy]
    exact antitoneOn_radialPSWFExteriorSpeed hsigma hx hy hxy

/-- Below the boundary turning parameter, the exterior speed is strictly decreasing. -/
theorem strictAntiOn_radialPSWFExteriorSpeed_of_sq_lt_one
    {sigma : ℝ} (hsigma : sigma ^ (2 : ℕ) < 1) :
    StrictAntiOn (radialPSWFExteriorSpeed sigma) (Ioi 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 1) ?_ ?_
  · intro z hz
    exact (continuousAt_radialPSWFExteriorSpeed sigma hz).continuousWithinAt
  · rw [interior_Ioi]
    intro z hz
    rw [(hasDerivAt_radialPSWFExteriorSpeed hsigma.le hz).deriv]
    have hz0 : 0 < z := zero_lt_one.trans hz
    have hnum : z * (sigma ^ (2 : ℕ) - 1) < 0 := mul_neg_of_pos_of_neg hz0 (sub_neg.mpr hsigma)
    have hden : 0 <
        (z ^ (2 : ℕ) - 1) ^ (2 : ℕ) * radialPSWFExteriorSpeed sigma z := by
      have hzden : 0 < z ^ (2 : ℕ) - 1 := by
        calc
          0 < (z - 1) * (z + 1) := mul_pos (sub_pos.mpr hz) (by linarith)
          _ = z ^ (2 : ℕ) - 1 := by ring
      exact mul_pos (sq_pos_of_pos hzden)
        (radialPSWFExteriorSpeed_pos hsigma.le hz)
    exact div_neg_of_neg_of_pos hnum hden

/-- Below the boundary turning parameter, the integrated exterior phase is strictly concave. -/
theorem strictConcaveOn_radialPSWFExteriorPhase_of_sq_lt_one
    {sigma : ℝ} (hsigma : sigma ^ (2 : ℕ) < 1) :
    StrictConcaveOn ℝ (Ioi 1) (radialPSWFExteriorPhase sigma) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 1)
    (continuousOn_radialPSWFExteriorPhase_Ioi sigma) ?_
  rw [interior_Ioi]
  intro x hx y hy hxy
  rw [deriv_radialPSWFExteriorPhase_eq sigma hx,
    deriv_radialPSWFExteriorPhase_eq sigma hy]
  exact strictAntiOn_radialPSWFExteriorSpeed_of_sq_lt_one hsigma hx hy hxy

/-- **Radial PSWF exterior-phase concavity/secant universality.**  Every finite exterior phase
increment is trapped between its endpoint speeds and above the free speed. -/
theorem radialPSWFExteriorPhase_concavitySecantUniversality
    {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ConcaveOn ℝ (Ioi 1) (radialPSWFExteriorPhase sigma) ∧
      ∀ ⦃x y : ℝ⦄, 1 < x → x < y →
        1 ≤ radialPSWFExteriorSpeed sigma y ∧
          radialPSWFExteriorSpeed sigma y ≤
            (radialPSWFExteriorPhase sigma y - radialPSWFExteriorPhase sigma x) / (y - x) ∧
          (radialPSWFExteriorPhase sigma y - radialPSWFExteriorPhase sigma x) / (y - x) ≤
            radialPSWFExteriorSpeed sigma x := by
  have hsigmaSq : sigma ^ (2 : ℕ) ≤ 1 := by nlinarith
  have hconcave := concaveOn_radialPSWFExteriorPhase hsigmaSq
  refine ⟨hconcave, ?_⟩
  intro x y hx hxy
  have hy : 1 < y := hx.trans hxy
  refine ⟨one_le_radialPSWFExteriorSpeed hsigma0 hsigma1 hy, ?_, ?_⟩
  · simpa only [slope_def_field] using
      hconcave.le_slope_of_hasDerivAt hx hy hxy
        (hasDerivAt_radialPSWFExteriorPhase sigma hy)
  · simpa only [slope_def_field] using
      hconcave.slope_le_of_hasDerivAt hx hy hxy
        (hasDerivAt_radialPSWFExteriorPhase sigma hx)

/-- Strict phase: below the boundary turning parameter, every nontrivial secant lies strictly
between the two endpoint speeds while retaining the free-speed floor. -/
theorem radialPSWFExteriorPhase_strictConcavitySecantUniversality
    {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) :
    StrictConcaveOn ℝ (Ioi 1) (radialPSWFExteriorPhase sigma) ∧
      ∀ ⦃x y : ℝ⦄, 1 < x → x < y →
        1 ≤ radialPSWFExteriorSpeed sigma y ∧
          radialPSWFExteriorSpeed sigma y <
            (radialPSWFExteriorPhase sigma y - radialPSWFExteriorPhase sigma x) / (y - x) ∧
          (radialPSWFExteriorPhase sigma y - radialPSWFExteriorPhase sigma x) / (y - x) <
            radialPSWFExteriorSpeed sigma x := by
  have hsigmaSq : sigma ^ (2 : ℕ) < 1 := by nlinarith
  have hstrict := strictConcaveOn_radialPSWFExteriorPhase_of_sq_lt_one hsigmaSq
  refine ⟨hstrict, ?_⟩
  intro x y hx hxy
  have hy : 1 < y := hx.trans hxy
  refine ⟨one_le_radialPSWFExteriorSpeed hsigma0 hsigma1.le hy, ?_, ?_⟩
  · simpa only [slope_def_field] using
      hstrict.lt_slope_of_hasDerivAt hx hy hxy
        (hasDerivAt_radialPSWFExteriorPhase sigma hy)
  · simpa only [slope_def_field] using
      hstrict.slope_lt_of_hasDerivAt hx hy hxy
        (hasDerivAt_radialPSWFExteriorPhase sigma hx)

end

end RHTower
