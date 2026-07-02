/-
# The window threshold is SHARP: coverage and obstruction meet at `‖b‖ = 2+√2`

The two-sided capstone of the window program.  At every parameter STRICTLY above modulus
`2+√2` the full window capstone holds — `u₀` and the Böttcher window branch are algebraically
independent over `ℂ(z)` (`u0_phiB_independence`, the coverage half).  AT modulus `2+√2` itself
there is a parameter — `b = −(2+√2)` — whose filled Julia set meets the closed unit disk, so no
Böttcher branch is analytic across the natural-boundary circle and the window route is void
(the obstruction half; the witness orbit is `1 ↦ −(1+√2) ↦ 1+√2 ↦ 1+√2`, and the witness point
`x₀ = 1` sits EXACTLY on the natural-boundary circle).

`2+√2` is therefore the exact uniform (direction-independent) threshold of the window method:
not an artifact of the estimates, but the modulus where the first-step clearance
`‖b‖ − 1 − xStar ‖b‖` vanishes AND where the negative-real obstruction interval ends.
-/
import GaloisForLFunctions.U0.U0PhiLargeCapstone
import GaloisForLFunctions.U0.U0WindowObstruction

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0 U0NaturalBoundary U0MeroCarrier U0PhiFourDescent
open U0PhiLargeWindow U0PhiLargeCarrier U0PhiLargeDescent U0PhiLargeCapstone

namespace U0WindowSharpness

/-- **The sharp window threshold theorem.**  Coverage strictly above `2+√2` (full algebraic
independence of `u₀` and the window branch, every parameter), matched by an obstruction witness
AT modulus `2+√2` (the filled Julia set meets the closed unit disk, so the window route is
void).  The constant is exact. -/
theorem window_threshold_sharp :
    (∀ b : ℂ, ∀ hb : 2 + Real.sqrt 2 < ‖b‖,
      letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
        (annWB_nonempty hb)
      letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
        (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
          (annWB_infinite hb)).toAlgebra
      NoRelation (RatFunc ℂ)
        (algebraMap (analyticSubring (annWB b)) (meroField (annWB b)) (phiBAn b hb))
        (algebraMap (analyticSubring (annWB b)) (meroField (annWB b))
          (u0AnSub annWB_subset_Ext))) ∧
    (∃ b : ℂ, ‖b‖ = 2 + Real.sqrt 2 ∧ ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b) := by
  constructor
  · intro b hb
    exact u0_phiB_independence hb
  · refine ⟨(((-2 - Real.sqrt 2 : ℝ)) : ℂ), ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (show (-2 - Real.sqrt 2 : ℝ) < 0 by linarith [Real.sqrt_nonneg 2])]
      ring
    · exact U0WindowObstruction.filledJulia_meets_unit_disk
        (by linarith [Real.sqrt_nonneg 2]) (le_refl _)

end U0WindowSharpness
