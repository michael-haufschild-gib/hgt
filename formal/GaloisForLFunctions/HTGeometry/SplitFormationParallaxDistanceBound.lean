import GaloisForLFunctions.HTGeometry.ConstitutiveSplitFormationParallax
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The quantitative parallax distance estimate

`(CPM.18)`.  If the hidden residual is bounded below by `α` on the orthogonal complement of its
kernel, then the ternary parallax energy dominates `A α²` times the squared distance to that
kernel.  Together with `(CPM.20)` this turns bounded repeated work into an exact membership
statement rather than a qualitative no-go.
-/

open Submodule

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι]
variable {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- The neutral overlap `(CPM.17)`: the states whose formation through `Fi` is already recovered
by `Fj`. -/
def neutralOverlap (Fi Fj : SplitLinearFormation ℝ X Z) : Submodule ℝ X :=
  LinearMap.ker (hiddenResidual Fi Fj)

/-- On the orthogonal complement of the neutral overlap, a lower bound for the hidden residual
transfers to a lower bound in terms of the distance to the overlap. -/
theorem norm_hiddenResidual_ge_dist
    (Fi Fj : SplitLinearFormation ℝ X Z)
    [(neutralOverlap Fi Fj).HasOrthogonalProjection] {α : ℝ} (hα : 0 ≤ α)
    (hlow : ∀ y ∈ (neutralOverlap Fi Fj)ᗮ, α * ‖y‖ ≤ ‖hiddenResidual Fi Fj y‖)
    (x : X) :
    α * (⨅ n : neutralOverlap Fi Fj, ‖x - (n : X)‖) ≤ ‖hiddenResidual Fi Fj x‖ := by
  set N := neutralOverlap Fi Fj with hN
  set p := N.starProjection x with hp
  have hpmem : p ∈ N := by
    rw [hp]
    exact N.starProjection_apply_mem x
  have hq : x - p ∈ Nᗮ := sub_starProjection_mem_orthogonal x
  have hRp : hiddenResidual Fi Fj p = 0 := hpmem
  have hRx : hiddenResidual Fi Fj (x - p) = hiddenResidual Fi Fj x := by
    rw [map_sub, hRp, sub_zero]
  have hmin : ‖x - p‖ = ⨅ n : N, ‖x - (n : X)‖ := starProjection_minimal x
  have := hlow (x - p) hq
  rw [hRx, hmin] at this
  exact this

/-- **(CPM.18)  The quantitative parallax distance estimate.** -/
theorem parallaxEnergy_ge_dist_sq
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) {A B α : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hframe : IsResidualFusionFrame F j A B)
    [(neutralOverlap (F i) (F j)).HasOrthogonalProjection]
    (hlow : ∀ y ∈ (neutralOverlap (F i) (F j))ᗮ,
      α * ‖y‖ ≤ ‖hiddenResidual (F i) (F j) y‖)
    (x : X) :
    A * α ^ 2 * (⨅ n : neutralOverlap (F i) (F j), ‖x - (n : X)‖) ^ 2
      ≤ parallaxEnergy F i j x := by
  have hdist_nonneg : 0 ≤ ⨅ n : neutralOverlap (F i) (F j), ‖x - (n : X)‖ := by
    refine le_ciInf fun n => norm_nonneg _
  have hstep := norm_hiddenResidual_ge_dist (F i) (F j) hα hlow x
  have hsq : (α * ⨅ n : neutralOverlap (F i) (F j), ‖x - (n : X)‖) ^ 2
      ≤ ‖hiddenResidual (F i) (F j) x‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hstep 2
  have hframe' := (parallaxEnergy_fusionFrame_bounds F i j x hframe).1
  calc A * α ^ 2 * (⨅ n : neutralOverlap (F i) (F j), ‖x - (n : X)‖) ^ 2
      = A * (α * ⨅ n : neutralOverlap (F i) (F j), ‖x - (n : X)‖) ^ 2 := by ring
    _ ≤ A * ‖hiddenResidual (F i) (F j) x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hA
    _ ≤ parallaxEnergy F i j x := hframe'

end GaloisForLFunctions.HTGeometry
