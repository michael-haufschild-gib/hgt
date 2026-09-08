import GaloisForLFunctions.RHTower.FokasLenellsSpaceMultiplier
import GaloisForLFunctions.RHTower.FokasLenellsTimeInverse

/-!
# Spatial differentiation of the constructed Cauchy inverse

The resolvent difference identity reduces spatial differentiation to the
proved strong derivative of the actual Cauchy operator. Joint continuity
of the constructed inverse then gives R Cₓ R, C¹ spatial orbits, and a
uniform operator-norm Lipschitz estimate in position.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

theorem directSolution_space_slope (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (d : Boundary) :
    slope (fun r => directSolution q t r d) x y =
      directSolution q t y (slope (fun r => directCauchyOperator q t r (directSolution q t x d)) x y) := by
  simp only [slope_def_module]
  rw [directSolution_resolvent_difference q t y t x d]
  exact (map_smul (((directResolventUnit q t y)⁻¹).val.restrictScalars ℝ) _ _).symm

def directSpaceSolution (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) : Boundary :=
  directSolution q t x (directCauchySpaceOperator q t x (directSolution q t x d))

/-- The actual inverse derivative in position is R Cₓ R on every fixed forcing vector. -/
theorem directSolution_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    HasDerivAt (fun y => directSolution q t y d) (directSpaceSolution q t x d) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hd := (directCauchyOperator_space_hasDerivAt q t x (directSolution q t x d)).tendsto_slope
  have hs : Tendsto (fun y : ℝ => y) (𝓝[≠] x) (𝓝 x) := nhdsWithin_le_nhds
  have hp := ((tendsto_const_nhds (x := t)).prodMk_nhds hs).prodMk_nhds hd
  have hh := ((continuous_directSolution_joint q).tendsto
    ((t,x),directCauchySpaceOperator q t x (directSolution q t x d))).comp hp
  exact hh.congr' (Eventually.of_forall fun y => (directSolution_space_slope q t x y d).symm)

/-- The spatial inverse derivative depends jointly continuously on both physical parameters and forcing. -/
theorem continuous_directSpaceSolution_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directSpaceSolution q p.1.1 p.1.2 p.2) := by
  have h1 := continuous_fst.prodMk (continuous_directSolution_joint q)
  have h2 := (continuous_directCauchySpaceOperator_joint q).comp h1
  have h3 := continuous_fst.prodMk h2
  have h4 := (continuous_directSolution_joint q).comp h3
  exact h4

/-- The actual inverse orbits are C¹ in position for arbitrary L² forcing. -/
theorem directSolution_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (d : Boundary) :
    ContDiff ℝ 1 (fun x => directSolution q t x d) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directSolution_space_hasDerivAt q t x d).differentiableAt,?_⟩
  have he : deriv (fun x => directSolution q t x d) = fun x => directSpaceSolution q t x d :=
    funext fun x => (directSolution_space_hasDerivAt q t x d).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => ((t,x),d)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
  have hh := (continuous_directSpaceSolution_joint q).comp hc
  exact hh

/-- The spatial derivative solves its own exact Cauchy equation. -/
theorem directSpaceSolution_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    directSpaceSolution q t x d-directCauchyOperator q t x (directSpaceSolution q t x d) =
      directCauchySpaceOperator q t x (directSolution q t x d) :=
  directSolution_equation q t x _

theorem directSpaceSolution_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    ‖directSpaceSolution q t x d‖ ≤ ((81/25 : ℝ)*directSpaceOperatorBudget q)*‖d‖ := by
  calc
    _ ≤ (9/5 : ℝ)*‖directCauchySpaceOperator q t x (directSolution q t x d)‖ := directSolution_bound q t x _
    _ ≤ (9/5 : ℝ)*(directSpaceOperatorBudget q*‖directSolution q t x d‖) :=
      mul_le_mul_of_nonneg_left (directCauchySpaceOperator_bound q t x _) (by positivity)
    _ ≤ (9/5 : ℝ)*(directSpaceOperatorBudget q*((9/5 : ℝ)*‖d‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (directSolution_bound q t x d) (directSpaceOperatorBudget_nonneg q)) (by positivity)
    _ = _ := by ring

/-- Spatial perturbations of the actual inverse have a uniform global Lipschitz estimate. -/
theorem directSolution_space_bound (q : SchwartzMap ℝ ℂ) (t x y : ℝ) (d : Boundary) :
    ‖directSolution q t x d-directSolution q t y d‖ ≤
      (((81/25 : ℝ)*directSpaceOperatorBudget q)*‖d‖)*|x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (directSolution_space_hasDerivAt q t r d).hasDerivWithinAt)
    (fun r _ => directSpaceSolution_bound q t r d) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- The constructed inverse is Lipschitz in position even in operator norm. -/
theorem norm_directResolventInverse_space_sub_le (q : SchwartzMap ℝ ℂ) (t x y : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val-((directResolventUnit q t y)⁻¹).val‖ ≤
      ((81/25 : ℝ)*directSpaceOperatorBudget q)*|x-y| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact mul_nonneg (mul_nonneg (by positivity) (directSpaceOperatorBudget_nonneg q)) (abs_nonneg _)
  · intro d
    change ‖directSolution q t x d-directSolution q t y d‖ ≤ _
    have hh := directSolution_space_bound q t x y d
    simpa only [mul_right_comm] using hh

end
end RHTower.FokasLenells
