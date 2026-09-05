import Mathlib

/-!
# Finite projected-coarea transfer from arXiv:2608.29060

The corpus currently has no canonical surface measure on arbitrary-dimensional unit spheres.
This module isolates the exact finite-cubature form of the paper's projected-coarea argument:
any weighted normal family integrating absolute linear projections exactly converts total
projected variation into path length.  No numerical quadrature or sampled approximation occurs.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Total absolute projected variation of a finite displacement family. -/
def bellmanShorelineFiniteProjectedVariation
    {I : Type*} [Fintype I] (step : I → F) (u : F) : ℝ :=
  ∑ i, |inner ℝ u (step i)|

/-- Polygonal length represented by a finite displacement family. -/
def bellmanShorelineFinitePathLength
    {I : Type*} [Fintype I] (step : I → F) : ℝ :=
  ∑ i, ‖step i‖

/-- Finite exact-cubature version of projected coarea.  Isotropy is required only on actual
displacements, rather than on every ambient vector. -/
theorem bellmanShoreline_finiteProjectedCoarea
    {I J : Type*} [Fintype I] [Fintype J]
    (step : I → F) (normal : J → F) (weight : J → ℝ) (c : ℝ)
    (hisotropy : ∀ i, ∑ j, weight j * |inner ℝ (normal j) (step i)| = c * ‖step i‖) :
    ∑ j, weight j * bellmanShorelineFiniteProjectedVariation step (normal j) =
      c * bellmanShorelineFinitePathLength step := by
  simp_rw [bellmanShorelineFiniteProjectedVariation, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hisotropy]
  rw [bellmanShorelineFinitePathLength, Finset.mul_sum]

/-- Variation defect remaining after paying twice a prescribed directional width. -/
def bellmanShorelineProjectionDefect
    {I : Type*} [Fintype I] (step : I → F) (width : F → ℝ) (u : F) : ℝ :=
  bellmanShorelineFiniteProjectedVariation step u - 2 * width u

/-- Pointwise projection lower bound is exactly nonnegativity of the variation defect. -/
theorem bellmanShoreline_projectionDefect_nonneg_iff
    {I : Type*} [Fintype I] (step : I → F) (width : F → ℝ) (u : F) :
    0 ≤ bellmanShorelineProjectionDefect step width u ↔
      2 * width u ≤ bellmanShorelineFiniteProjectedVariation step u := by
  rw [bellmanShorelineProjectionDefect]
  constructor <;> intro h <;> linarith

/-- Finite projected coarea splits exactly into directional width stock and nonnegative defect. -/
theorem bellmanShoreline_finiteProjectedCoarea_decomposition
    {I J : Type*} [Fintype I] [Fintype J]
    (step : I → F) (normal : J → F) (weight : J → ℝ)
    (width : F → ℝ) (c : ℝ)
    (hisotropy : ∀ i, ∑ j, weight j * |inner ℝ (normal j) (step i)| = c * ‖step i‖) :
    c * bellmanShorelineFinitePathLength step =
      2 * ∑ j, weight j * width (normal j) +
        ∑ j, weight j * bellmanShorelineProjectionDefect step width (normal j) := by
  rw [← bellmanShoreline_finiteProjectedCoarea step normal weight c hisotropy]
  simp_rw [bellmanShorelineProjectionDefect, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfactor : ∀ j, weight j * (2 * width (normal j)) =
      2 * (weight j * width (normal j)) := by
    intro j
    ring
  simp_rw [hfactor, ← Finset.mul_sum]
  ring

/-- Finite-cubature lower bound: if every directional width is at least `2m`, projected variation
pays twice that width, and weights are nonnegative, then coarea stock is at least
`4m` times total normal weight. -/
theorem bellmanShoreline_finiteProjectedCoarea_lower
    {I J : Type*} [Fintype I] [Fintype J]
    (step : I → F) (normal : J → F) (weight : J → ℝ)
    (width : F → ℝ) (c m : ℝ)
    (hweight : ∀ j, 0 ≤ weight j)
    (hwidth : ∀ j, 2 * m ≤ width (normal j))
    (hvariation : ∀ j,
      2 * width (normal j) ≤ bellmanShorelineFiniteProjectedVariation step (normal j))
    (hisotropy : ∀ i, ∑ j, weight j * |inner ℝ (normal j) (step i)| = c * ‖step i‖) :
    4 * m * (∑ j, weight j) ≤ c * bellmanShorelineFinitePathLength step := by
  have hwidthSum : 2 * m * (∑ j, weight j) ≤
      ∑ j, weight j * width (normal j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [mul_comm (2 * m) (weight j)]
    exact mul_le_mul_of_nonneg_left (hwidth j) (hweight j)
  have hdefectSum : 0 ≤
      ∑ j, weight j * bellmanShorelineProjectionDefect step width (normal j) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hweight j)
      ((bellmanShoreline_projectionDefect_nonneg_iff step width (normal j)).mpr
        (hvariation j))
  rw [bellmanShoreline_finiteProjectedCoarea_decomposition
    step normal weight width c hisotropy]
  nlinarith

end GaloisForLFunctions.HTGeometry

end
