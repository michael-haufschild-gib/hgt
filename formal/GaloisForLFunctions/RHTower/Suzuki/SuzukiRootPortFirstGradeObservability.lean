import GaloisForLFunctions.RHTower.Suzuki.SuzukiExteriorFeshbachPruning

/-!
# First-grade observability of Suzuki endpoint roots

The full prime adjacency must retain the two exterior endpoint roots until after boundary-log
transport.  This module formalizes the load-bearing first-step fact: every strictly visible
valuation step sends both oriented root coefficients to separately observable strict-interior
coordinates.  Opposite-end spatial resonance cannot cancel them because the root label remains
part of the Hilbert coordinate.

No theorem assumes a completed-domain carrier map or RH.
-/

open Complex Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Two oriented endpoint coefficients embedded in the unpruned seam Hilbert carrier. -/
def suzukiRootTraceVector (βleft βright : ℂ) : SuzukiSeamHilbert :=
  βleft • lp.single 2 (SuzukiSeamRoot.left, 0) 1 +
    βright • lp.single 2 (SuzukiSeamRoot.right, 0) 1

@[simp] theorem suzukiRootTraceVector_left_root (βleft βright : ℂ) :
    suzukiRootTraceVector βleft βright (SuzukiSeamRoot.left, 0) = βleft := by
  simp [suzukiRootTraceVector, lp.single_apply]

@[simp] theorem suzukiRootTraceVector_right_root (βleft βright : ℂ) :
    suzukiRootTraceVector βleft βright (SuzukiSeamRoot.right, 0) = βright := by
  simp [suzukiRootTraceVector, lp.single_apply]

/-- A valuation step of positive displacement strictly below the aperture width produces an
admissible left-root descendant. -/
theorem suzukiLeftRoot_step_admissible
    (a : ℝ) (δ : SuzukiSeamValuation)
    (hδpos : 0 < primeSeamCoordinate δ)
    (hδlt : primeSeamCoordinate δ < 2 * a) :
    (SuzukiSeamRoot.left, δ) ∈ suzukiAdmissibleSeamVertices a := by
  rw [suzukiAdmissibleSeamVertices, Set.mem_setOf_eq]
  simp only [suzukiSeamLocation]
  rw [abs_lt]
  constructor <;> linarith

/-- The same strictly visible valuation step produces an admissible right-root descendant. -/
theorem suzukiRightRoot_step_admissible
    (a : ℝ) (δ : SuzukiSeamValuation)
    (hδpos : 0 < primeSeamCoordinate δ)
    (hδlt : primeSeamCoordinate δ < 2 * a) :
    (SuzukiSeamRoot.right, δ) ∈ suzukiAdmissibleSeamVertices a := by
  rw [suzukiAdmissibleSeamVertices, Set.mem_setOf_eq]
  simp only [suzukiSeamLocation]
  rw [abs_lt]
  constructor <;> linarith

/-- The symmetric full prime step exposes the left endpoint coefficient at its strict-interior
descendant coordinate. -/
theorem suzukiFirstGrade_left_coordinate
    (a : ℝ) (δ : SuzukiSeamValuation) (βleft βright : ℂ)
    (hδpos : 0 < primeSeamCoordinate δ)
    (hδlt : primeSeamCoordinate δ < 2 * a) :
    lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
        (suzukiSymmetricSeamStep δ (suzukiRootTraceVector βleft βright))
        (SuzukiSeamRoot.left, δ) =
      βleft := by
  have htwo : δ + δ ≠ 0 := by
    intro h
    have hcoord := congrArg primeSeamCoordinate h
    simp only [map_add, map_zero] at hcoord
    linarith
  rw [lpCoordinateProjection_apply,
    indicator_of_mem (suzukiLeftRoot_step_admissible a δ hδpos hδlt),
    suzukiSymmetricSeamStep_apply]
  simp [suzukiRootTraceVector, lp.single_apply, htwo]

/-- The symmetric full prime step exposes the right endpoint coefficient at its strict-interior
descendant coordinate. -/
theorem suzukiFirstGrade_right_coordinate
    (a : ℝ) (δ : SuzukiSeamValuation) (βleft βright : ℂ)
    (hδpos : 0 < primeSeamCoordinate δ)
    (hδlt : primeSeamCoordinate δ < 2 * a) :
    lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
        (suzukiSymmetricSeamStep δ (suzukiRootTraceVector βleft βright))
        (SuzukiSeamRoot.right, δ) =
      βright := by
  have htwo : δ + δ ≠ 0 := by
    intro h
    have hcoord := congrArg primeSeamCoordinate h
    simp only [map_add, map_zero] at hcoord
    linarith
  rw [lpCoordinateProjection_apply,
    indicator_of_mem (suzukiRightRoot_step_admissible a δ hδpos hδlt),
    suzukiSymmetricSeamStep_apply]
  simp [suzukiRootTraceVector, lp.single_apply, htwo]

/-- **First-grade root-port observability.**  One strictly visible prime step already separates
both oriented endpoint coefficients. -/
theorem suzukiFirstGrade_rootTrace_injective
    (a : ℝ) (δ : SuzukiSeamValuation)
    (hδpos : 0 < primeSeamCoordinate δ)
    (hδlt : primeSeamCoordinate δ < 2 * a)
    (βleft βright : ℂ)
    (hzero :
      lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
        (suzukiSymmetricSeamStep δ (suzukiRootTraceVector βleft βright)) = 0) :
    βleft = 0 ∧ βright = 0 := by
  constructor
  · have hcoord := congrArg
      (fun f : SuzukiSeamHilbert => f (SuzukiSeamRoot.left, δ)) hzero
    simpa [suzukiFirstGrade_left_coordinate a δ βleft βright hδpos hδlt] using hcoord
  · have hcoord := congrArg
      (fun f : SuzukiSeamHilbert => f (SuzukiSeamRoot.right, δ)) hzero
    simpa [suzukiFirstGrade_right_coordinate a δ βleft βright hδpos hδlt] using hcoord

end GaloisForLFunctions.RHTower
