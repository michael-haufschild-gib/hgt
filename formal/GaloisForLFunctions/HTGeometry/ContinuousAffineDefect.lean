import GaloisForLFunctions.HTGeometry.ContinuousPolynomialDefect
import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Proper continuous-affine fibers are nowhere dense

A continuous affine scalar observation is a linear observation plus its value at zero.  Encoding
that decomposition as a one-variable polynomial lets the existing continuous-polynomial defect
theorem prove that a zero fiber is closed and has empty interior as soon as one point escapes it.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The linear part of a continuous affine scalar observation, packaged as a one-coordinate
observation map. -/
def continuousAffineLinearObservation
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [IsTopologicalAddGroup X]
    (f : X →ᴬ[ℂ] ℂ) : X →L[ℂ] (Unit → ℂ) :=
  ContinuousLinearMap.pi fun _ ↦ f.contLinear

/-- The one-variable polynomial representing a continuous affine scalar observation. -/
def continuousAffineObservationPolynomial
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [IsTopologicalAddGroup X]
    (f : X →ᴬ[ℂ] ℂ) : MvPolynomial Unit ℂ :=
  MvPolynomial.X () + MvPolynomial.C (f 0)

theorem eval_continuousAffineObservationPolynomial
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [IsTopologicalAddGroup X]
    (f : X →ᴬ[ℂ] ℂ) (x : X) :
    MvPolynomial.eval (continuousAffineLinearObservation f x)
      (continuousAffineObservationPolynomial f) = f x := by
  have h := congrFun (ContinuousAffineMap.decomp f) x
  simpa [continuousAffineLinearObservation, continuousAffineObservationPolynomial] using h.symm

/-- A continuous affine zero fiber is closed. -/
theorem isClosed_continuousAffineMap_zero
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [IsTopologicalAddGroup X]
    (f : X →ᴬ[ℂ] ℂ) :
    IsClosed {x | f x = 0} := by
  have h := isClosed_continuousLinearMap_mvPolynomial_zero
    (continuousAffineLinearObservation f) (continuousAffineObservationPolynomial f)
  simpa only [eval_continuousAffineObservationPolynomial] using h

/-- One nonzero value makes a continuous affine zero fiber have empty interior. -/
theorem interior_continuousAffineMap_zero_eq_empty_of_witness
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (f : X →ᴬ[ℂ] ℂ) (h : X) (hh : f h ≠ 0) :
    interior {x | f x = 0} = ∅ := by
  have hpoly := interior_continuousLinearMap_mvPolynomial_zero_eq_empty_of_witness
    (continuousAffineLinearObservation f) (continuousAffineObservationPolynomial f) h
    (by simpa only [eval_continuousAffineObservationPolynomial] using hh)
  simpa only [eval_continuousAffineObservationPolynomial] using hpoly

/-- A proper continuous affine zero fiber is nowhere dense. -/
theorem isNowhereDense_continuousAffineMap_zero_of_witness
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (f : X →ᴬ[ℂ] ℂ) (h : X) (hh : f h ≠ 0) :
    IsNowhereDense {x | f x = 0} := by
  rw [(isClosed_continuousAffineMap_zero f).isNowhereDense_iff]
  exact interior_continuousAffineMap_zero_eq_empty_of_witness f h hh

end

end GaloisForLFunctions.HTGeometry
