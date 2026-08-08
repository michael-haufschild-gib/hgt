import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature
import GaloisForLFunctions.RHTower.XiShiftedHankelNullPolynomialRoots
import GaloisForLFunctions.RHTower.XiShiftedHankelHeatResolventBridge

/-!
# Shifted Xi first faces as positive flat quadrature

At a first singular shifted-Xi Hankel face, the null polynomial's real-simple roots carry positive
interpolatory weights reproducing the shifted moments through degree `2n`. The first omitted Xi
coupling—and hence the exact boundary heat integral—is the first quadrature error, in degree
`2n+1`.
-/

open scoped BigOperators
open Matrix Polynomial

namespace RHTower

noncomputable section

def xiShiftedHankelBoundaryNodes {n : ℕ} (c : Fin (n + 1) → ℝ) : Finset ℝ :=
  HTGeometry.finiteHankelBoundaryNodes c

def xiShiftedHankelBoundaryWeight
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  HTGeometry.finiteHankelBoundaryWeight
    (fun k => (xiShiftedReciprocalMoment y k).re) c x

def xiShiftedHankelBoundaryQuadratureError
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (f : Polynomial ℝ) : ℝ :=
  HTGeometry.finiteHankelBoundaryQuadratureError
    (fun k => (xiShiftedReciprocalMoment y k).re) c f

theorem xiShiftedHankelBoundaryNodes_card
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    (xiShiftedHankelBoundaryNodes c).card = n := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  change (HTGeometry.finiteHankelBoundaryNodes c).card = n
  apply HTGeometry.finiteHankelBoundaryNodes_card c
  · change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
    exact hhead
  · change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
    exact hc
  · exact hlast

theorem xiShiftedHankelBoundaryWeight_pos
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    {x : ℝ} (hx : x ∈ xiShiftedHankelBoundaryNodes c) :
    0 < xiShiftedHankelBoundaryWeight y c x := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  change 0 < HTGeometry.finiteHankelBoundaryWeight
    (fun k => (xiShiftedReciprocalMoment y k).re) c x
  apply HTGeometry.finiteHankelBoundaryWeight_pos c
  · change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
    exact hhead
  · change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
    exact hc
  · exact hlast
  · exact hx

theorem xiShiftedHankelBoundaryQuadratureError_eq_zero
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (f : Polynomial ℝ) (hf : f.degree ≤ ((2 * n : ℕ) : WithBot ℕ)) :
    xiShiftedHankelBoundaryQuadratureError y c f = 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  change HTGeometry.finiteHankelBoundaryQuadratureError
    (fun k => (xiShiftedReciprocalMoment y k).re) c f = 0
  apply HTGeometry.finiteHankelBoundaryQuadratureError_eq_zero c
  · change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
    exact hhead
  · change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
    exact hc
  · exact hlast
  · exact hf

/-- The sole extension coordinate is exactly the first quadrature remainder. -/
theorem xiShiftedHankelFirstOmittedCoupling_eq_boundaryQuadratureError
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelFirstOmittedCoupling y (n + 1) c =
      xiShiftedHankelBoundaryQuadratureError y c
        (X ^ (n + 1) * xiShiftedHankelNullPolynomial c) := by
  rw [xiShiftedHankelFirstOmittedCoupling,
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling]
  change (∑ j : Fin (n + 1), c j *
      (xiShiftedReciprocalMoment y (n + 1 + (j : ℕ))).re) = _
  rw [show (∑ j : Fin (n + 1), c j *
      (xiShiftedReciprocalMoment y (n + 1 + (j : ℕ))).re) =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X ^ (n + 1) * HTGeometry.finiteHankelNullPolynomial c) by
    exact (HTGeometry.momentFunctional_X_pow_mul_finiteHankelNullPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) c).symm]
  exact (HTGeometry.finiteHankelBoundary_firstRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c).symm

/-- Heat-source form: the first singular-face obstruction is the first positive-flat-quadrature
remainder of the shifted Xi moment functional. -/
theorem integral_xiShiftedHankelBoundaryHeatKernel_eq_boundaryQuadratureError
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
      xiShiftedHankelBoundaryHeatKernel y (n + 1) c t) =
      xiShiftedHankelBoundaryQuadratureError y c
        (X ^ (n + 1) * xiShiftedHankelNullPolynomial c) := by
  rw [integral_xiShiftedHankelBoundaryHeatKernel_eq_firstOmittedCoupling hy,
    xiShiftedHankelFirstOmittedCoupling_eq_boundaryQuadratureError]

end

end RHTower
