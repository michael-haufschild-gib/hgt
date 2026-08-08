import GaloisForLFunctions.HTGeometry.FiniteMomentNullPolynomialRoots
import GaloisForLFunctions.RHTower.XiShiftedHankelFirstCrossing

/-!
# Real-simple null polynomials on shifted Xi Hankel faces

At a first singular shifted-Xi Hankel block, positivity of the preceding block forces every
nonzero null polynomial to have full degree. Finite moment-root rigidity then makes all of its
roots real and simple. This is unconditional and uses only the finite face data.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Polynomial carried by a finite shifted-Xi Hankel coefficient vector. -/
def xiShiftedHankelNullPolynomial {n : ℕ} (c : Fin n → ℝ) : Polynomial ℝ :=
  HTGeometry.finiteHankelNullPolynomial c

theorem xiShiftedHankelNullPolynomial_natDegree
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    (xiShiftedHankelNullPolynomial c).natDegree = n := by
  apply HTGeometry.finiteHankelNullPolynomial_natDegree
  exact xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc

/-- **First-face real-rootedness.** Every complex root of the shifted-Xi null polynomial is real. -/
theorem xiShiftedHankelNullPolynomial_root_im_eq_zero
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    {z : ℂ} (hz : Polynomial.aeval z (xiShiftedHankelNullPolynomial c) = 0) :
    z.im = 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  have hhead' :
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
    exact hhead
  have hc' :
      HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 := by
    change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
    exact hc
  exact HTGeometry.finiteHankelNullPolynomial_root_im_eq_zero
    c hhead' hc' hlast hz

/-- **First-face root simplicity.** Every real root of the shifted-Xi null polynomial has
multiplicity at most one. -/
theorem xiShiftedHankelNullPolynomial_rootMultiplicity_le_one
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (r : ℝ) :
    rootMultiplicity r (xiShiftedHankelNullPolynomial c) ≤ 1 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  have hhead' :
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef := by
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
    exact hhead
  have hc' :
      HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 := by
    change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
    exact hc
  exact HTGeometry.finiteHankelNullPolynomial_rootMultiplicity_le_one
    c hhead' hc' hlast r

end

end RHTower
