import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquarePoleDecomposition
import GaloisForLFunctions.RHTower.RectangleConfluentTwoPoleResidue

/-!
# Finite contour crossing for the Gaussian zeta-square integrand

Exact confluent-residue crossing on the balanced strip from real part -1 to 1.
-/

noncomputable section

open Complex Set

namespace RHTower.Sieve

/-- Exact finite Gaussian zeta-square contour crossing. -/
theorem rectIntegral_smoothAFEZetaSquareMellinIntegrand
    (tau T : ℝ) {x : ℝ} (hx : 0 < x) (hT : |tau| < T) :
    rectIntegral (smoothAFEZetaSquareMellinIntegrand (linePt tau) x)
        (Complex.mk (-1) (-T)) (Complex.mk 1 T) =
      2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ (2 : ℕ) +
          confluentResidueCoeff
            (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)) := by
  have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg tau) hT
  apply rectIntegral_eq_confluent_two_pole_residues_of_analyticOnNhd
    (U := Set.univ)
    (p := 0) (q := 1 - linePt tau)
    (rp := riemannZeta (linePt tau) ^ (2 : ℕ))
    (dq := confluentDoubleCoeff
      (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
      (1 - linePt tau))
    (rq := confluentResidueCoeff
      (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
      (1 - linePt tau))
    (R := confluentPoleRemainder
      (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
      (1 - linePt tau))
  · norm_num
  · norm_num
  · simpa using neg_lt_zero.mpr hT0
  · simpa using hT0
  · change (-1 : ℝ) < (1 - linePt tau).re
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  · change (1 - linePt tau).re < (1 : ℝ)
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  · change -T < (1 - linePt tau).im
    have hlineim : (linePt tau).im = tau := by unfold linePt; simp
    rw [Complex.sub_im, Complex.one_im, hlineim]
    have htau : tau < T := lt_of_le_of_lt (le_abs_self tau) hT
    linarith
  · change (1 - linePt tau).im < T
    have hlineim : (linePt tau).im = tau := by unfold linePt; simp
    rw [Complex.sub_im, Complex.one_im, hlineim]
    have htau : -tau < T := lt_of_le_of_lt (neg_le_abs tau) hT
    linarith
  · intro z hz
    simp
  · exact (differentiable_confluentPoleRemainder
      (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
      (1 - linePt tau)
      (differentiable_smoothAFEZetaSquarePoleNumerator
        (linePt tau) hx)).differentiableOn.analyticOnNhd isOpen_univ
  · intro z hz0 hza
    rw [smoothAFEZetaSquareMellinIntegrand_confluent_decomposition
      tau hx hz0 hza]
    simp only [sub_zero]
    ring


end RHTower.Sieve
