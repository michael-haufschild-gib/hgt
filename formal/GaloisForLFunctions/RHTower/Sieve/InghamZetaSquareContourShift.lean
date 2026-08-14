import GaloisForLFunctions.RHTower.RectangleConfluentTwoPoleResidue
import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquarePoleDecomposition

/-!
# Finite confluent contour crossing for Ingham's zeta-square Mellin integral

The critical zeta-square Mellin integrand has a Gamma pole at zero and a shifted double zeta pole
at `1 - (1/2 + i tau)`.  On every rectangle with left edge in `(-1,0)` and height larger than
`|tau|`, its exact boundary integral is `2*pi*i` times the Gamma-pole residue plus the residue
coefficient of the shifted double-pole packet.  The actual double-pole coefficient contributes
zero.
-/

noncomputable section

open Complex Set

namespace RHTower.Sieve

/-- Exact finite-rectangle contour crossing for the pole-regularized zeta-square integrand. -/
theorem rectIntegral_inghamZetaSquareMellinIntegrand
    (tau c T : ℝ) {x : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0)
    (hT : |tau| < T) :
    rectIntegral (inghamZetaSquareMellinIntegrand (linePt tau) x)
        (Complex.mk c (-T)) (Complex.mk 2 T) =
      2 * Real.pi * I *
        (riemannZeta (linePt tau) ^ 2 +
          confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)) := by
  have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg tau) hT
  have hc2 : c < 2 := by linarith
  apply rectIntegral_eq_confluent_two_pole_residues_of_analyticOnNhd
    (U := inghamZetaSquareShiftDomain)
    (p := 0) (q := 1 - linePt tau)
    (rp := riemannZeta (linePt tau) ^ 2)
    (dq := confluentDoubleCoeff
      (inghamZetaSquarePoleNumerator (linePt tau) x) (1 - linePt tau))
    (rq := confluentResidueCoeff
      (inghamZetaSquarePoleNumerator (linePt tau) x) (1 - linePt tau))
    (R := confluentPoleRemainder
      (inghamZetaSquarePoleNumerator (linePt tau) x) (1 - linePt tau))
  · simpa using hc0
  · norm_num
  · simpa using neg_lt_zero.mpr hT0
  · simpa using hT0
  · change c < (1 - linePt tau).re
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    linarith
  · norm_num [linePt_re]
  · change -T < (1 - linePt tau).im
    have hlineim : (linePt tau).im = tau := by
      unfold linePt
      simp
    rw [Complex.sub_im, Complex.one_im, hlineim]
    have htau : tau < T := lt_of_le_of_lt (le_abs_self tau) hT
    linarith
  · change (1 - linePt tau).im < T
    have hlineim : (linePt tau).im = tau := by
      unfold linePt
      simp
    rw [Complex.sub_im, Complex.one_im, hlineim]
    have htau : -tau < T := lt_of_le_of_lt (neg_le_abs tau) hT
    linarith
  · intro z hz
    change -1 < z.re
    have hzre : z.re ∈ uIcc c 2 := by
      exact hz.1
    rw [uIcc_of_le (le_of_lt hc2)] at hzre
    exact lt_of_lt_of_le hc hzre.1
  · exact (differentiableOn_inghamZetaSquareConfluentRemainder_shiftDomain tau hx).analyticOnNhd
      isOpen_inghamZetaSquareShiftDomain
  · intro z hz0 hza
    rw [inghamZetaSquareMellinIntegrand_confluent_decomposition tau hx hz0 hza]
    simp only [sub_zero]
    ring

end RHTower.Sieve
