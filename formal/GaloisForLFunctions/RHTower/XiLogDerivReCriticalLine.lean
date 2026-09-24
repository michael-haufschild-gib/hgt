import GaloisForLFunctions.RHTower.XiLogDerivReWindowWidth
import GaloisForLFunctions.RHTower.XiAntipodalShiftPhaseSplittingUniversalityLaw

/-!
# The criterion quantity on the critical line

The functional equation gives `(ξ'/ξ)(1-s) = -(ξ'/ξ)(s)` and Schwarz reflection gives
`(ξ'/ξ)(conj s) = conj (ξ'/ξ)(s)`.  On the critical line `conj s = 1 - s`, so the two combine to
`conj (ξ'/ξ)(s) = -(ξ'/ξ)(s)`: the quantity is purely imaginary there, and its real part vanishes
identically.

The critical line is therefore the exact boundary of the region in which the criterion asks for
nonnegativity, and the inequality cannot be strengthened to a strict one up to the line.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The criterion quantity vanishes identically on the critical line.**  Schwarz reflection and
the functional equation give `conj (ξ'/ξ)(s) = -(ξ'/ξ)(s)` at `s = 1/2 + it`, so its real part is
zero.  The critical line is therefore the exact boundary of the region where the criterion asks
for nonnegativity, and no strict inequality can hold up to it. -/
theorem re_logDeriv_xi_eq_zero_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    (logDeriv xi s).re = 0 := by
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    refine Complex.ext ?_ ?_
    · simp [Complex.sub_re, hs]
      ring
    · simp [Complex.sub_im]
  have h := logDeriv_xi_conj_global s
  rw [hconj, logDeriv_xi_one_sub] at h
  have hre := congrArg Complex.re h
  rw [Complex.neg_re, Complex.conj_re] at hre
  linarith

theorem re_logDeriv_xi_eq_zero_critical_line (t : ℝ) :
    (logDeriv xi (1 / 2 + (t : ℂ) * Complex.I)).re = 0 := by
  refine re_logDeriv_xi_eq_zero_of_re_eq_half ?_
  simp

end

end RHTower
