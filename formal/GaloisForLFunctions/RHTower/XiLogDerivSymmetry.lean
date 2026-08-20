import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness
import GaloisForLFunctions.RHTower.XiRectangleZeroCount
import GaloisForLFunctions.PNTPlus.ZetaConj

/-!
# The two symmetries of `ξ'/ξ`

Schwarz reflection `ξ(s̄) = conj ξ(s)` and the functional equation `ξ(1−s) = ξ(s)` transfer to the
logarithmic derivative as

`ξ'/ξ (s̄) = conj (ξ'/ξ (s))`,   `ξ'/ξ (1−s) = −ξ'/ξ (s)`,

the second because differentiating the functional equation flips the sign.  Combining them, the
real part on the reflected vertical line is the negative of the real part on the original one, and
the imaginary part on the reflected horizontal segment is unchanged.  These four identities are what
fold the four sides of a symmetric rectangle onto one quarter path.
-/

open Complex

noncomputable section

namespace RHTower

/-! ## The logarithmic-derivative symmetries

The two derivative symmetries `deriv_xi_conj` and `deriv_xi_one_sub` they rest on are
`RHTower.XiEdgeLogDerivativeBlindness`. -/

theorem logDeriv_xi_conj (s : ℂ) :
    logDeriv xi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv xi s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xi_conj, xi_conj, ← map_div₀]

theorem logDeriv_xi_one_sub (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xi_one_sub, xi_one_sub, neg_div]

/-! ## The four folding identities -/

theorem re_logDeriv_xi_conj_line (a y : ℝ) :
    (logDeriv xi ((a : ℂ) - (y : ℂ) * I)).re = (logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re := by
  have hconj : ((a : ℂ) - (y : ℂ) * I) = (starRingEnd ℂ) ((a : ℂ) + (y : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [hconj, logDeriv_xi_conj]
  simp

theorem im_logDeriv_xi_conj_line (a y : ℝ) :
    (logDeriv xi ((a : ℂ) - (y : ℂ) * I)).im = -(logDeriv xi ((a : ℂ) + (y : ℂ) * I)).im := by
  have hconj : ((a : ℂ) - (y : ℂ) * I) = (starRingEnd ℂ) ((a : ℂ) + (y : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [hconj, logDeriv_xi_conj]
  simp

theorem re_logDeriv_xi_reflect_line (a y : ℝ) :
    (logDeriv xi (((1 - a : ℝ) : ℂ) + (y : ℂ) * I)).re
      = -(logDeriv xi ((a : ℂ) + (y : ℂ) * I)).re := by
  have hrw : (((1 - a : ℝ) : ℂ) + (y : ℂ) * I)
      = 1 - (starRingEnd ℂ) ((a : ℂ) + (y : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [hrw, logDeriv_xi_one_sub, logDeriv_xi_conj]
  simp

theorem im_logDeriv_xi_reflect_segment (x T : ℝ) :
    (logDeriv xi (((1 - x : ℝ) : ℂ) + (T : ℂ) * I)).im
      = (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im := by
  have hrw : (((1 - x : ℝ) : ℂ) + (T : ℂ) * I)
      = 1 - (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [hrw, logDeriv_xi_one_sub, logDeriv_xi_conj]
  simp

end RHTower
