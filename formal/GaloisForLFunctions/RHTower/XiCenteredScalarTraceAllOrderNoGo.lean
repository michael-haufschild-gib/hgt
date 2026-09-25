import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# All centered scalar trace signs do not detect an off-axis zero

The even Schwarz-real polynomial `(1-z²)(1+z²/4)` has both real and nonreal
zeros. Its reciprocal-square roots are `1` and `-1/4`; every scalar power sum
`1+(-1/4)^n` is strictly positive for `n≥1`. The first shifted two-by-two
Hankel minor is nevertheless negative. Thus extending a centered reciprocal
trace sign to *every individual order* cannot by itself replace the shifted
Hankel/general-packet condition. This is an abstract countermodel, not a
perturbation of the literal Xi source.
-/

open Complex

noncomputable section

namespace RHTower

def scalarTraceBlindEvenPolynomial (z : ℂ) : ℂ :=
  (1 - z ^ 2) * (1 + z ^ 2 / 4)

def scalarTraceBlindReciprocalMoment (n : ℕ) : ℝ :=
  1 + (-1 / 4 : ℝ) ^ n

theorem scalarTraceBlindEvenPolynomial_even (z : ℂ) :
    scalarTraceBlindEvenPolynomial (-z) = scalarTraceBlindEvenPolynomial z := by
  simp [scalarTraceBlindEvenPolynomial]

theorem scalarTraceBlindEvenPolynomial_schwarz (z : ℂ) :
    star (scalarTraceBlindEvenPolynomial (star z)) =
      scalarTraceBlindEvenPolynomial z := by
  simp [scalarTraceBlindEvenPolynomial]

theorem scalarTraceBlindEvenPolynomial_offAxisZero :
    scalarTraceBlindEvenPolynomial (2 * I) = 0 := by
  have h : ((2 : ℂ) * I) ^ 2 = -4 := by
    calc
      ((2 : ℂ) * I) ^ 2 = 4 * I ^ 2 := by ring
      _ = -4 := by norm_num
  simp [scalarTraceBlindEvenPolynomial, h]

theorem scalarTraceBlindEvenPolynomial_offAxisZero_im_pos :
    0 < (2 * I : ℂ).im := by
  norm_num

theorem scalarTraceBlindReciprocalMoment_pos (n : ℕ) :
    0 < scalarTraceBlindReciprocalMoment (n + 1) := by
  have hpow : (1 / 4 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have habs : |(-1 / 4 : ℝ) ^ (n + 1)| ≤ 1 / 4 := by
    rw [abs_pow, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num, pow_succ]
    nlinarith
  have hleft := neg_abs_le ((-1 / 4 : ℝ) ^ (n + 1))
  dsimp [scalarTraceBlindReciprocalMoment]
  linarith

theorem scalarTraceBlind_shiftedHankelMinor_eq :
    scalarTraceBlindReciprocalMoment 1 * scalarTraceBlindReciprocalMoment 3 -
      scalarTraceBlindReciprocalMoment 2 ^ 2 = -(25 / 64 : ℝ) := by
  norm_num [scalarTraceBlindReciprocalMoment]

theorem scalarTraceBlind_shiftedHankelMinor_neg :
    scalarTraceBlindReciprocalMoment 1 * scalarTraceBlindReciprocalMoment 3 -
      scalarTraceBlindReciprocalMoment 2 ^ 2 < 0 := by
  rw [scalarTraceBlind_shiftedHankelMinor_eq]
  norm_num

end RHTower

end
