import GaloisForLFunctions.RHTower.XiMeromorphicCauchyPairReflectionCorrectionNoGo
import GaloisForLFunctions.RHTower.CCM.CCMUnitaryPolarSourceAtlas

/-!
# Centered spectral EGC shifted-pole correction

The two shifted residues of the EGC rational Cauchy pair are one rational
correction.  EGC uses the rotated spectral coordinate
`xiSpectralPoint = (rho - 1/2) * (-I)`: a critical Xi copy is therefore real,
not vertical.  At centered spectral observation `w = 0`, the corpus's sharp
`|t| > 4` critical-ordinate bound makes every correction at `0 < eps ≤ 1`
strictly negative.

Thus no nonempty finite critical copy cluster can internally cancel that
centered, small-shift correction.  This is deliberately local in the
observation variable: it neither controls noncentered outer observations nor
proves a cofinal contour limit or RH.  Those are the remaining EGC hard gates.
-/

noncomputable section

open Complex Finset
open scoped BigOperators

namespace RHTower

/-- The two EGC shifted residues combine to one even rational correction. -/
theorem meromorphicCauchyPairShiftResidueCorrection_eq_negative_square_div
    (eps : ℝ) (w rho : ℂ)
    (hminus : rho - w - (eps : ℂ) ≠ 0)
    (hplus : rho - w + (eps : ℂ) ≠ 0) :
    meromorphicCauchyPairShiftResidueCorrection eps w rho =
      -((eps : ℂ) ^ (2 : ℕ)) / ((rho - w) ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ)) := by
  have hden : (rho - w) ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  unfold meromorphicCauchyPairShiftResidueCorrection
  field_simp [hminus, hplus, hden]
  ring

/-- At centered spectral observation, one actual critical Xi copy contributes
the displayed negative rational correction for every allowed EGC small shift. -/
theorem meromorphicCauchyPairShiftResidueCorrection_critical_centered_eq_negative
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (q : XiCriticalZeroCopy) :
    meromorphicCauchyPairShiftResidueCorrection eps 0 (xiSpectralPoint q.1) =
      ((-(eps ^ (2 : ℕ) / (xiCriticalOrdinate q ^ (2 : ℕ) - eps ^ (2 : ℕ))) : ℝ) : ℂ) := by
  have ht4 : 4 < |xiCriticalOrdinate q| := four_lt_abs_xiCriticalOrdinate q
  have htSq : 16 < xiCriticalOrdinate q ^ (2 : ℕ) := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|xiCriticalOrdinate q| - 4)]
  have hepsSq : eps ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg heps.le (sub_nonneg.mpr heps1)]
  have hdenpos : 0 < xiCriticalOrdinate q ^ (2 : ℕ) - eps ^ (2 : ℕ) := by
    nlinarith
  have hden : xiCriticalOrdinate q ^ (2 : ℕ) - eps ^ (2 : ℕ) ≠ 0 := ne_of_gt hdenpos
  rw [xiSpectralPoint_eq_of_critical q]
  have hminus :
      (xiCriticalOrdinate q : ℂ) - 0 - (eps : ℂ) ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    have hordinate : xiCriticalOrdinate q = eps := by linarith
    rw [hordinate] at hden
    exact hden (by ring)
  have hplus :
      (xiCriticalOrdinate q : ℂ) - 0 + (eps : ℂ) ≠ 0 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
    have hordinate : xiCriticalOrdinate q = -eps := by linarith
    rw [hordinate] at hden
    exact hden (by ring)
  rw [meromorphicCauchyPairShiftResidueCorrection_eq_negative_square_div
    eps 0 (xiCriticalOrdinate q : ℂ) hminus hplus]
  have hkernel :
      (((xiCriticalOrdinate q : ℂ) - 0) ^ (2 : ℕ) - (eps : ℂ) ^ (2 : ℕ)) =
        ((xiCriticalOrdinate q ^ (2 : ℕ) - eps ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hkernel]
  norm_cast
  ring

/-- The actual centered critical correction has strictly negative real part.
Hence critical copies cannot internally supply the zero outer correction at
this observation and scale. -/
theorem meromorphicCauchyPairShiftResidueCorrection_critical_centered_re_neg
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (q : XiCriticalZeroCopy) :
    (meromorphicCauchyPairShiftResidueCorrection eps 0 (xiSpectralPoint q.1)).re < 0 := by
  rw [meromorphicCauchyPairShiftResidueCorrection_critical_centered_eq_negative
    heps heps1 q]
  norm_cast
  apply neg_lt_zero.mpr
  apply div_pos (sq_pos_of_pos heps)
  have ht4 : 4 < |xiCriticalOrdinate q| := four_lt_abs_xiCriticalOrdinate q
  have htSq : 16 < xiCriticalOrdinate q ^ (2 : ℕ) := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|xiCriticalOrdinate q| - 4)]
  have hepsSq : eps ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg heps.le (sub_nonneg.mpr heps1)]
  nlinarith

/-- Every nonempty finite cluster of actual critical Xi copies has a strictly
negative centered small-shift correction. -/
theorem sum_meromorphicCauchyPairShiftResidueCorrection_critical_centered_re_neg
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (S : Finset XiCriticalZeroCopy) (hS : S.Nonempty) :
    (∑ q ∈ S,
      meromorphicCauchyPairShiftResidueCorrection eps 0 (xiSpectralPoint q.1)).re < 0 := by
  rw [Complex.re_sum]
  exact Finset.sum_neg
    (fun q hq => meromorphicCauchyPairShiftResidueCorrection_critical_centered_re_neg
      heps heps1 q) hS

end RHTower
