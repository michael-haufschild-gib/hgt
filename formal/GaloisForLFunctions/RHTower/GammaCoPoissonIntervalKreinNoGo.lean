import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Gamma/co-Poisson interval cell is intrinsically Krein

The exact factorial/co-Poisson interval cell is not a positive kernel, even
on two real characters.  For every positive logarithmic action `L` and every
positive displacement `d`, the symmetric packet at `1/2 ± d` has:

* an explicit vector with strictly negative quadratic value;
* a strictly negative `2 × 2` determinant.

Thus no exact incidence-preserving Hilbert Gram factorization can be assembled
action by action.  Any positive common-test realization must first couple
different logarithmic actions with the Gamma/boundary channel.
-/

open Complex

namespace RHTower

noncomputable section

/-- Quadratic value of the symmetric two-character packet with coefficients
`1` and `-exp (dL)`. -/
def gammaCoPoissonSymmetricPacketValue (L d : ℝ) : ℂ :=
  let z : ℂ := ((1 / 2 + d : ℝ) : ℂ)
  let w : ℂ := ((1 / 2 - d : ℝ) : ℂ)
  let c : ℂ := Complex.exp ((d * L : ℝ) : ℂ)
  gammaCoPoissonIntervalCell (L : ℂ) z z -
    c * gammaCoPoissonIntervalCell (L : ℂ) z w -
    c * gammaCoPoissonIntervalCell (L : ℂ) w z +
    c ^ 2 * gammaCoPoissonIntervalCell (L : ℂ) w w

/-- The off-diagonal symmetric interval cell is the hyperbolic sine quotient. -/
theorem gammaCoPoissonIntervalCell_symmetric_off
    {L d : ℝ} (hd : d ≠ 0) :
    gammaCoPoissonIntervalCell (L : ℂ)
        (((1 / 2 + d : ℝ) : ℂ)) (((1 / 2 - d : ℝ) : ℂ)) =
      ((Real.sinh (d * L) / d : ℝ) : ℂ) := by
  rw [gammaCoPoissonIntervalCell_eq_dividedDifference]
  · have hplus :
        ((((1 / 2 + d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
          ((d * L : ℝ) : ℂ) := by
      push_cast
      ring
    have hminus :
        ((((1 / 2 - d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
          ((-(d * L) : ℝ) : ℂ) := by
      push_cast
      ring
    have hden :
        (((1 / 2 + d : ℝ) : ℂ) - ((1 / 2 - d : ℝ) : ℂ)) =
          ((2 * d : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hplus, hminus, hden]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
    norm_cast
    rw [Real.sinh_eq]
    field_simp [hd]
  · have hreal : (1 / 2 + d : ℝ) ≠ 1 / 2 - d := by
      intro h
      apply hd
      linarith
    exact_mod_cast hreal

/-- Symmetry of the real off-diagonal interval cell. -/
theorem gammaCoPoissonIntervalCell_symmetric_off_swap
    {L d : ℝ} (hd : d ≠ 0) :
    gammaCoPoissonIntervalCell (L : ℂ)
        (((1 / 2 - d : ℝ) : ℂ)) (((1 / 2 + d : ℝ) : ℂ)) =
      ((Real.sinh (d * L) / d : ℝ) : ℂ) := by
  rw [gammaCoPoissonIntervalCell_eq_dividedDifference]
  · have hplus :
        ((((1 / 2 + d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
          ((d * L : ℝ) : ℂ) := by
      push_cast
      ring
    have hminus :
        ((((1 / 2 - d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
          ((-(d * L) : ℝ) : ℂ) := by
      push_cast
      ring
    have hden :
        (((1 / 2 - d : ℝ) : ℂ) - ((1 / 2 + d : ℝ) : ℂ)) =
          ((-(2 * d) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hminus, hplus, hden]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
    norm_cast
    rw [Real.sinh_eq]
    field_simp [hd]
    ring
  · have hreal : (1 / 2 - d : ℝ) ≠ 1 / 2 + d := by
      intro h
      apply hd
      linarith
    exact_mod_cast hreal

/-- Closed form of the negative symmetric-packet quadratic value. -/
theorem gammaCoPoissonSymmetricPacketValue_eq
    {L d : ℝ} (hd : d ≠ 0) :
    gammaCoPoissonSymmetricPacketValue L d =
      ((2 * Real.exp (d * L) *
        (L - Real.sinh (d * L) / d) : ℝ) : ℂ) := by
  rw [gammaCoPoissonSymmetricPacketValue]
  rw [gammaCoPoissonIntervalCell_self,
    gammaCoPoissonIntervalCell_self,
    gammaCoPoissonIntervalCell_symmetric_off hd,
    gammaCoPoissonIntervalCell_symmetric_off_swap hd]
  have hplus :
      ((((1 / 2 + d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
        ((d * L : ℝ) : ℂ) := by
    push_cast
    ring
  have hminus :
      ((((1 / 2 - d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
        ((-(d * L) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hplus, hminus]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- Every nontrivial positive logarithmic interval has a strictly negative
two-character quadratic direction. -/
theorem gammaCoPoissonSymmetricPacketValue_re_neg
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    (gammaCoPoissonSymmetricPacketValue L d).re < 0 := by
  rw [gammaCoPoissonSymmetricPacketValue_eq hd.ne']
  simp only [ofReal_re]
  have hu : 0 < d * L := mul_pos hd hL
  have hsinh : d * L < Real.sinh (d * L) :=
    Real.self_lt_sinh_iff.mpr hu
  have hdiv : L < Real.sinh (d * L) / d := by
    exact (lt_div_iff₀ hd).2 (by simpa [mul_comm] using hsinh)
  have hneg : L - Real.sinh (d * L) / d < 0 := sub_neg.mpr hdiv
  exact mul_neg_of_pos_of_neg
    (mul_pos (by norm_num) (Real.exp_pos _)) hneg

/-- Determinant of the interval-cell matrix at the symmetric real characters
`1/2 ± d`. -/
def gammaCoPoissonSymmetricPacketDeterminant (L d : ℝ) : ℂ :=
  let z : ℂ := ((1 / 2 + d : ℝ) : ℂ)
  let w : ℂ := ((1 / 2 - d : ℝ) : ℂ)
  gammaCoPoissonIntervalCell (L : ℂ) z z *
      gammaCoPoissonIntervalCell (L : ℂ) w w -
    gammaCoPoissonIntervalCell (L : ℂ) z w *
      gammaCoPoissonIntervalCell (L : ℂ) w z

/-- Exact determinant formula for the symmetric interval-cell matrix. -/
theorem gammaCoPoissonSymmetricPacketDeterminant_eq
    {L d : ℝ} (hd : d ≠ 0) :
    gammaCoPoissonSymmetricPacketDeterminant L d =
      ((L ^ 2 - (Real.sinh (d * L) / d) ^ 2 : ℝ) : ℂ) := by
  rw [gammaCoPoissonSymmetricPacketDeterminant]
  rw [gammaCoPoissonIntervalCell_self,
    gammaCoPoissonIntervalCell_self,
    gammaCoPoissonIntervalCell_symmetric_off hd,
    gammaCoPoissonIntervalCell_symmetric_off_swap hd]
  have hplus :
      ((((1 / 2 + d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
        ((d * L : ℝ) : ℂ) := by
    push_cast
    ring
  have hminus :
      ((((1 / 2 - d : ℝ) : ℂ) - 1 / 2) * (L : ℂ)) =
        ((-(d * L) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hplus, hminus, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- The symmetric `2 × 2` interval-cell determinant is strictly negative.
Therefore the exact interval cell is not a positive-semidefinite kernel. -/
theorem gammaCoPoissonSymmetricPacketDeterminant_re_neg
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    (gammaCoPoissonSymmetricPacketDeterminant L d).re < 0 := by
  rw [gammaCoPoissonSymmetricPacketDeterminant_eq hd.ne']
  simp only [ofReal_re]
  have hu : 0 < d * L := mul_pos hd hL
  have hsinh : d * L < Real.sinh (d * L) :=
    Real.self_lt_sinh_iff.mpr hu
  have hdiv : L < Real.sinh (d * L) / d := by
    exact (lt_div_iff₀ hd).2 (by simpa [mul_comm] using hsinh)
  have hL0 : 0 ≤ L := hL.le
  have hdiv0 : 0 ≤ Real.sinh (d * L) / d := by positivity
  nlinarith

end

end RHTower
