/-
# Chen--Gupta--Li zero-density exponent consolidation

The final all-moduli display in Chen--Gupta--Li Theorem 1.2 consists of the
two source powers

`q^(7(1-σ)/3) T^(2(1-σ))` and `(qT)^(30(1-σ)/13)`.

For the corpus's literal positive natural conductor and height scales, this
module proves their closed algebraic consolidation into twice the uniform
`(qT)^(7(1-σ)/3)` envelope.  It is the exact exponent arithmetic used to
extract the advertised `7/3` coefficient once the analytic two-term estimate
is established; it does not assume or restate that analytic estimate.

No RH, GRH, zero-density, large-value, or asymptotic premise is supplied by a
caller.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace RHTower

noncomputable section

/-- A literal zero-density abscissa in the source critical-strip range. -/
structure CGLZeroDensityExponentPoint where
  value : ℝ
  half_lt : 1 / 2 < value
  lt_one : value < 1

/-- The nonnegative distance of a certified source abscissa from `1`. -/
def cglZeroDensityDefect (σ : CGLZeroDensityExponentPoint) : ℝ := 1 - σ.value

/-- The positive integral modulus scale used for a modulus indexed by `n`. -/
def cglZeroDensityModulusScale (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The positive integral height scale used for a height indexed by `T`. -/
def cglZeroDensityHeightScale (T : ℕ) : ℝ := (T : ℝ) + 1

/-- First displayed source power in the all-moduli Chen--Gupta--Li estimate. -/
def cglZeroDensityFirstTerm (σ : CGLZeroDensityExponentPoint) (n T : ℕ) : ℝ :=
  cglZeroDensityModulusScale n ^ ((7 / 3 : ℝ) * cglZeroDensityDefect σ) *
    cglZeroDensityHeightScale T ^ (2 * cglZeroDensityDefect σ)

/-- Second displayed source power in the all-moduli Chen--Gupta--Li estimate. -/
def cglZeroDensitySecondTerm (σ : CGLZeroDensityExponentPoint) (n T : ℕ) : ℝ :=
  (cglZeroDensityModulusScale n * cglZeroDensityHeightScale T) ^
    ((30 / 13 : ℝ) * cglZeroDensityDefect σ)

/-- Uniform `7/3` source envelope at the literal positive scales. -/
def cglZeroDensitySevenThirdsEnvelope
    (σ : CGLZeroDensityExponentPoint) (n T : ℕ) : ℝ :=
  (cglZeroDensityModulusScale n * cglZeroDensityHeightScale T) ^
    ((7 / 3 : ℝ) * cglZeroDensityDefect σ)

/-- Every certified source abscissa has nonnegative defect. -/
theorem cglZeroDensityDefect_nonneg (σ : CGLZeroDensityExponentPoint) :
    0 ≤ cglZeroDensityDefect σ := by
  unfold cglZeroDensityDefect
  linarith [σ.lt_one]

/-- The literal conductor scale is at least one. -/
theorem one_le_cglZeroDensityModulusScale (n : ℕ) :
    1 ≤ cglZeroDensityModulusScale n := by
  unfold cglZeroDensityModulusScale
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  linarith

/-- The literal height scale is at least one. -/
theorem one_le_cglZeroDensityHeightScale (T : ℕ) :
    1 ≤ cglZeroDensityHeightScale T := by
  unfold cglZeroDensityHeightScale
  have hT : (0 : ℝ) ≤ (T : ℝ) := by positivity
  linarith

/-- The `q^(7(1-σ)/3) T^(2(1-σ))` source term is bounded by the uniform
`(qT)^(7(1-σ)/3)` envelope. -/
theorem cglZeroDensityFirstTerm_le_sevenThirdsEnvelope
    (σ : CGLZeroDensityExponentPoint) (n T : ℕ) :
    cglZeroDensityFirstTerm σ n T ≤ cglZeroDensitySevenThirdsEnvelope σ n T := by
  have hδ : 0 ≤ cglZeroDensityDefect σ := cglZeroDensityDefect_nonneg σ
  have hQ : 0 ≤ cglZeroDensityModulusScale n :=
    (one_le_cglZeroDensityModulusScale n).trans' zero_le_one
  have hT : 0 ≤ cglZeroDensityHeightScale T :=
    (one_le_cglZeroDensityHeightScale T).trans' zero_le_one
  have hsmall : cglZeroDensityHeightScale T ^ (2 * cglZeroDensityDefect σ) ≤
      cglZeroDensityHeightScale T ^ ((7 / 3 : ℝ) * cglZeroDensityDefect σ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_cglZeroDensityHeightScale T) (by nlinarith)
  unfold cglZeroDensityFirstTerm cglZeroDensitySevenThirdsEnvelope
  calc
    cglZeroDensityModulusScale n ^ ((7 / 3 : ℝ) * cglZeroDensityDefect σ) *
        cglZeroDensityHeightScale T ^ (2 * cglZeroDensityDefect σ) ≤
      cglZeroDensityModulusScale n ^ ((7 / 3 : ℝ) * cglZeroDensityDefect σ) *
        cglZeroDensityHeightScale T ^ ((7 / 3 : ℝ) * cglZeroDensityDefect σ) := by
        exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hQ _)
    _ = (cglZeroDensityModulusScale n * cglZeroDensityHeightScale T) ^
        ((7 / 3 : ℝ) * cglZeroDensityDefect σ) := by
        rw [Real.mul_rpow hQ hT]

/-- The `(qT)^(30(1-σ)/13)` source term is bounded by the uniform
`(qT)^(7(1-σ)/3)` envelope. -/
theorem cglZeroDensitySecondTerm_le_sevenThirdsEnvelope
    (σ : CGLZeroDensityExponentPoint) (n T : ℕ) :
    cglZeroDensitySecondTerm σ n T ≤ cglZeroDensitySevenThirdsEnvelope σ n T := by
  have hδ : 0 ≤ cglZeroDensityDefect σ := cglZeroDensityDefect_nonneg σ
  have hQT : 1 ≤ cglZeroDensityModulusScale n * cglZeroDensityHeightScale T := by
    nlinarith [one_le_cglZeroDensityModulusScale n,
      one_le_cglZeroDensityHeightScale T]
  unfold cglZeroDensitySecondTerm cglZeroDensitySevenThirdsEnvelope
  exact Real.rpow_le_rpow_of_exponent_le hQT (by nlinarith)

/-- The two displayed all-moduli source powers are bounded by twice the
uniform Chen--Gupta--Li `7/3` envelope. -/
theorem cglZeroDensityTwoTerm_le_two_mul_sevenThirdsEnvelope
    (σ : CGLZeroDensityExponentPoint) (n T : ℕ) :
    cglZeroDensityFirstTerm σ n T + cglZeroDensitySecondTerm σ n T ≤
      2 * cglZeroDensitySevenThirdsEnvelope σ n T := by
  nlinarith [cglZeroDensityFirstTerm_le_sevenThirdsEnvelope σ n T,
    cglZeroDensitySecondTerm_le_sevenThirdsEnvelope σ n T]

end

end RHTower
