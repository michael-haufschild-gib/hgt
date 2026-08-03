import GaloisForLFunctions.RHTower.DeningerBurnolConormalRadialTopBoundaryComparison

/-!
# Ordinary-integer BV Green--Stokes radial comparison

The Wold/BV first-trace boundary at an ordinary integer `n` has normalized
conormal evaluation

`n⁻¹ * (1 - χ_n(s)⁻¹)`,

where `χ_n(s)` is the Deninger half-density mate gain.  Reflection changes
`χ` to `χ⁻¹`; therefore the reflected difference of the two
Green--Stokes evaluations is exactly `1/n` times the physical
Deninger--Burnol radial defect.

This identifies the exact chain-level descent obstruction.  It does not
assert that the physical conormal evaluation annihilates the boundary:
that statement is equivalent to the critical-line equation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Normalized physical conormal evaluation of the ordinary-integer BV
Green--Stokes boundary.  Operator-theoretically this is the evaluation of
`[S_n^*, Q S_n] = n⁻¹ Q - P_n Q`, divided by the nonzero value on `Q`. -/
def deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
    (n : ℕ) (s : ℂ) : ℝ :=
  ((n : ℝ))⁻¹ * (1 - (deningerHalfDensityMateGain n s)⁻¹)

/-- Critical reflection exchanges the physical conormal evaluation with the
opposite mate-gain branch. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_reflection
    (n : ℕ) (s : ℂ) :
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (1 - star s) =
      ((n : ℝ))⁻¹ * (1 - deningerHalfDensityMateGain n s) := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation,
    deningerHalfDensityMateGain_reflection]
  simp only [inv_inv]

/-- **Ordinary-integer BV Green--Stokes reflected-difference law.**
Multiplication by the ordinary index recovers the full Deninger radial mate
curvature. -/
theorem deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℝ) *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (1 - star s)) =
      deningerTensorSquareRadialMateCurvature n s := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation,
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_reflection,
    ← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature hn s]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgain0 : deningerHalfDensityMateGain n s ≠ 0 :=
    ne_of_gt (deningerHalfDensityMateGain_pos n s)
  field_simp [hn0, hgain0]
  <;> ring

/-- The actual multiplicity-exact Burnol conormal radial defect is the
reflected ordinary-integer BV Green--Stokes boundary evaluation. -/
theorem deningerBurnolActualConormalRadialReflectionDefect_eq_bvGreenStokes
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    deningerBurnolActualConormalRadialReflectionDefect n rho =
      (n : ℝ) *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (rho : ℂ) -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n
            (1 - star (rho : ℂ))) := by
  rw [deningerBurnolActualConormalRadialReflectionDefect_eq hn,
    deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
      (lt_of_lt_of_le Nat.zero_lt_two hn)]

/-- A physical conormal marginal kills the ordinary-integer BV
Green--Stokes boundary exactly on the critical line.  Thus replacing the
physical marginal by a cyclic source trace is the RH-bearing descent step,
not a formal consequence of commutatorhood. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s = 0 ↔
      s.re = 1 / 2 := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation]
  have hn0 : ((n : ℝ))⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn).ne')
  rw [mul_eq_zero, or_iff_right hn0, sub_eq_zero]
  have hgain := deningerHalfDensityMateGain_pos n s
  constructor
  · intro h
    have hgainOne : deningerHalfDensityMateGain n s = 1 := by
      have hinv := congrArg Inv.inv h
      simpa using hinv
    apply (deningerTensorSquareRadialMateCurvature_eq_zero_iff n s hn).mp
    rw [← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
      (lt_of_lt_of_le Nat.zero_lt_two hn), hgainOne]
    norm_num
  · intro h
    have hcurv :=
      (deningerTensorSquareRadialMateCurvature_eq_zero_iff n s hn).mpr h
    have hgainSub :=
      deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
        (lt_of_lt_of_le Nat.zero_lt_two hn) s
    rw [hcurv] at hgainSub
    have hgainPos := deningerHalfDensityMateGain_pos n s
    have hgainOne : deningerHalfDensityMateGain n s = 1 := by
      have hsq : deningerHalfDensityMateGain n s ^ 2 = 1 := by
        field_simp [ne_of_gt hgainPos] at hgainSub
        nlinarith
      nlinarith
    rw [hgainOne, inv_one]

end

end RHTower

