import GaloisForLFunctions.RHTower.FrankensteinParacyclicGhostTwoSheetAnomaly
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature
import GaloisForLFunctions.RHTower.Deninger.DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo

/-!
# Reflected paracyclic anomaly product as a Gamma-six boundary curvature

For a zero `ρ` of `Ξ`, this module pairs the paracyclic anomaly coefficient of `ρ` with that of
its functional-equation reflection `1 - ρ` and identifies minus their product with the unit
opposite boundary curvature `K(a) = 2(cosh a - 1)` evaluated at `a = log n^{2 Re ρ - 1}`, times the
two nonzero leading source coefficients `c(ρ) c(1 - ρ)`. Since `K(a) = 0` only at `a = 0`, the
reflected curvature coefficient vanishes exactly on the critical line.

## Main results

- `frankensteinParacyclicReflectedCurvatureCoefficient_eq`: the reflected coefficient equals
  `K((2 Re ρ - 1) log n) · c(ρ) · c(1 - ρ)`.
- `frankensteinParacyclicReflectedCurvatureCoefficient_eq_zero_iff`: for `n ≥ 2` it vanishes iff
  `Re ρ = 1/2`.

## Hypotheses

Unconditional; the vanishing criterion assumes `2 ≤ n`.
-/

open Complex Matrix GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Reflected curvature coefficient: minus the product of the anomaly coefficients of `ρ` and of
its reflection `1 - ρ`. -/
def frankensteinParacyclicReflectedCurvatureCoefficient
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) : ℂ :=
  -frankensteinParacyclicAnomalyCoefficient n rho pe *
    frankensteinParacyclicAnomalyCoefficient n (xiZeroReflectEquiv rho) pe

/-- The reflected coefficient equals `K(log n^{2 Re ρ - 1}) · c(ρ) · c(1 - ρ)`, where
`K(a) = 2(cosh a - 1)` is the unit opposite boundary curvature. -/
theorem frankensteinParacyclicReflectedCurvatureCoefficient_eq
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    frankensteinParacyclicReflectedCurvatureCoefficient n rho pe =
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (deningerHalfDensityMateGain n (rho : ℂ))) : ℂ) *
        thetaInternalJetLeadingSourceCoefficient rho *
        thetaInternalJetLeadingSourceCoefficient (xiZeroReflectEquiv rho) := by
  rw [frankensteinParacyclicReflectedCurvatureCoefficient,
    frankensteinParacyclicAnomalyCoefficient_eq,
    frankensteinParacyclicAnomalyCoefficient_eq,
    xiZeroReflectEquiv_apply]
  have hgainref :
      deningerHalfDensityMateGain n (1 - (rho : ℂ)) =
        (deningerHalfDensityMateGain n (rho : ℂ))⁻¹ := by
    simpa [deningerHalfDensityMateGain] using
      (deningerHalfDensityMateGain_reflection n (star (rho : ℂ)))
  rw [hgainref,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
    sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
  have hg : 0 < deningerHalfDensityMateGain n (rho : ℂ) :=
    deningerHalfDensityMateGain_pos n (rho : ℂ)
  rw [Real.exp_log hg, Real.exp_neg, Real.exp_log hg]
  push_cast
  ring

/-- For `n ≥ 2`, the reflected curvature coefficient of `ρ` vanishes iff `Re ρ = 1/2`. -/
theorem frankensteinParacyclicReflectedCurvatureCoefficient_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (pe : Nat.Primes × ℕ) :
    frankensteinParacyclicReflectedCurvatureCoefficient n rho pe = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [frankensteinParacyclicReflectedCurvatureCoefficient_eq, mul_assoc]
  have hc :
      thetaInternalJetLeadingSourceCoefficient rho *
        thetaInternalJetLeadingSourceCoefficient (xiZeroReflectEquiv rho) ≠ 0 :=
    mul_ne_zero
      (thetaInternalJetLeadingSourceCoefficient_ne_zero rho)
      (thetaInternalJetLeadingSourceCoefficient_ne_zero (xiZeroReflectEquiv rho))
  constructor
  · intro h
    have hcurvC :
        (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (deningerHalfDensityMateGain n (rho : ℂ))) : ℂ) = 0 :=
      (mul_eq_zero.mp h).resolve_right hc
    have hcurvR :
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (deningerHalfDensityMateGain n (rho : ℂ))) = 0 := by
      exact_mod_cast hcurvC
    have hlog : Real.log (deningerHalfDensityMateGain n (rho : ℂ)) = 0 :=
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff _).1 hcurvR
    have hgpos : 0 < deningerHalfDensityMateGain n (rho : ℂ) :=
      deningerHalfDensityMateGain_pos n (rho : ℂ)
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
      calc
        deningerHalfDensityMateGain n (rho : ℂ) =
            Real.exp (Real.log (deningerHalfDensityMateGain n (rho : ℂ))) :=
          (Real.exp_log hgpos).symm
        _ = 1 := by rw [hlog, Real.exp_zero]
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).1 hgain
  · intro hline
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).2 hline
    rw [hgain, Real.log_one]
    norm_num [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

end

end RHTower
