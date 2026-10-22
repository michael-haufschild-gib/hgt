import GaloisForLFunctions.RHTower.Suzuki.SuzukiGlobalLocalCompoundBezoutianWeld

/-!
# Suzuki global-local scalar Pick universality

The compound global-local weld already identifies both its affine quotient and its division-free
Hermitian Bezoutian.  Composing those endpoints gives the full scalar Pick kernel of an arbitrary
local response minus Suzuki's centered global Xi multiplier.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Global-local scalar Pick universality law.** Away from only the explicit local and global
denominator divisors, the scalar Pick kernel of `Q/P - XiC'/(z² XiC)` is exactly the compound
denominator normalization of the signed local-minus-global Hermitian Bezoutian. -/
theorem suzukiXiGlobalLocalCompound_scalarPickKernel
    (Q P : ℂ → ℂ) {z w : ℂ}
    (hPz : P z ≠ 0) (hPw : P w ≠ 0)
    (hXiZ : suzukiXiDerivativePairDenominator z ≠ 0)
    (hXiW : suzukiXiDerivativePairDenominator w ≠ 0) :
    suzukiScalarPickKernel
        (fun u => Q u / P u - suzukiShiftedXiMultiplier 0 u) z w =
      (suzukiXiDerivativePairDenominator z *
            (starRingEnd ℂ) (suzukiXiDerivativePairDenominator w) *
            suzukiHermitianBezoutCross Q P z w -
          P z * (starRingEnd ℂ) (P w) *
            suzukiHermitianBezoutCross
              suzukiXiDerivativePairNumerator
              suzukiXiDerivativePairDenominator z w) /
        (suzukiXiGlobalLocalCompoundDenominator P z *
          (starRingEnd ℂ) (suzukiXiGlobalLocalCompoundDenominator P w) *
          (z - (starRingEnd ℂ) w)) := by
  have hDz : suzukiXiGlobalLocalCompoundDenominator P z ≠ 0 := by
    simpa [suzukiXiGlobalLocalCompoundDenominator,
      suzukiGlobalLocalCompoundDenominatorFn,
      suzukiGlobalLocalCompoundDenominator] using mul_ne_zero hPz hXiZ
  have hDw : suzukiXiGlobalLocalCompoundDenominator P w ≠ 0 := by
    simpa [suzukiXiGlobalLocalCompoundDenominator,
      suzukiGlobalLocalCompoundDenominatorFn,
      suzukiGlobalLocalCompoundDenominator] using mul_ne_zero hPw hXiW
  calc
    suzukiScalarPickKernel
        (fun u => Q u / P u - suzukiShiftedXiMultiplier 0 u) z w =
        suzukiScalarPickKernel
          (fun u => suzukiXiGlobalLocalCompoundNumerator Q P u /
            suzukiXiGlobalLocalCompoundDenominator P u) z w := by
      simp only [suzukiScalarPickKernel]
      rw [suzukiXiGlobalLocalCompound_quotient Q P hPz hXiZ,
        suzukiXiGlobalLocalCompound_quotient Q P hPw hXiW]
    _ = suzukiHermitianBezoutCross
          (suzukiXiGlobalLocalCompoundNumerator Q P)
          (suzukiXiGlobalLocalCompoundDenominator P) z w /
        (suzukiXiGlobalLocalCompoundDenominator P z *
          (starRingEnd ℂ) (suzukiXiGlobalLocalCompoundDenominator P w) *
          (z - (starRingEnd ℂ) w)) :=
      suzukiScalarPickKernel_quotient_eq_bezoutCross
        (suzukiXiGlobalLocalCompoundNumerator Q P)
        (suzukiXiGlobalLocalCompoundDenominator P) hDz hDw
    _ = _ := by
      rw [suzukiXiGlobalLocalCompound_bezoutCross]

end

end RHTower
