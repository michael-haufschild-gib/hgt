import GaloisForLFunctions.RHTower.Sieve.HeathBrownFinitePacket
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The von Mangoldt self-convolution and the zeta source

On the half-plane of absolute convergence the Dirichlet series of `Λ * Λ`
is the square of the logarithmic derivative of the Riemann zeta function.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The actual Rankin–Selberg coefficient sequence `Λ * Λ` produces
`(ζ'/ζ)²` for `Re s > 1`. -/
theorem LSeries_vonMangoldtSelfConvolution_eq_logDeriv_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (((ArithmeticFunction.vonMangoldt *
      ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ)) s =
      (logDeriv riemannZeta s) ^ 2 := by
  have hcoeff : RHTower.Sieve.complexCoeff ArithmeticFunction.vonMangoldt =
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    exact RHTower.Sieve.complexCoeff_apply _ _
  have hcoeffsq : RHTower.Sieve.complexCoeff
      (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) =
      (fun n => (((ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ)) := by
    funext n
    exact RHTower.Sieve.complexCoeff_apply _ _
  have hsum : LSeriesSummable
      (RHTower.Sieve.complexCoeff ArithmeticFunction.vonMangoldt) s := by
    rw [hcoeff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hmul := RHTower.Sieve.LSeries_complexCoeff_mul
    (F := ArithmeticFunction.vonMangoldt) (G := ArithmeticFunction.vonMangoldt) hsum hsum
  rw [hcoeffsq, hcoeff] at hmul
  calc
    _ = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
      exact hmul
    _ = _ := by
      rw [RHTower.logDeriv_riemannZeta_eq_neg_LSeries hs]
      ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
