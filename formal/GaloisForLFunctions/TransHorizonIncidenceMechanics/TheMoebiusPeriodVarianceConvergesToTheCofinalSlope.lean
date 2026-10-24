import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusSlopeIsThePeriodVariance
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusResponseWhiteNoiseLaw
import GaloisForLFunctions.BezoutValuationIncidence.UniformCofinalMobiusPrefixDiscrepancy
import GaloisForLFunctions.BiScaleUncertainty.SignedLcmFractionalDefectAndCompleteFibreCollapse

/-!
# The Möbius period variance converges to the cofinal slope

The complete-period variance of the Möbius response, `Var_N(μ) = Cov_N(0; μ)`, has a limit, and
the limit is the slope `κ` of the cofinal Möbius profile (`tendsto_periodVariance_moebius`):

`lim_N Var_N(μ) = κ = lim_B P(B)/B`.

The Selberg diagonal of `μ` is the lcm form `C(N) = Σ_{d,e ≤ N} μ(d)μ(e)/[d,e]`, which tends to `κ`
(`tendsto_moebiusPeriodMeanSquare`); the harmonic mode `(Σ_{d ≤ N} μ(d)/d)²` vanishes. The white-noise
floor `Var_N(μ) ≥ 1/288` therefore passes to the slope: `κ ≥ 1/288`, so the cofinal profile grows
linearly with a positive rate. The Bézout form of `μ` is null as well, so the dissipation rate
`R_N(μ)` also tends to `κ`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The Selberg diagonal of the Möbius weight is its lcm form `C(N)`. -/
theorem selbergTotientDiagonalForm_moebiusReal (N : ℕ) :
    selbergTotientDiagonalForm N moebiusReal = moebiusPeriodMeanSquare N := by
  rw [← sum_div_lcm_eq_selbergTotientDiagonalForm, sum_product]
  rfl

/-- **The Möbius period variance converges**, to the cofinal slope: `Var_N(μ) → κ`. -/
theorem tendsto_periodVariance_moebius :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N moebiusReal 0) atTop
      (𝓝 cofinalMobiusSlope) := by
  have h := tendsto_moebiusPeriodMeanSquare.sub (tendsto_finiteHarmonicSum_moebiusReal_zero.pow 2)
  rw [zero_pow two_ne_zero, sub_zero] at h
  refine h.congr fun N => ?_
  rw [TwoLagSieve.periodCovariance_zero, ← selbergTotientDiagonalForm_moebiusReal,
    selberg_eq_harmonic_sq_add_variance]
  ring

/-- **The cofinal slope is positive**: `κ ≥ 1/288`. -/
theorem one_div_288_le_cofinalMobiusSlope : (1 : ℝ) / 288 ≤ cofinalMobiusSlope :=
  ge_of_tendsto tendsto_periodVariance_moebius eventually_periodCovariance_moebius_zero_ge

/-- **The Möbius dissipation rate converges** to the cofinal slope: `R_N(μ) → κ`. -/
theorem tendsto_sieveSuccessorReserve_moebius :
    Tendsto (fun N : ℕ => sieveSuccessorReserve N moebiusReal) atTop (𝓝 cofinalMobiusSlope) := by
  have h := tendsto_moebiusPeriodMeanSquare.sub tendsto_bezoutCoprimeQuadraticForm_moebius
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [sieveSuccessorReserve, selbergTotientDiagonalForm_moebiusReal]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
