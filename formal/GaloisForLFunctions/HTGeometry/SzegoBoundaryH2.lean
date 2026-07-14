import GaloisForLFunctions.HTGeometry.SzegoH2
import GaloisForLFunctions.HTGeometry.RieszBrothersRieszFischer

/-!
# The reciprocal outer function as a boundary `L²` function

`gutzmer_tsum_le` shows the Taylor coefficients `bₖ` of `1/D` are square-summable.  This module
packages that as membership in `ℓ²` and realises the sequence as an honest `L²(circleLebesgue)`
boundary function `G = circleRieszFischerOfNat b`, whose analytic monomial partial sums converge to
it in `L²`.  This `G` is the boundary value of `1/D` — the multiplier that turns the reversed Taylor
polynomials of `D(0)/D` into a Szegő-extremal approximating family.
-/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- **Fourier coefficients of the Riesz–Fischer reconstruction.**  The `k`-th Fourier coefficient of
`circleRieszFischerOfNat c` is `cₖ` for `k ≥ 0` and `0` for `k < 0` — i.e. the zero-extended input
sequence. -/
theorem fourierCoeff_circleRieszFischerOfNat (c : ℕ → ℂ) (hc : Memℓp c 2) (k : ℤ) :
    fourierCoeff (↑↑(circleLpAddCircleLinearIsometryEquiv (circleRieszFischerOfNat c hc))) k
      = nonnegativeIntExtension c k := by
  rw [circleRieszFischerOfNat, LinearIsometryEquiv.apply_symm_apply, ← fourierBasis_repr,
    LinearIsometryEquiv.apply_symm_apply]

/-- **The analytic monomial partial sums converge to the boundary function.**  For a square-summable
`c`, the sums `∑_{k<N} cₖ zᵏ` converge in `L²(circleLebesgue)` to `circleRieszFischerOfNat c`.  This
is `Sₙ → G` in `L²`, the `H²`-convergence of the reciprocal outer function's Taylor partial sums to
its boundary value. -/
theorem hasSum_circleMonomial_smul_circleRieszFischerOfNat (c : ℕ → ℂ) (hc : Memℓp c 2) :
    HasSum (fun n : ℕ => c n • circleMonomialLp circleLebesgue n)
      (circleRieszFischerOfNat c hc) := by
  have hf : ∀ n : ℤ, n < 0 →
      fourierCoeff (↑↑(circleLpAddCircleLinearIsometryEquiv (circleRieszFischerOfNat c hc))) n = 0 :=
    fun n hn => by
      rw [fourierCoeff_circleRieszFischerOfNat, nonnegativeIntExtension, if_neg (not_le.mpr hn)]
  have heq : (fun n : ℕ => c n • circleMonomialLp circleLebesgue n)
      = fun n : ℕ => fourierCoeff
          (↑↑(circleLpAddCircleLinearIsometryEquiv (circleRieszFischerOfNat c hc))) (n : ℤ)
        • circleMonomialLp circleLebesgue n := by
    funext n
    rw [fourierCoeff_circleRieszFischerOfNat, nonnegativeIntExtension_ofNat]
  rw [heq]
  exact analyticPoly_hasSum_of_hardy hf

/-- **The reciprocal outer coefficients lie in `ℓ²`.**  For a weight bounded below by `c > 0`, the
Taylor coefficients of `1/D` are square-summable, so they realise a genuine boundary `L²` function
via Riesz–Fischer.  This is `1/D ∈ H²` in the form the reconstruction consumes. -/
theorem memℓp_coeff_inv_szegoOuter {w : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlog : IntervalIntegrable (fun θ => Real.log (w θ)) volume 0 (2 * π))
    (hper : Function.Periodic (fun θ => Real.log (w θ)) (2 * π))
    (hlogφ : ∀ φ, IntervalIntegrable (fun t => Real.log (w (φ + t))) volume (-π) π)
    (hwc : ∀ θ, c ≤ w θ)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1) :
    Memℓp (fun k => (cauchyPowerSeries (fun z => (szegoOuter w z)⁻¹) 0 R₀).coeff k) 2 := by
  apply memℓp_gen
  simpa using summable_of_sum_range_le (fun n => sq_nonneg _)
    (fun n => gutzmer_tsum_le hc hlog hper hlogφ hwc hR₀0 hR₀1 n)

end GaloisForLFunctions.HTGeometry
