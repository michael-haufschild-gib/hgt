/-
# The Xi relative resolvent is the completed prime--archimedean flux

The centered Xi coordinate is the static affine change `s = 1/2 + z I`.  Its logarithmic
derivative therefore converts the regulator-independent relative resolvent trace into the
already constructed completed flux `-ξ'/ξ`.  Inside the critical strip this gives the exact
continued-prime plus archimedean/boundary decomposition.  No evolution, zero ordering, or
operator spectrum is introduced.
-/
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition

open Complex Function

namespace RHTower

noncomputable section

/-- Logarithmic derivative under the fixed centered affine coordinate. -/
theorem logDeriv_XiC_eq_mul_I_logDeriv_xi (z : ℂ) :
    logDeriv XiC z = Complex.I * logDeriv xi (1 / 2 + z * Complex.I) := by
  have haff : HasDerivAt (fun w : ℂ => 1 / 2 + w * Complex.I) Complex.I z := by
    convert (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id (𝕜 := ℂ) (x := z)).mul_const Complex.I) using 1
    all_goals ring
  have hderiv : deriv XiC z =
      deriv xi (1 / 2 + z * Complex.I) * Complex.I := by
    exact (xi_differentiable.differentiableAt.hasDerivAt.comp z haff).deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv, XiC]
  ring

/-- The regulator-independent relative trace is exactly the centered completed flux. -/
theorem xiRelativeResolventTrace_eq_completedFlux {z : ℂ} (hz : XiC z ≠ 0) :
    xiRelativeResolventTrace z =
      -Complex.I * seamFluxCochain (1 / 2 + z * Complex.I) := by
  rw [← logDeriv_XiC_eq_relativeResolventTrace hz,
    logDeriv_XiC_eq_mul_I_logDeriv_xi, seamFluxCochain]
  ring

/-- In the open strip away from a zeta zero, the same relative trace is the exact continued
prime flux plus the archimedean/boundary correction. -/
theorem xiRelativeResolventTrace_eq_prime_add_archimedean
    {z : ℂ} (hz : XiC z ≠ 0)
    (hstrip : 0 < (1 / 2 + z * Complex.I).re ∧
      (1 / 2 + z * Complex.I).re < 1)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    xiRelativeResolventTrace z =
      -Complex.I * (infinitePrimeFlux (1 / 2 + z * Complex.I) -
        logDeriv archFactor (1 / 2 + z * Complex.I)) := by
  rw [xiRelativeResolventTrace_eq_completedFlux hz,
    seamFluxCochain_eq_infinitePrimeFlux_add_archimedean hstrip hzeta]

end

end RHTower
