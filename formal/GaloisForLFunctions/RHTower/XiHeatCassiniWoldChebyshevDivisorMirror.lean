import GaloisForLFunctions.RHTower.CriticalChebyshevBoostChargeInjection

/-!
# Continuous-Chebyshev divisor mirror for the Route-T Wold pole

The shifted continuous-Chebyshev source supplies an apparent opposite charge for the first Wold
pole.  This file identifies that charge exactly: on the common safe half-plane it is the logarithmic
derivative of the complete zeta residue unit at the Wold shift.  Thus it carries the entire divisor
data already.  It is a valid singular counter-current, but not an independent source mechanism
from which a strict-right divisor exclusion could follow.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Shifted continuous-Chebyshev counter-current at the first Wold pole coordinate. -/
def chebyshevWoldDivisorMirror (s : ℂ) : ℂ :=
  -(s + 1 / 2)⁻¹ * criticalChebyshevBoostCurrent (s + 1 / 2)

/-- The apparent Chebyshev counter-current is exactly the complete regularized zeta divisor
current.  Hence it cannot provide an independent cancellation of a Wold divisor pole. -/
theorem chebyshevWoldDivisorMirror_eq_logDeriv
    {s : ℂ} (hs : 0 < s.re) :
    chebyshevWoldDivisorMirror s = logDeriv zetaResidueUnit (s + 1) := by
  have hhalf_re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hs0 : s + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    rw [Complex.add_re, hhalf_re]
    linarith
  rw [chebyshevWoldDivisorMirror, criticalChebyshevBoostCurrent]
  have harg : s + 1 / 2 + 1 / 2 = s + 1 := by ring
  rw [harg]
  calc
    -(s + 1 / 2)⁻¹ * (-(s + 1 / 2) * logDeriv zetaResidueUnit (s + 1)) =
        ((s + 1 / 2)⁻¹ * (s + 1 / 2)) * logDeriv zetaResidueUnit (s + 1) := by ring
    _ = logDeriv zetaResidueUnit (s + 1) := by rw [inv_mul_cancel₀ hs0, one_mul]

/-- On its literal convergence half-plane, the same counter-current is an affine transform of
the continuous-Chebyshev Laplace source. -/
theorem chebyshevWoldDivisorMirror_eq_source
    {s : ℂ} (hs : 0 < s.re) :
    chebyshevWoldDivisorMirror s =
      -((s + 1) * criticalNormalizedChebyshevErrorLaplace (s + 1 / 2) + 1) := by
  have hhalf_re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hs0 : s + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    rw [Complex.add_re, hhalf_re]
    linarith
  have hz : 1 / 2 < (s + 1 / 2).re := by
    rw [Complex.add_re, hhalf_re]
    linarith
  rw [chebyshevWoldDivisorMirror,
    criticalChebyshevBoostCurrent_eq_laplaceAffine hz]
  have harg : s + 1 / 2 + 1 / 2 = s + 1 := by ring
  rw [harg]
  calc
    -(s + 1 / 2)⁻¹ * ((s + 1 / 2) *
        ((s + 1) * criticalNormalizedChebyshevErrorLaplace (s + 1 / 2) + 1)) =
        -(((s + 1 / 2)⁻¹ * (s + 1 / 2)) *
          ((s + 1) * criticalNormalizedChebyshevErrorLaplace (s + 1 / 2) + 1)) := by ring
    _ = -((s + 1) * criticalNormalizedChebyshevErrorLaplace (s + 1 / 2) + 1) := by
      rw [inv_mul_cancel₀ hs0, one_mul]

end

end RHTower
