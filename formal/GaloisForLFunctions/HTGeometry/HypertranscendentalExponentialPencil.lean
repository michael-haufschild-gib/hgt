import GaloisForLFunctions.HTGeometry.EntireExponentialCompositionDA
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.ReciprocalSubstitutionInjective
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Hypertranscendental exponential pencils

For an entire exponent `Q` and a nonzero constant `c`, the unit `exp (c Q)` is
differentially algebraic exactly when `Q` is.  The reverse implication is the
logarithmic-derivative argument needed by zero-free gauge constructions.
-/

open Set
open scoped Differential UnivMeroFieldInstances

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Differential algebraicity of an entire function is closed under differentiation. -/
theorem differentiallyAlgebraic_deriv_of_entire {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hDA : DifferentiallyAlgebraic f) :
    DifferentiallyAlgebraic (deriv f) := by
  apply differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hf.deriv
  rw [← deriv_analyticMeroElement f hf]
  exact differentialAlgebraicOver_deriv
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf hDA)

/-- For a nonzero scalar, exponentiation preserves and reflects differential algebraicity of an
entire exponent. -/
theorem differentiallyAlgebraic_cexp_const_mul_iff {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraic (fun z => Complex.exp (c * Q z)) ↔
      DifferentiallyAlgebraic Q := by
  let P : ℂ → ℂ := fun z => c * Q z
  have hP : AnalyticOnNhd ℂ P Set.univ := analyticOnNhd_const.mul hQ
  constructor
  · intro hExp
    have hExpAn : AnalyticOnNhd ℂ (fun z => Complex.exp (P z)) Set.univ := hP.cexp
    have hDerivExp : DifferentiallyAlgebraic (deriv fun z => Complex.exp (P z)) :=
      differentiallyAlgebraic_deriv_of_entire hExpAn hExp
    have hInvExp : DifferentiallyAlgebraic (fun z => (Complex.exp (P z))⁻¹) :=
      differentiallyAlgebraic_inv hExpAn (fun z => Complex.exp_ne_zero _) hExp
    have hLogDeriv : DifferentiallyAlgebraic
        (fun z => deriv (fun u => Complex.exp (P u)) z * (Complex.exp (P z))⁻¹) :=
      differentiallyAlgebraic_mul hExpAn.deriv
        (hExpAn.inv fun z _ => Complex.exp_ne_zero _) hDerivExp hInvExp
    have hEq :
        (fun z => deriv (fun u => Complex.exp (P u)) z * (Complex.exp (P z))⁻¹) =
          fun z => c * deriv Q z := by
      funext z
      have hPderiv : deriv P z = c * deriv Q z := by
        have hQz := (hQ z (Set.mem_univ z)).differentiableAt.hasDerivAt
        change deriv (fun u => c * Q u) z = c * deriv Q z
        exact (hQz.const_mul c).deriv
      have hExpDeriv : deriv (fun u => Complex.exp (P u)) z =
          Complex.exp (P z) * deriv P z :=
        ((hP z (Set.mem_univ z)).differentiableAt.hasDerivAt.cexp).deriv
      rw [hExpDeriv, hPderiv]
      field_simp
    rw [hEq] at hLogDeriv
    exact differentiallyAlgebraic_of_deriv
      ((differentiallyAlgebraic_const_mul_iff hc).mp hLogDeriv)
  · intro hDA
    exact differentiallyAlgebraic_cexp_comp hP (hDA.const_mul hc)

/-- Every nonzero member of the exponential pencil of an entire hypertranscendental exponent is
hypertranscendental. -/
theorem hypertranscendental_cexp_const_mul_iff {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) {c : ℂ} (hc : c ≠ 0) :
    Hypertranscendental (fun z => Complex.exp (c * Q z)) ↔
      Hypertranscendental Q := by
  exact not_congr (differentiallyAlgebraic_cexp_const_mul_iff hQ hc)

end

end GaloisForLFunctions.HTGeometry
