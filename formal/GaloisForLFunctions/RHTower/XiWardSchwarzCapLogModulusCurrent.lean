import GaloisForLFunctions.RHTower.XiWardSchwarzCapResonantQuadrature
import GaloisForLFunctions.RHTower.LogModulusHorizontal

/-!
# Log-modulus transport for the resonant Ward cap current

On every admissible lower cap line, the real component of the literal
completed prime--polar--Gamma source is a horizontal log-modulus derivative of
`XiC`.  Combined with the exact Schwarz-cap quadrature, this identifies the
moving resonant current with an explicit weighted divisor-potential current
plus its independent imaginary component.

This is an identity, not a bound: controlling the potential term cofinally is
the remaining analytic problem.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- On the conull family of actual zero-free lower cap lines, the real
completed source is exactly the horizontal derivative of the Xi log modulus. -/
theorem ae_forall_hasDerivAt_log_norm_XiC_lowerCap :
    ∀ᵐ s : ℝ ∂volume, ∀ x : ℝ,
      HasDerivAt
        (fun u : ℝ => Real.log ‖XiC (xiWardLowerCapPoint s u)‖)
        (continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re x := by
  filter_upwards [ae_forall_XiExplicitAdmissible_canonicalLowerCapLine] with s hs
  intro x
  have hadm := hs x
  have hXi : XiC (xiWardLowerCapPoint s x) ≠ 0 :=
    XiC_ne_zero_of_admissible hadm
  have hpath : HasDerivAt (fun u : ℝ => xiWardLowerCapPoint s u) 1 x := by
    unfold xiWardLowerCapPoint
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const
      ((xiWardTransverseLevel s : ℂ) * I)
  have hXiA := XiC_analytic (xiWardLowerCapPoint s x)
    (Set.mem_univ (xiWardLowerCapPoint s x))
  have hcomp : HasDerivAt
      (fun u : ℝ => XiC (xiWardLowerCapPoint s u))
      (deriv XiC (xiWardLowerCapPoint s x)) x := by
    change HasDerivAt (XiC ∘ xiWardLowerCapPoint s)
      (deriv XiC (xiWardLowerCapPoint s x)) x
    simpa using hXiA.differentiableAt.hasDerivAt.comp x hpath
  have hlog := hasDerivAt_log_norm_comp hcomp hXi
  have hsource :
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) =
        logDeriv XiC (xiWardLowerCapPoint s x) := by
    change continuedPrimeArchSourceRelativeTrace
        ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I) =
      logDeriv XiC ((x : ℂ) - (xiWardTransverseLevel s : ℂ) * I)
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hadm.re_pos hadm.ne_one hadm.zeta_ne]
    exact (logDeriv_XiC_eq_relativeResolventTrace hXi).symm
  rw [hsource]
  change HasDerivAt
    (fun u : ℝ => Real.log ‖XiC (xiWardLowerCapPoint s u)‖)
    (deriv XiC (xiWardLowerCapPoint s x) /
      XiC (xiWardLowerCapPoint s x)).re x
  exact hlog

/-- Exact resonant potential/imaginary decomposition of the literal
completed-source cap current on every admissible lower cap line. -/
theorem ae_forall_xiWardSchwarzCapFactorDensity_resonant_logModulus :
    ∀ᵐ s : ℝ ∂volume, ∀ x : ℝ,
      (xiWardSchwarzCapDifference x s x *
        continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).re =
        (-(8 * x ^ 2) /
          ((51 / 100 + xiWardTransverseLevel s) *
            ((51 / 100 + xiWardTransverseLevel s) ^ 2 + 4 * x ^ 2))) *
          deriv (fun u : ℝ => Real.log ‖XiC (xiWardLowerCapPoint s u)‖) x +
        ((4 * x) /
          ((51 / 100 + xiWardTransverseLevel s) ^ 2 + 4 * x ^ 2)) *
          (continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)).im := by
  filter_upwards [ae_forall_hasDerivAt_log_norm_XiC_lowerCap] with s hs
  intro x
  rw [xiWardSchwarzCapFactorDensity_resonant_re, ← (hs x).deriv]

end

end RHTower
