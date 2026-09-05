import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaWeierstrassTrace
import Mathlib.Tactic

/-!
# Second derivative of the pole-free Weierstrass trace

The first-order cubic in equation (72) of arXiv:2607.21750 can be differentiated everywhere on
the half-period-shifted trace.  This module builds the actual second derivative from mathlib's
analytic Weierstrass function and proves the differentiated cubic globally.  The result deliberately
retains the factor `y'`: cancelling it would lose validity at half-period critical points and would
require a separate analytic-continuation argument.
-/

open PeriodPair

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def halfShiftWeierstrassSecond (L : PeriodPair) (x : ℝ) : ℂ :=
  L.ω₁ ^ 2 * deriv L.derivWeierstrassP (halfShiftArgument L x)

/-- The pole-free trace has a certified second real derivative at every point. -/
theorem hasDerivAt_halfShiftWeierstrassPrime (L : PeriodPair) (x : ℝ) :
    HasDerivAt (halfShiftWeierstrassPrime L) (halfShiftWeierstrassSecond L x) x := by
  have houter : HasDerivAt L.derivWeierstrassP
      (deriv L.derivWeierstrassP (halfShiftArgument L x))
      (halfShiftArgument L x) :=
    (L.analyticOnNhd_derivWeierstrassP _
      (halfShiftArgument_not_mem_lattice L x)).differentiableAt.hasDerivAt
  have hpath : HasDerivAt (halfShiftArgument L) L.ω₁ x := by
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ) * L.ω₁) L.ω₁ x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const L.ω₁
    exact hbase.add_const (L.ω₂ / 2)
  have h := (houter.scomp x hpath).const_mul L.ω₁
  apply h.congr_deriv
  rw [halfShiftWeierstrassSecond]
  simp only [smul_eq_mul]
  ring

/-- Derivative of paper equation (72), valid even where the first derivative vanishes. -/
theorem halfShiftWeierstrass_differentiated_equation (L : PeriodPair) (x : ℝ) :
    2 * halfShiftWeierstrassPrime L x * halfShiftWeierstrassSecond L x =
      L.ω₁ ^ 2 *
        ((12 * halfShiftWeierstrass L x ^ 2 - L.g₂) *
          halfShiftWeierstrassPrime L x) := by
  have hy := hasDerivAt_halfShiftWeierstrass L x
  have hyp := hasDerivAt_halfShiftWeierstrassPrime L x
  have hcubic : HasDerivAt
      (fun z : ℝ => L.ω₁ ^ 2 *
        (4 * halfShiftWeierstrass L z ^ 3 -
          L.g₂ * halfShiftWeierstrass L z - L.g₃))
      (L.ω₁ ^ 2 *
        ((12 * halfShiftWeierstrass L x ^ 2 - L.g₂) *
          halfShiftWeierstrassPrime L x)) x := by
    have h := (((hy.pow 3).const_mul 4).sub (hy.const_mul L.g₂) |>.sub_const L.g₃
      |>.const_mul (L.ω₁ ^ 2))
    apply h.congr_deriv
    ring
  have hsquare : HasDerivAt (fun z : ℝ => halfShiftWeierstrassPrime L z ^ 2)
      (2 * halfShiftWeierstrassPrime L x * halfShiftWeierstrassSecond L x) x := by
    apply (hyp.pow 2).congr_deriv
    ring
  have hevent :
      (fun z : ℝ => halfShiftWeierstrassPrime L z ^ 2) =ᶠ[nhds x]
        (fun z : ℝ => L.ω₁ ^ 2 *
          (4 * halfShiftWeierstrass L z ^ 3 -
            L.g₂ * halfShiftWeierstrass L z - L.g₃)) :=
    Filter.Eventually.of_forall (halfShiftWeierstrass_equation L)
  exact (hsquare.congr_of_eventuallyEq hevent.symm).unique hcubic

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
