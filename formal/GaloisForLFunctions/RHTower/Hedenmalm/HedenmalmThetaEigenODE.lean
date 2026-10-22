import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoEndedVolterraDefect

/-!
# The theta eigenfunction equation solved by the source-pointed inverses

With `D = -i d/dx` and `k` the theta cusp source, the Hedenmalm eigenfunction equation at spectral
parameter `alpha` is `(D + alpha) u = -k`.  Both one-sided source-pointed inverses solve it.

The causal one is the free mode times the left half-line profile of the source against that mode;
the profile differentiates to its integrand by the fundamental theorem of calculus, and the product
rule turns the exponential factor into the spectral term.  The anti-causal one differs from it by a
free mode, which the operator annihilates, so it solves the same equation.  The two coincide for
every `x` exactly at a zero of `XiC`, which is the eigenfunction condition.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section


/-- The Volterra profile: the theta source against the free mode, integrated up to `x`. -/
def hedenmalmVolterraProfile (α : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Iic x, thetaCuspFourierLaplaceIntegrand (-α) t

theorem continuous_thetaCuspFourierLaplaceIntegrand (w : ℂ) :
    Continuous (thetaCuspFourierLaplaceIntegrand w) := by
  have hk : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  unfold thetaCuspFourierLaplaceIntegrand
  fun_prop (disch := assumption)

theorem hedenmalmCausalVolterra_eq_profile (α : ℂ) (x : ℝ) :
    hedenmalmCausalVolterra α x =
      -I * Complex.exp (-I * α * (x : ℂ)) * hedenmalmVolterraProfile α x := by
  have hrw : (∫ t in Iic x, hedenmalmVolterraIntegrand α x t) =
      Complex.exp (-I * α * (x : ℂ)) * hedenmalmVolterraProfile α x := by
    rw [hedenmalmVolterraProfile, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Iic
      (fun t _ => hedenmalmVolterraIntegrand_eq α x t)
  rw [hedenmalmCausalVolterra, hrw]
  ring

/-- The Volterra profile differentiates to its integrand: the fundamental theorem of calculus for
the left half-line integral of the theta source against the free mode. -/
theorem hasDerivAt_hedenmalmVolterraProfile {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    HasDerivAt (hedenmalmVolterraProfile α) (thetaCuspFourierLaplaceIntegrand (-α) x) x := by
  have hneg : |(-α).im| < 1 := by rw [Complex.neg_im, abs_neg]; exact hα
  have hint : Integrable (thetaCuspFourierLaplaceIntegrand (-α)) :=
    integrable_thetaCuspFourierLaplaceIntegrand hneg
  have hcont : Continuous (thetaCuspFourierLaplaceIntegrand (-α)) :=
    continuous_thetaCuspFourierLaplaceIntegrand (-α)
  have heq : ∀ y : ℝ, hedenmalmVolterraProfile α y =
      hedenmalmVolterraProfile α x + ∫ t in x..y, thetaCuspFourierLaplaceIntegrand (-α) t := by
    intro y
    rw [hedenmalmVolterraProfile, hedenmalmVolterraProfile,
      ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
    ring
  have hbase : HasDerivAt (fun y => ∫ t in x..y, thetaCuspFourierLaplaceIntegrand (-α) t)
      (thetaCuspFourierLaplaceIntegrand (-α) x) x :=
    intervalIntegral.integral_hasDerivAt_right hint.intervalIntegrable
      (hcont.stronglyMeasurable.stronglyMeasurableAtFilter) hcont.continuousAt
  refine (hbase.const_add (hedenmalmVolterraProfile α x)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall heq

/-- **(17): the causal source-pointed inverse solves the Hedenmalm eigenfunction equation.** -/
theorem hasDerivAt_hedenmalmCausalVolterra {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    HasDerivAt (hedenmalmCausalVolterra α)
      (-I * α * hedenmalmCausalVolterra α x - I * (thetaCuspFullSource x : ℂ)) x := by
  have hE : HasDerivAt (fun y : ℝ => -I * Complex.exp (-I * α * (y : ℂ)))
      (-I * (-I * α) * Complex.exp (-I * α * (x : ℂ))) x := by
    have h0 : HasDerivAt (fun z : ℂ => -I * α * z) (-I * α) (x : ℂ) := by
      simpa using (hasDerivAt_id ((x : ℝ) : ℂ)).const_mul (-I * α)
    have h1 := (h0.cexp).const_mul (-I)
    have h2 := h1.comp_ofReal
    refine h2.congr_deriv ?_
    ring
  have hP := hasDerivAt_hedenmalmVolterraProfile hα x
  have hmul := hE.mul hP
  refine (hmul.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => hedenmalmCausalVolterra_eq_profile α y)
  rw [hedenmalmCausalVolterra_eq_profile α x, thetaCuspFourierLaplaceIntegrand]
  have hexp : Complex.exp (-I * α * (x : ℂ)) * Complex.exp (-I * -α * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have hz : -I * α * (x : ℂ) + -I * -α * (x : ℂ) = 0 := by ring
    rw [hz, Complex.exp_zero]
  linear_combination (-I * (thetaCuspFullSource x : ℂ)) * hexp


/-- The anti-causal source-pointed inverse solves the same equation: it differs from the causal one
by the free mode, which is annihilated by the operator. -/
theorem hasDerivAt_hedenmalmAntiCausalVolterra {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    HasDerivAt (hedenmalmAntiCausalVolterra α)
      (-I * α * hedenmalmAntiCausalVolterra α x - I * (thetaCuspFullSource x : ℂ)) x := by
  have hw : HasDerivAt (fun y : ℝ => -I * Complex.exp (-I * α * (y : ℂ)) * XiC α)
      (-I * α * (-I * Complex.exp (-I * α * (x : ℂ)) * XiC α)) x := by
    have h0 : HasDerivAt (fun z : ℂ => -I * α * z) (-I * α) (x : ℂ) := by
      simpa using (hasDerivAt_id ((x : ℝ) : ℂ)).const_mul (-I * α)
    have h1 := ((h0.cexp).const_mul (-I)).mul_const (XiC α)
    have h2 := h1.comp_ofReal
    refine h2.congr_deriv ?_
    ring
  have hsplit : ∀ y : ℝ, hedenmalmAntiCausalVolterra α y =
      hedenmalmCausalVolterra α y - -I * Complex.exp (-I * α * (y : ℂ)) * XiC α := by
    intro y
    have h := hedenmalmCausalVolterra_sub_antiCausal hα y
    linear_combination -h
  have hsub := (hasDerivAt_hedenmalmCausalVolterra hα x).sub hw
  refine (hsub.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall hsplit)
  rw [hsplit x]
  ring

/-- **(17) for the causal inverse.**  With `D = -i d/dx` the causal source-pointed inverse solves
`(D + alpha) u = -k`, the Hedenmalm theta eigenfunction equation at spectral parameter `alpha`. -/
theorem hedenmalmCausalVolterra_thetaEigen_ode {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    -I * deriv (hedenmalmCausalVolterra α) x + α * hedenmalmCausalVolterra α x =
      -(thetaCuspFullSource x : ℂ) := by
  rw [(hasDerivAt_hedenmalmCausalVolterra hα x).deriv]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (α * hedenmalmCausalVolterra α x + (thetaCuspFullSource x : ℂ)) * hI

/-- **(17) for the anti-causal inverse.** -/
theorem hedenmalmAntiCausalVolterra_thetaEigen_ode {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    -I * deriv (hedenmalmAntiCausalVolterra α) x + α * hedenmalmAntiCausalVolterra α x =
      -(thetaCuspFullSource x : ℂ) := by
  rw [(hasDerivAt_hedenmalmAntiCausalVolterra hα x).deriv]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (α * hedenmalmAntiCausalVolterra α x + (thetaCuspFullSource x : ℂ)) * hI

/-- At a zero of `XiC` the two source-pointed solutions coincide, so the theta eigenfunction
equation has a distinguished two-sided solution exactly at the Xi divisor. -/
theorem exists_unique_twoSided_thetaEigen_solution_iff {α : ℂ} (hα : |α.im| < 1) :
    (∀ x : ℝ, hedenmalmCausalVolterra α x = hedenmalmAntiCausalVolterra α x) ↔ XiC α = 0 :=
  hedenmalmCausalVolterra_eq_antiCausal_iff hα

end

end RHTower
