import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Polar-quarter obstruction to critical Thorin tilting

For an auxiliary completed-Xi source based at square radius `r`, the separated polar
factor is the Laplace transform of an exponential law with rate `r - 1/4`. Transport
back to the functional-equation center requires exponential tilt by `r`. This file
formalizes the sharp obstruction: an exponential density of rate `a` admits tilt
`θ` exactly when `θ < a`, whereas `r - 1/4 < r` for every aperture.

The theorem is source-route bookkeeping, not an RH proof. Its positive content is
that the polar and zeta-pole channels must be coupled before imposing a positive
Thorin decomposition; increasing the auxiliary aperture cannot repair a separated
polar atom.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exponential density of rate `rate`, multiplied by the exponential tilt `tilt`. -/
def thorinExponentialTiltKernel (rate tilt x : ℝ) : ℝ :=
  Real.exp (tilt * x) * (rate * Real.exp (-(rate * x)))

/-- A linear exponential on the positive half-line is integrable exactly when it decays. -/
theorem integrableOn_expLinear_Ioi_iff {c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (c * x)) (Ioi 0) ↔ c < 0 := by
  constructor
  · intro h
    by_contra! hc
    have hlin : ∫⁻ _ : ℝ in Ioi 0, 1 ≤
        ∫⁻ x : ℝ in Ioi 0, ‖Real.exp (c * x)‖₊ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
        Real.norm_of_nonneg (Real.exp_pos _).le, coe_nnnorm, Real.one_le_exp_iff]
      exact mul_nonneg hc hx.le
    simpa using hlin.trans_lt h.2
  · exact fun hc => integrableOn_exp_mul_Ioi hc 0

/-- Exact moment domain of an exponentially tilted exponential density. -/
theorem integrableOn_thorinExponentialTiltKernel_Ioi_iff
    {rate tilt : ℝ} (hrate : 0 < rate) :
    IntegrableOn (thorinExponentialTiltKernel rate tilt) (Ioi 0) ↔ tilt < rate := by
  have hfun : thorinExponentialTiltKernel rate tilt =
      fun x : ℝ => rate * Real.exp ((tilt - rate) * x) := by
    funext x
    rw [thorinExponentialTiltKernel]
    calc
      Real.exp (tilt * x) * (rate * Real.exp (-(rate * x))) =
          rate * (Real.exp (tilt * x) * Real.exp (-(rate * x))) := by ring
      _ = rate * Real.exp ((tilt - rate) * x) := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [hfun, IntegrableOn, integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr hrate.ne')]
  simpa only [sub_neg] using integrableOn_expLinear_Ioi_iff (c := tilt - rate)

/-- Rate of the separated completed polar factor at square aperture `r`. -/
def completedPolarRate (r : ℝ) : ℝ := r - 1 / 4

/-- The critical-center tilt exceeds the separated polar rate by exactly `1/4`. -/
theorem centerTilt_sub_completedPolarRate (r : ℝ) :
    r - completedPolarRate r = 1 / 4 := by
  rw [completedPolarRate]
  ring

/-- No aperture removes the strict polar deficit. -/
theorem completedPolarRate_lt_centerTilt (r : ℝ) : completedPolarRate r < r := by
  rw [completedPolarRate]
  norm_num

/-- **Polar-quarter tilt barrier.** The separated positive polar factor cannot be
exponentially tilted far enough to reach the functional-equation center. -/
theorem not_integrableOn_completedPolarCenterTilt
    {r : ℝ} (hr : 1 / 4 < r) :
    ¬ IntegrableOn
      (thorinExponentialTiltKernel (completedPolarRate r) r) (Ioi 0) := by
  unfold completedPolarRate
  rw [integrableOn_thorinExponentialTiltKernel_Ioi_iff (sub_pos.mpr hr)]
  linarith [completedPolarRate_lt_centerTilt r]

/-- At the unit auxiliary aperture, the raw polar atom has rate `3/4`. -/
theorem completedPolarRate_one : completedPolarRate 1 = 3 / 4 := by
  norm_num [completedPolarRate]

/-- The specific `Exp(3/4)` component cannot support the unit tilt used by critical
continuation. -/
theorem not_integrableOn_threeQuarterPolarUnitTilt :
    ¬ IntegrableOn (thorinExponentialTiltKernel (3 / 4) 1) (Ioi 0) := by
  simpa only [completedPolarRate_one] using
    not_integrableOn_completedPolarCenterTilt (r := 1) (by norm_num)

end

end RHTower
