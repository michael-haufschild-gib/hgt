import GaloisForLFunctions.RHTower.PrimeVacuumExponentialIntegral
import GaloisForLFunctions.RHTower.EulerMascheroniGaussKernel
import GaloisForLFunctions.RHTower.EulerFisherPoincareBoundary
import GaloisForLFunctions.RHTower.ExponentialIntegralE1

/-!
# The pole vacuum cancels the pole of the Euler logarithm

At a real point of the physical half-plane the continuous prime vacuum is the exponential
integral at the shifted argument, so it carries exactly the logarithmic singularity
`-gamma - log(z-1)` of the pole; the canonical Euler logarithm carries the singularity
`-log(z-1)` with an analytic regular part.  Subtracting removes the logarithm identically: the
difference is an analytic regular part plus `gamma`, corrected by a quantity of size `O(z-1)`.

This is the chain-level realization of the pole cancellation in `(z-1) zeta(z)`.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## The vacuum at real points -/

theorem expIntegralOneC_ofReal {s : ℝ} (hs : 0 < s) :
    expIntegralOneC (s : ℂ) 1 = ((expIntegralOne s : ℝ) : ℂ) := by
  have hpt : ∀ u ∈ Ioi (1 : ℝ),
      Complex.exp (-(s : ℂ) * (u : ℂ)) / (u : ℂ) = ((Real.exp (-s * u) / u : ℝ) : ℂ) := by
    intro u _
    rw [Complex.ofReal_div, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [expIntegralOneC, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_complex_ofReal]
  congr 1
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun v : ℝ => Real.exp (-v) / v) 1 hs
  rw [mul_one] at hscale
  have hlhs : (∫ x in Ioi (1 : ℝ), Real.exp (-(s * x)) / (s * x))
      = s⁻¹ * ∫ x in Ioi (1 : ℝ), Real.exp (-s * x) / x := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have : Real.exp (-(s * x)) = Real.exp (-s * x) := by
      congr 1
      ring
    rw [this]
    field_simp
  rw [hlhs, smul_eq_mul] at hscale
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs
  rw [expIntegralOne]
  exact mul_left_cancel₀ (inv_ne_zero hsne) hscale

/-- **Card equation (20e).**  At a real point near the pole the vacuum is
`-gamma - log(z-1) + O(z-1)`. -/
theorem primeVacuumValue_ofReal {β : ℝ} (hβ : 1 < β) (hβ2 : β ≤ 2) :
    primeVacuumValue (β : ℂ)
      = ((-Real.eulerMascheroniConstant - Real.log (β - 1) + ein (β - 1) : ℝ) : ℂ) := by
  have hre : (1 : ℝ) < ((β : ℂ)).re := by simpa using hβ
  have hs : (0 : ℝ) < β - 1 := by linarith
  have hs1 : β - 1 ≤ 1 := by linarith
  have hcast : (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [primeVacuumValue_eq hre, hcast, expIntegralOneC_ofReal hs, expIntegralOne,
    integral_expNegDiv_Ioi_small hs hs1]
  congr 1
  ring

/-! ## The Euler logarithm at real points -/

/-- **Card equation (20f).**  The canonical Euler logarithm is `-log(z-1)` plus an analytic
regular part. -/
theorem canonicalEulerLogZeta_ofReal_eq {β : ℝ} (hβ : 1 < β) :
    canonicalEulerLogZeta (β : ℂ) = ((eulerLogRegular β - Real.log (β - 1) : ℝ) : ℂ) := by
  rw [canonicalEulerLogZeta_ofReal (β := β), eulerLogRegular_eq hβ]
  congr 1
  ring

/-! ## The cancellation -/

/-- **Card equation (20g).**  The logarithmic singularities cancel identically: the difference of
the canonical Euler logarithm and the continuous vacuum is an analytic regular part plus `gamma`,
corrected by a quantity of size `O(z-1)`. -/
theorem primePoleCancellation {β : ℝ} (hβ : 1 < β) (hβ2 : β ≤ 2) :
    canonicalEulerLogZeta (β : ℂ) - primeVacuumValue (β : ℂ)
      = ((eulerLogRegular β + Real.eulerMascheroniConstant - ein (β - 1) : ℝ) : ℂ) := by
  rw [canonicalEulerLogZeta_ofReal_eq hβ, primeVacuumValue_ofReal hβ hβ2, ← Complex.ofReal_sub]
  congr 1
  ring

/-- The pole has cancelled: the difference extends continuously to the pole. -/
theorem tendsto_primePoleCancellation :
    Tendsto (fun β : ℝ => canonicalEulerLogZeta (β : ℂ) - primeVacuumValue (β : ℂ))
      (𝓝[>] 1) (𝓝 (((eulerLogRegular 1 + Real.eulerMascheroniConstant : ℝ)) : ℂ)) := by
  have hreg : Tendsto eulerLogRegular (𝓝[>] 1) (𝓝 (eulerLogRegular 1)) :=
    (analyticAt_eulerLogRegular.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hein : Tendsto (fun β : ℝ => ein (β - 1)) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_ein_nhdsWithin_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun β : ℝ => β - 1) (𝓝 1) (𝓝 0) := by
        simpa using (continuous_id.sub continuous_const).tendsto (1 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact sub_pos.mpr (Set.mem_Ioi.mp hβ)
  have hcomb := ((hreg.add_const Real.eulerMascheroniConstant).sub hein)
  have hcast : Tendsto (fun β : ℝ =>
      ((eulerLogRegular β + Real.eulerMascheroniConstant - ein (β - 1) : ℝ) : ℂ))
      (𝓝[>] 1) (𝓝 (((eulerLogRegular 1 + Real.eulerMascheroniConstant - 0 : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hcomb
  rw [sub_zero] at hcast
  refine Tendsto.congr' ?_ hcast
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1:ℝ) < 2)] with β hβ
  exact (primePoleCancellation hβ.1 hβ.2.le).symm

end

end RHTower
