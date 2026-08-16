import GaloisForLFunctions.RHTower.HeatEnergyExpand

/-!
# Real moments of the heat multiplier

At a real exponent the window moment is the cast of a nonnegative real integral, so its norm is
that integral.  This is what converts the pointwise error bound of the Jonquière expansion into a
bound by moments.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The window moment at a real exponent, as a real number. -/
noncomputable def realHeatMoment (x lam : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in Ioc (-Real.pi) Real.pi, |θ| ^ lam * heatMultiplierValue x θ

theorem heatMoment_ofReal_exponent {x : ℝ} (hx : 0 < x) (lam : ℝ) :
    heatMoment x ((lam : ℝ) : ℂ) = ((realHeatMoment x lam : ℝ) : ℂ) := by
  rw [heatMoment, realHeatMoment, Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · push_cast
    ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [Complex.ofReal_mul, heatMultiplier_eq_value hx, Complex.ofReal_cpow (abs_nonneg θ)]

theorem realHeatMoment_nonneg {x : ℝ} (hx : 0 < x) (lam : ℝ) : 0 ≤ realHeatMoment x lam := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg fun θ => ?_
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg θ) _) (heatMultiplierValue_nonneg hx θ)

theorem norm_heatMoment_ofReal {x : ℝ} (hx : 0 < x) (lam : ℝ) :
    ‖heatMoment x ((lam : ℝ) : ℂ)‖ = realHeatMoment x lam := by
  rw [heatMoment_ofReal_exponent hx, Complex.norm_real,
    Real.norm_of_nonneg (realHeatMoment_nonneg hx lam)]

/-- **The real moments vanish in the small-aperture limit.** -/
theorem tendsto_realHeatMoment {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun x : ℝ => realHeatMoment x lam) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hre : ((lam : ℝ) : ℂ).re = lam := by simp
  have hc := tendsto_heatMoment_of_pos_re (lam := ((lam : ℝ) : ℂ)) (by rw [hre]; exact hlam)
  rw [tendsto_zero_iff_norm_tendsto_zero] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact norm_heatMoment_ofReal hx lam

end RHTower
