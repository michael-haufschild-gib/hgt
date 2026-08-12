import GaloisForLFunctions.RHTower.SourceHorizontalWoldResolventEdge
import GaloisForLFunctions.HTGeometry.PeriodRigidity

/-!
# No one-variable holomorphic realization of the horizontal Wold weight

The bounded Wold coefficient used by the weighted resolvent edge depends only on horizontal
displacement, hence only on the imaginary coordinate of the centered Xi spectral point.  This
module proves that no complex-differentiable function can realize that coefficient on all of
`ℂ`: invariance under every real translation supplies arbitrarily small nonzero periods, so period
rigidity forces constancy, while the Wold coefficient vanishes only at the horizon.

This closes the direct single-contour producer route.  Any source formula producing the weighted
edge observable must retain a reflected second variable (or equivalent operator-valued data)
rather than insert the coefficient as one holomorphic test function.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- A complex-differentiable function which factors through the imaginary coordinate is constant.
The proof deliberately passes through the corpus period-rigidity theorem: dyadic real periods
converge to zero and remain nonzero. -/
theorem differentiable_constant_of_eq_imaginaryProfile
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (g : ℝ → ℂ)
    (hfg : ∀ z, f z = g z.im) :
    ∀ x y, f x = f y := by
  let p : ℕ → ℂ := fun n => (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)
  have hp0 : Tendsto p atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    exact (Complex.continuous_ofReal.tendsto 0).comp hreal
  have hpne : ∀ n, p n ≠ 0 := by
    intro n
    have hreal : (1 / 2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    change (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) ≠ 0
    exact ofReal_ne_zero.mpr hreal
  have hperiod : ∀ n, Function.Periodic f (p n) := by
    intro n z
    rw [hfg (z + p n), hfg z]
    congr 1
    rw [Complex.add_im]
    change z.im + (((1 / 2 : ℝ) ^ n : ℝ) : ℂ).im = z.im
    rw [Complex.ofReal_im, add_zero]
  exact GaloisForLFunctions.differentiable_constant_of_small_periods
    f hf p hp0 hpne hperiod

/-- Bounded scalar normalization of the universal reflection-even Wold polar rate work. -/
def sourceHorizontalWoldNormalizedPolarRateWeight (u : ℝ) : ℝ :=
  sourceHorizontalWoldPrimeClockPolarRateWork u /
    (1 + sourceHorizontalWoldPrimeClockPolarRateWork u)

theorem sourceHorizontalWoldPrimeClockPolarRateWork_nonneg (u : ℝ) :
    0 ≤ sourceHorizontalWoldPrimeClockPolarRateWork u := by
  have hlower := sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower u
  have hbase : 0 ≤ Real.log 2 / 18 * u ^ 4 := by positivity
  linarith

@[simp] theorem sourceHorizontalWoldNormalizedPolarRateWeight_zero :
    sourceHorizontalWoldNormalizedPolarRateWeight 0 = 0 := by
  simp [sourceHorizontalWoldNormalizedPolarRateWeight,
    sourceHorizontalWoldPrimeClockPolarRateWork]

theorem sourceHorizontalWoldNormalizedPolarRateWeight_pos_of_ne_zero
    {u : ℝ} (hu : u ≠ 0) :
    0 < sourceHorizontalWoldNormalizedPolarRateWeight u := by
  have hlower := sourceHorizontalWoldPrimeClockPolarRateWork_quartic_lower u
  have hbase : 0 < Real.log 2 / 18 * u ^ 4 := by positivity
  have hwork : 0 < sourceHorizontalWoldPrimeClockPolarRateWork u := lt_of_lt_of_le hbase hlower
  rw [sourceHorizontalWoldNormalizedPolarRateWeight]
  exact div_pos hwork (by linarith)

/-- **Single-holomorphic-profile no-go.**  No entire one-variable factor realizes the normalized
Wold horizontal coefficient.  Values at `0` and `I` already contradict the constancy forced by
real-translation invariance. -/
theorem no_differentiable_sourceHorizontalWoldNormalizedPolarImaginaryProfile :
    ¬ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z, f z =
        (sourceHorizontalWoldNormalizedPolarRateWeight (-2 * z.im) : ℂ) := by
  rintro ⟨f, hf, hprofile⟩
  let g : ℝ → ℂ := fun y =>
    (sourceHorizontalWoldNormalizedPolarRateWeight (-2 * y) : ℂ)
  have hfactor : ∀ z, f z = g z.im := by
    intro z
    simpa [g] using hprofile z
  have hconstant := differentiable_constant_of_eq_imaginaryProfile f hf g hfactor
  have hzeroI := hconstant 0 Complex.I
  have hweightEq : sourceHorizontalWoldNormalizedPolarRateWeight 0 =
      sourceHorizontalWoldNormalizedPolarRateWeight (-2) := by
    have hre := congrArg Complex.re hzeroI
    simpa [hprofile] using hre
  have hpositive : 0 < sourceHorizontalWoldNormalizedPolarRateWeight (-2) :=
    sourceHorizontalWoldNormalizedPolarRateWeight_pos_of_ne_zero (by norm_num)
  rw [sourceHorizontalWoldNormalizedPolarRateWeight_zero] at hweightEq
  linarith

end

end RHTower
