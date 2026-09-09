import GaloisForLFunctions.HTGeometry.FokasLenellsRawFirstCoefficient

/-!
# The first spectral slope of the actual solution on the entire line

The exact divided integral equation controls its slope uniformly in position.
Dominated convergence evaluates that slope at zero as an explicit anchored
Schwartz primitive. These are the inputs for successive exact Taylor
remainders and for passage to both infinite scattering endpoints.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawSolutionSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  ∫ s in (0 : ℝ)..x, rawDividedDerivative q k v s

theorem continuous_rawSolutionSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawSolutionSlope q k v) := (rawDividedDerivative_integrable q k v).continuous_primitive 0

/-- Exact first divided equation, defined also at zero frequency. -/
theorem rawInteractionSolution_first_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k v x = v+(k : ℂ) • rawSolutionSlope q k v x := by
  have hh := rawInteractionSolution_equation q k v x
  change rawInteractionSolution q k v x = v+∫ s in (0 : ℝ)..x, rawInteractionDerivative q k v s at hh
  simp_rw [rawInteractionDerivative_factor,intervalIntegral.integral_smul] at hh
  exact hh

/-- The divided solution has a uniform whole-line bound, independent of the anchor distance. -/
theorem rawSolutionSlope_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawSolutionSlope q k v x‖ ≤ ‖v‖*Real.exp (|k| * rawInteractionMass q)*rawInteractionMass q := by
  have h1 : ‖rawSolutionSlope q k v x‖ ≤ ∫ s : ℝ, ‖rawDividedDerivative q k v s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral (rawDividedDerivative_integrable q k v).norm
        (Eventually.of_forall fun s => norm_nonneg (rawDividedDerivative q k v s)))
  have h2 := integral_mono (rawDividedDerivative_integrable q k v).norm
    ((rawInteractionDensity_integrable q).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q)))
    (rawDividedDerivative_bound q k v)
  exact h1.trans (by simpa only [integral_const_mul,rawInteractionMass] using h2)

/-- The actual divided solution converges through zero, for every spatial position. -/
theorem rawSolutionSlope_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawSolutionSlope q k v x) (𝓝 0) (𝓝 (rawSolutionSlope q 0 v x)) := by
  have hb := (rawInteractionDensity_integrable q).const_mul (‖v‖*Real.exp (rawInteractionMass q))
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => (‖v‖*Real.exp (rawInteractionMass q))*rawInteractionDensity q s)
    (Eventually.of_forall fun k => (rawDividedDerivative_integrable q k v).aestronglyMeasurable.restrict)
    ?_ hb.intervalIntegrable ?_
  · filter_upwards [hk] with k hk
    apply Eventually.of_forall
    intro s _
    have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (rawInteractionMass_nonneg q)
    exact (rawDividedDerivative_bound q k v s).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v))
        (rawInteractionDensity_nonneg q s))
  · apply Eventually.of_forall
    intro s _
    simpa only [rawDividedDerivative,rawInteractionSolution_zero_frequency] using rawDividedDerivative_tendsto_zero q v s

def rawLinearCoefficient (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawLinearPrimitive q v x-rawLinearPrimitive q v 0

/-- The first coefficient is the exact anchored primitive of the zero-frequency Lax kernel. -/
theorem rawSolutionSlope_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawSolutionSlope q 0 v x = rawLinearCoefficient q v x := by
  have hd : ∀ s : ℝ, HasDerivAt (rawLinearPrimitive q v) (rawDividedDerivative q 0 v s) s := by
    intro s
    simpa only [rawDividedDerivative,rawInteractionSolution_zero_frequency] using rawLinearPrimitive_hasDerivAt q v s
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (rawDividedDerivative_integrable q 0 v).intervalIntegrable

theorem rawLinearCoefficient_bound (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    ‖rawLinearCoefficient q v x‖ ≤ ‖v‖*rawInteractionMass q := by
  have hh := rawSolutionSlope_bound q 0 v x
  simpa only [rawSolutionSlope_zero,abs_zero,zero_mul,Real.exp_zero,mul_one] using hh

/-- An evaluated genuine derivative of the original flow, with all initial-data assumptions discharged. -/
theorem rawInteractionSolution_first_derivative (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (fun k : ℝ => rawInteractionSolution q k v x) (rawLinearCoefficient q v x) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hh : Tendsto (fun k => rawSolutionSlope q k v x) (𝓝[≠] (0 : ℝ)) (𝓝 (rawLinearCoefficient q v x)) := by
    simpa only [rawSolutionSlope_zero] using (rawSolutionSlope_tendsto_zero q v x).mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk0 : k ≠ 0 := hk
  simp only [zero_add,rawInteractionSolution_zero_frequency]
  rw [rawInteractionSolution_first_factor,add_sub_cancel_left]
  change rawSolutionSlope q k v x = k⁻¹ • (k • rawSolutionSlope q k v x)
  rw [smul_smul,inv_mul_cancel₀ hk0,one_smul]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
