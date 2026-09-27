import GaloisForLFunctions.RHTower.CCMPolarFourierGram
import GaloisForLFunctions.RHTower.CCMActualHeadExteriorGaugeCoerciveCompactReduction

/-!
# A correlation bound for the negative part of the complete arithmetic source

The negative part is taken only after adding Gamma, both poles, and every active
prime atom. Its measure is finite by the proved growth of the Gamma symbol.
The two-pole constrained Fourier Gram gives an independent lower bound for
the whole source, uniformly over its full form domain. No sign of the
resulting scalar lower bound is assumed or asserted.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct FourierTransform
noncomputable section
namespace RHTower

/-- The complete actual symbol, retaining Gamma, every active prime power, and both poles. -/
def ccmActualWeilSymbol (a : SuzukiPositiveAperture) (ξ : ℝ) : ℝ :=
  correctedCCMSymbol a.1 (2 * Real.pi * ξ)

theorem continuous_ccmActualWeilSymbol (a : SuzukiPositiveAperture) :
    Continuous (ccmActualWeilSymbol a) :=
  (continuous_correctedCCMSymbol a.1).comp (continuous_const.mul continuous_id)

/-- An arbitrary fixed level lies below the complete symbol outside a finite interval. -/
theorem exists_ccmActualWeilSymbol_tail_floor (a : SuzukiPositiveAperture) (α : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ ξ : ℝ, R ≤ |ξ| → α ≤ ccmActualWeilSymbol a ξ := by
  have htop : Tendsto (ccmActualWeilSymbol a) atTop atTop :=
    (tendsto_correctedCCMSymbol_atTop a.1).comp
      (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
  obtain ⟨r,hr⟩ := eventually_atTop.mp (htop.eventually (eventually_ge_atTop α))
  refine ⟨max 0 r, le_max_left _ _, fun ξ hξ => ?_⟩
  have h := hr |ξ| ((le_max_right 0 r).trans hξ)
  rcases le_total 0 ξ with hξ0 | hξ0
  · rwa [abs_of_nonneg hξ0] at h
  · simpa only [abs_of_nonpos hξ0, ccmActualWeilSymbol, mul_neg,
      correctedCCMSymbol_even] using h

/-- Only the negative part relative to the chosen level is charged as debt. -/
def ccmActualSourceNegativeWeight (a : SuzukiPositiveAperture) (α ξ : ℝ) : ℝ :=
  max 0 (α - ccmActualWeilSymbol a ξ)

theorem continuous_ccmActualSourceNegativeWeight (a : SuzukiPositiveAperture) (α : ℝ) :
    Continuous (ccmActualSourceNegativeWeight a α) :=
  continuous_const.max (continuous_const.sub (continuous_ccmActualWeilSymbol a))

theorem hasCompactSupport_ccmActualSourceNegativeWeight
    (a : SuzukiPositiveAperture) (α : ℝ) :
    HasCompactSupport (ccmActualSourceNegativeWeight a α) := by
  obtain ⟨R,hR,htail⟩ := exists_ccmActualWeilSymbol_tail_floor a α
  apply (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro ξ hξ
  by_contra hnot
  have hRξ : R ≤ |ξ| := by
    by_contra h
    exact hnot (abs_le.mp (le_of_lt (lt_of_not_ge h)))
  have hz : ccmActualSourceNegativeWeight a α ξ = 0 :=
    max_eq_left (sub_nonpos.mpr (htail ξ hRξ))
  exact hξ hz

theorem integrable_ccmActualSourceNegativeWeight (a : SuzukiPositiveAperture) (α : ℝ) :
    Integrable (ccmActualSourceNegativeWeight a α) :=
  (continuous_ccmActualSourceNegativeWeight a α).integrable_of_hasCompactSupport
    (hasCompactSupport_ccmActualSourceNegativeWeight a α)

/-- This measure contains the signed Gamma/prime cancellation before taking a positive part. -/
def ccmActualSourceNegativeMeasure (a : SuzukiPositiveAperture) (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun ξ => ENNReal.ofReal (ccmActualSourceNegativeWeight a α ξ))

instance ccmActualSourceNegativeMeasure_finite (a : SuzukiPositiveAperture) (α : ℝ) :
    IsFiniteMeasure (ccmActualSourceNegativeMeasure a α) :=
  isFiniteMeasure_withDensity_ofReal (integrable_ccmActualSourceNegativeWeight a α).hasFiniteIntegral

private theorem negative_measure_integral (a : SuzukiPositiveAperture) (α : ℝ) (g : ℝ → ℝ) :
    (∫ ξ, g ξ ∂ccmActualSourceNegativeMeasure a α) =
      ∫ ξ, ccmActualSourceNegativeWeight a α ξ * g ξ := by
  rw [ccmActualSourceNegativeMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_ccmActualSourceNegativeWeight a α).measurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_left 0 _), smul_eq_mul,
    ccmActualSourceNegativeWeight]

private theorem actual_symbol_integrable (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ => ccmActualWeilSymbol a ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
  apply (integrable_correctedCCMSymbol_mul_actualHeadDensity a u).congr
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hξ
  rw [hξ]
  rfl

/-- The full arithmetic source retains its polar term before the negative part is taken. -/
theorem ccmRestrictedWeilSource_eq_actualSymbol (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a u =
      ∫ ξ, ccmActualWeilSymbol a ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [← ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic]
  unfold ccmActualHeadCoherentCompletedGammaProducer
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hξ
  change correctedCCMSymbol a.1 (2 * Real.pi * ξ) *
    ‖ccmArchimedeanWeightedToL2 u.1 ξ‖ ^ 2 = _
  rw [hξ]
  rfl

/-- A scalar independent of the source and of every coefficient-space dimension. -/
def ccmActualSourceGramCeiling (a : SuzukiPositiveAperture) (α : ℝ) : ℝ :=
  Real.sqrt (ccmPolarFourierGramEnergy a (ccmActualSourceNegativeMeasure a α))

theorem ccmActualSourceGramCeiling_nonneg (a : SuzukiPositiveAperture) (α : ℝ) :
    0 ≤ ccmActualSourceGramCeiling a α := Real.sqrt_nonneg _

/-- The complete signed source has a source-independent lower bound retaining frequency correlations. -/
theorem ccmRestrictedWeilSource_ge_actualGram (a : SuzukiPositiveAperture)
    (α : ℝ) (u : ccmPolarConstraintSubmodule a) :
    (α - ccmActualSourceGramCeiling a α) * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.1 := by
  let f := ccmArchimedeanFormToAperture a u.1
  let φ : ℝ → ℝ := fun ξ => ‖(u.1.1 : ℝ → ℂ) ξ‖ ^ 2
  have hφ : Integrable φ := integrable_norm_sq_ccmFormDomain a u.1
  have hM := actual_symbol_integrable a u.1
  have hD : Integrable (fun ξ => ccmActualSourceNegativeWeight a α ξ * φ ξ) := by
    have h := ((hφ.const_mul α).sub hM).sup
      (by simp : Integrable (0 : ℝ → ℝ) volume)
    apply h.congr
    filter_upwards with ξ
    change max (α * φ ξ - ccmActualWeilSymbol a ξ * φ ξ) 0 = _
    rw [ccmActualSourceNegativeWeight, max_mul_of_nonneg _ _ (sq_nonneg _), zero_mul]
    dsimp only [φ]
    rw [sub_mul, max_comm]
  have hlow : α * ‖f‖ ^ 2 -
      (∫ ξ, ccmActualSourceNegativeWeight a α ξ * φ ξ) ≤
        ccmRestrictedWeilSourceQuadratic a u.1 := by
    have h := integral_mono ((hφ.const_mul α).sub hD) hM (fun ξ => ?_)
    · dsimp only [Pi.sub_apply] at h
      rw [integral_sub (hφ.const_mul α) hD, integral_const_mul,
        integral_norm_sq_ccmFormDomain, ← ccmRestrictedWeilSource_eq_actualSymbol] at h
      exact h
    · dsimp only [Pi.sub_apply, φ]
      have h := le_max_right 0 (α - ccmActualWeilSymbol a ξ)
      have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖(u.1.1 : ℝ → ℂ) ξ‖)
      dsimp only [ccmActualSourceNegativeWeight]
      nlinarith only [hm]
  have hdebt := ccmPolarFourier_debt_le_gram a (ccmActualSourceNegativeMeasure a α) u
  rw [negative_measure_integral] at hdebt
  have hsame : (∫ ξ, ccmActualSourceNegativeWeight a α ξ *
      ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2) =
      ∫ ξ, ccmActualSourceNegativeWeight a α ξ * φ ξ := by
    apply integral_congr_ae
    filter_upwards [ccmFormDomain_ae_eq_fourier a u.1] with ξ hξ
    dsimp only [φ, f]
    rw [hξ]
  rw [hsame] at hdebt
  change _ ≤ ccmActualSourceGramCeiling a α * ‖f‖ ^ 2 at hdebt
  change (α - ccmActualSourceGramCeiling a α) * ‖f‖ ^ 2 ≤ _
  nlinarith only [hlow,hdebt]

/-- The ground-energy lower bound controls the entire constrained form domain at each aperture. -/
theorem ccmRestrictedWeilPolarGround_ge_actualGram (a : SuzukiPositiveAperture) (α : ℝ) :
    α - ccmActualSourceGramCeiling a α ≤ ccmRestrictedWeilPolarGroundEnergy a := by
  apply le_ccmRestrictedWeilPolarGroundEnergy_of_floor
  intro u hu
  exact ccmRestrictedWeilSource_ge_actualGram a α ⟨u,hu⟩

/-- Comparison with the old diagonal trace estimate, after complete arithmetic cancellation. -/
theorem ccmActualSourceGramCeiling_le_trace (a : SuzukiPositiveAperture) (α : ℝ) :
    ccmActualSourceGramCeiling a α ≤
      ∫ ξ, ccmActualSourceNegativeWeight a α ξ * ‖ccmPolarPlaneWave a ξ‖ ^ 2 := by
  have h := ccmPolarFourier_gram_le_trace a (ccmActualSourceNegativeMeasure a α)
  rw [negative_measure_integral] at h
  exact h

/-- Diagonal mass of the actual negative-frequency measure after both pole constraints. -/
def ccmActualSourceNegativeTrace (a : SuzukiPositiveAperture) (α : ℝ) : ℝ :=
  ∫ ξ, ‖ccmPolarPlaneWave a ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α

/-- The integrated two-frequency Gram determinant of the actual source. -/
def ccmActualSourceGramCurvature (a : SuzukiPositiveAperture) (α : ℝ) : ℝ :=
  HTGeometry.continuousFrameGramDefect (ccmActualSourceNegativeMeasure a α)
    (ccmPolarPlaneWaveFrame a)

theorem ccmActualSourceGramCurvature_nonneg (a : SuzukiPositiveAperture) (α : ℝ) :
    0 ≤ ccmActualSourceGramCurvature a α :=
  HTGeometry.continuousFrameGramDefect_nonneg _ _

/-- The curvature supplies an exact nonnegative discount from squared diagonal trace. -/
theorem ccmActualSourceGramCeiling_sq_add_curvature (a : SuzukiPositiveAperture) (α : ℝ) :
    ccmActualSourceGramCeiling a α ^ 2 + ccmActualSourceGramCurvature a α =
      ccmActualSourceNegativeTrace a α ^ 2 := by
  rw [ccmActualSourceGramCeiling,
    Real.sq_sqrt (ccmPolarFourierGramEnergy_nonneg a _)]
  exact HTGeometry.continuousFrame_gram_add_defect _ (ccmPolarPlaneWaveFrame a)

/-- A quantitative curvature improvement of the old diagonal trace, including its zero-mass case. -/
theorem ccmActualSourceGramCeiling_le_trace_sub_curvature
    (a : SuzukiPositiveAperture) (α : ℝ) :
    ccmActualSourceGramCeiling a α ≤ ccmActualSourceNegativeTrace a α -
      ccmActualSourceGramCurvature a α / (2 * ccmActualSourceNegativeTrace a α) := by
  let T := ccmActualSourceNegativeTrace a α
  let C := ccmActualSourceGramCeiling a α
  let D := ccmActualSourceGramCurvature a α
  have hT : 0 ≤ T := integral_nonneg fun _ => sq_nonneg _
  have hC : 0 ≤ C := ccmActualSourceGramCeiling_nonneg a α
  have he : C^2 + D = T^2 := ccmActualSourceGramCeiling_sq_add_curvature a α
  have hCT : C ≤ T := ccmPolarFourier_gram_le_trace a _
  change C ≤ T - D/(2*T)
  by_cases hz : T = 0
  · simp only [hz, mul_zero, div_zero, sub_zero]
    simpa only [hz] using hCT
  · have hp : 0 < 2*T := by positivity
    have h : D/(2*T) ≤ T-C := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [sq_nonneg (T-C)]
    linarith only [h]

/-- The literal full source gains the independently nonnegative Gram-curvature saving. -/
theorem ccmRestrictedWeilSource_ge_actualTrace_curvature
    (a : SuzukiPositiveAperture) (α : ℝ) (u : ccmPolarConstraintSubmodule a) :
    (α - ccmActualSourceNegativeTrace a α + ccmActualSourceGramCurvature a α /
      (2 * ccmActualSourceNegativeTrace a α)) * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 ≤
        ccmRestrictedWeilSourceQuadratic a u.1 := by
  have h := ccmActualSourceGramCeiling_le_trace_sub_curvature a α
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg ‖ccmArchimedeanFormToAperture a u.1‖)
  have hl := ccmRestrictedWeilSource_ge_actualGram a α u
  nlinarith only [hm,hl]

end RHTower
