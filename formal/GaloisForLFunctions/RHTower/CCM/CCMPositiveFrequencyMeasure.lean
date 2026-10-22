import GaloisForLFunctions.RHTower.CCM.CCMActualSourceGramLower

/-!
# Retaining a positive-frequency window of the complete arithmetic source

The window uses the positive excess of the literal Gamma/prime/polar symbol.
Its contribution is retained before estimating the negative-frequency debt.
All source coefficient cross terms remain inside the source density.
-/

open Complex MeasureTheory Set
open scoped InnerProduct FourierTransform
noncomputable section
namespace RHTower

/-- A compact tent taking values in `[0,1]`; its radius is positive for every real parameter. -/
def ccmFrequencyTent (R ξ : ℝ) : ℝ := max 0 (1 - |ξ| / (1 + |R|))

theorem ccmFrequencyTent_bounds (R ξ : ℝ) :
    0 ≤ ccmFrequencyTent R ξ ∧ ccmFrequencyTent R ξ ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have h : 0 ≤ |ξ| / (1 + |R|) := by positivity
  linarith

theorem continuous_ccmFrequencyTent (R : ℝ) : Continuous (ccmFrequencyTent R) := by
  unfold ccmFrequencyTent
  fun_prop

theorem hasCompactSupport_ccmFrequencyTent (R : ℝ) :
    HasCompactSupport (ccmFrequencyTent R) := by
  let r : ℝ := 1 + |R|
  have hr : 0 < r := by dsimp only [r]; positivity
  apply (isCompact_Icc : IsCompact (Icc (-r) r)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro ξ hξ
  by_contra hnot
  have hlarge : r ≤ |ξ| := by
    by_contra h
    exact hnot (abs_le.mp (le_of_lt (lt_of_not_ge h)))
  have hdiv : 1 ≤ |ξ| / r := (le_div_iff₀ hr).mpr (by simpa using hlarge)
  have hz : ccmFrequencyTent R ξ = 0 := max_eq_left (by change 1 - |ξ|/r ≤ 0; linarith)
  exact hξ hz

/-- Positive excess is taken only after full arithmetic and polar assembly. -/
def ccmPositiveFrequencyWeight (a : SuzukiPositiveAperture) (α R ξ : ℝ) : ℝ :=
  max 0 (ccmActualWeilSymbol a ξ - α) * ccmFrequencyTent R ξ

theorem ccmPositiveFrequencyWeight_bounds (a : SuzukiPositiveAperture) (α R ξ : ℝ) :
    0 ≤ ccmPositiveFrequencyWeight a α R ξ ∧
      ccmPositiveFrequencyWeight a α R ξ ≤ max 0 (ccmActualWeilSymbol a ξ - α) := by
  have ht := ccmFrequencyTent_bounds R ξ
  exact ⟨mul_nonneg (le_max_left _ _) ht.1,
    mul_le_of_le_one_right (le_max_left _ _) ht.2⟩

theorem continuous_ccmPositiveFrequencyWeight (a : SuzukiPositiveAperture) (α R : ℝ) :
    Continuous (ccmPositiveFrequencyWeight a α R) :=
  (continuous_const.max ((continuous_ccmActualWeilSymbol a).sub continuous_const)).mul
    (continuous_ccmFrequencyTent R)

theorem hasCompactSupport_ccmPositiveFrequencyWeight
    (a : SuzukiPositiveAperture) (α R : ℝ) :
    HasCompactSupport (ccmPositiveFrequencyWeight a α R) :=
  (hasCompactSupport_ccmFrequencyTent R).mul_left

theorem integrable_ccmPositiveFrequencyWeight (a : SuzukiPositiveAperture) (α R : ℝ) :
    Integrable (ccmPositiveFrequencyWeight a α R) :=
  (continuous_ccmPositiveFrequencyWeight a α R).integrable_of_hasCompactSupport
    (hasCompactSupport_ccmPositiveFrequencyWeight a α R)

def ccmPositiveFrequencyMeasure (a : SuzukiPositiveAperture) (α R : ℝ) : Measure ℝ :=
  volume.withDensity (fun ξ => ENNReal.ofReal (ccmPositiveFrequencyWeight a α R ξ))

instance ccmPositiveFrequencyMeasure_finite (a : SuzukiPositiveAperture) (α R : ℝ) :
    IsFiniteMeasure (ccmPositiveFrequencyMeasure a α R) :=
  isFiniteMeasure_withDensity_ofReal (integrable_ccmPositiveFrequencyWeight a α R).hasFiniteIntegral

theorem ccmPositiveFrequency_integral (a : SuzukiPositiveAperture) (α R : ℝ) (g : ℝ → ℝ) :
    (∫ ξ, g ξ ∂ccmPositiveFrequencyMeasure a α R) =
      ∫ ξ, ccmPositiveFrequencyWeight a α R ξ * g ξ := by
  rw [ccmPositiveFrequencyMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_ccmPositiveFrequencyWeight a α R).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (ccmPositiveFrequencyWeight_bounds a α R _).1,
    smul_eq_mul]

theorem ccmNegativeFrequency_integral (a : SuzukiPositiveAperture) (α : ℝ) (g : ℝ → ℝ) :
    (∫ ξ, g ξ ∂ccmActualSourceNegativeMeasure a α) =
      ∫ ξ, ccmActualSourceNegativeWeight a α ξ * g ξ := by
  rw [ccmActualSourceNegativeMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_ccmActualSourceNegativeWeight a α).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_left 0 _), smul_eq_mul,
    ccmActualSourceNegativeWeight]

private theorem compact_weight_mul_integrable {w φ : ℝ → ℝ}
    (hw : Continuous w) (hk : HasCompactSupport w) (hφ : Integrable φ) :
    Integrable (fun ξ => w ξ * φ ξ) := by
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuousOn hw.continuousOn
  apply hφ.bdd_mul hw.aestronglyMeasurable
  filter_upwards with ξ
  by_cases hξ : ξ ∈ tsupport w
  · exact (hC ξ hξ).trans (le_max_left C 0)
  · have hz : w ξ = 0 := by
      by_contra hn
      exact hξ (subset_closure hn)
    simpa only [hz, norm_zero] using le_max_right C 0

/-- The full source pays for any retained fraction of the positive window before debt is estimated. -/
theorem ccmRestrictedWeilSource_ge_retainedPositiveWindow
    (a : SuzukiPositiveAperture) (α R : ℝ) (θ : Icc (0 : ℝ) 1)
    (u : CCMArchimedeanFormDomain a) :
    α * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 -
      ((∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmActualSourceNegativeMeasure a α) -
        θ.1 * (∫ ξ, ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 ∂ccmPositiveFrequencyMeasure a α R)) ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  let φ : ℝ → ℝ := fun ξ => ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2
  have hφ : Integrable φ := integrable_norm_sq_ccmFormDomain a u
  have hN := compact_weight_mul_integrable (continuous_ccmActualSourceNegativeWeight a α)
    (hasCompactSupport_ccmActualSourceNegativeWeight a α) hφ
  have hP := compact_weight_mul_integrable (continuous_ccmPositiveFrequencyWeight a α R)
    (hasCompactSupport_ccmPositiveFrequencyWeight a α R) hφ
  have hM : Integrable (fun ξ => ccmActualWeilSymbol a ξ * φ ξ) := by
    apply (integrable_correctedCCMSymbol_mul_actualHeadDensity a u).congr
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1] with ξ hξ
    rw [hξ]
    rfl
  have hpoint (ξ : ℝ) :
      α * φ ξ - (ccmActualSourceNegativeWeight a α ξ * φ ξ -
        θ.1 * (ccmPositiveFrequencyWeight a α R ξ * φ ξ)) ≤
      ccmActualWeilSymbol a ξ * φ ξ := by
    have hp := ccmPositiveFrequencyWeight_bounds a α R ξ
    have hθp := mul_le_of_le_one_left hp.1 θ.2.2
    have hbase : α - ccmActualSourceNegativeWeight a α ξ +
        θ.1 * ccmPositiveFrequencyWeight a α R ξ ≤ ccmActualWeilSymbol a ξ := by
      by_cases hm : α ≤ ccmActualWeilSymbol a ξ
      · rw [ccmActualSourceNegativeWeight, max_eq_left (sub_nonpos.mpr hm)]
        rw [max_eq_right (sub_nonneg.mpr hm)] at hp
        linarith only [hp.2,hθp]
      · have hm' := le_of_lt (lt_of_not_ge hm)
        rw [max_eq_left (sub_nonpos.mpr hm')] at hp
        have hz := le_antisymm hp.2 hp.1
        rw [hz, mul_zero, ccmActualSourceNegativeWeight,
          max_eq_right (sub_nonneg.mpr hm')]
        linarith
    have h := mul_le_mul_of_nonneg_right hbase (sq_nonneg ‖(u.1 : ℝ → ℂ) ξ‖)
    dsimp only [φ] at h ⊢
    nlinarith only [h]
  have h := integral_mono ((hφ.const_mul α).sub (hN.sub (hP.const_mul θ.1))) hM hpoint
  have houter := integral_sub (hφ.const_mul α) (hN.sub (hP.const_mul θ.1))
  have hinner := integral_sub hN (hP.const_mul θ.1)
  dsimp only [Pi.sub_apply] at h houter hinner
  rw [houter, hinner, integral_const_mul, integral_const_mul] at h
  dsimp only [φ] at h
  rw [integral_norm_sq_ccmFormDomain, ← ccmRestrictedWeilSource_eq_actualSymbol,
    ← ccmNegativeFrequency_integral, ← ccmPositiveFrequency_integral] at h
  exact h

end RHTower
