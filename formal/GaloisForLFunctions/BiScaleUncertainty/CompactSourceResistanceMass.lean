import GaloisForLFunctions.BiScaleUncertainty.MixedEdgePathCongestion
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicJumpEnergyTransfer

/-!
# Finite resistance mass of compact-source mixed jump measures

The archimedean singularity cancels against physical path resistance. Compact
source support also kills all sufficiently large logarithmic atom lags, with
no summability assumption on the nonnegative atom coefficients.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
set_option autoImplicit false

def sourcePair (ψ : C_c(ℝ, ℝ)) (e : Edge) : ℝ := ψ e.2 ^ 2 * ψ (e.2+e.1) ^ 2

theorem sourcePair_nonneg (ψ : C_c(ℝ, ℝ)) (e : Edge) : 0 ≤ sourcePair ψ e :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem continuous_sourcePair (ψ : C_c(ℝ, ℝ)) : Continuous (sourcePair ψ) := by
  unfold sourcePair
  fun_prop

theorem sourcePair_endpoints (ψ : C_c(ℝ, ℝ)) (e : Edge) (he : sourcePair ψ e ≠ 0) :
    e.2 ∈ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ) ∧
      e.2+e.1 ∈ Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ) := by
  have h₁ : ψ e.2 ≠ 0 := by intro h; simp [sourcePair, h] at he
  have h₂ : ψ (e.2+e.1) ≠ 0 := by intro h; simp [sourcePair, h] at he
  exact ⟨abs_le.mp (abs_le_multiplierSourceRadius ψ _ h₁),
    abs_le.mp (abs_le_multiplierSourceRadius ψ _ h₂)⟩

/-- The actual diffuse plus countable arithmetic source measure. -/
def compactMixture (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) : EdgeMixture where
  diffuseWeight e := ENNReal.ofReal (archLevySinhWeight e.1 * sourcePair ψ e)
  lag n := Real.log ((n : ℝ)+2)
  lineWeight n u := ENNReal.ofReal ((λ n : ℝ) * sourcePair ψ (Real.log ((n : ℝ)+2),u))

theorem measurable_compactDiffuse (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) :
    Measurable (compactMixture ψ λ).diffuseWeight := by
  dsimp [compactMixture, archLevySinhWeight]
  have := (continuous_sourcePair ψ).measurable
  fun_prop

theorem measurable_compactLine (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (n : ℕ) :
    Measurable ((compactMixture ψ λ).lineWeight n) := by
  dsimp [compactMixture]
  have := (continuous_sourcePair ψ).measurable
  fun_prop

/-- Smooth extension of the resistance-weighted diffuse density through zero lag. -/
def cancelledDensity (ψ : C_c(ℝ, ℝ)) (e : Edge) : ℝ :=
  (2*Real.exp (e.2+e.1/2)/(1+Real.exp (-e.1))) * sourcePair ψ e

theorem continuous_cancelledDensity (ψ : C_c(ℝ, ℝ)) : Continuous (cancelledDensity ψ) := by
  have hd (e : Edge) : 1+Real.exp (-e.1) ≠ 0 := ne_of_gt (by positivity)
  exact ((continuous_const.mul (Real.continuous_exp.comp
    (continuous_snd.add (continuous_fst.div_const 2)))).div
      (continuous_const.add (Real.continuous_exp.comp continuous_fst.neg)) hd).mul
        (continuous_sourcePair ψ)

theorem cancelledDensity_nonneg (ψ : C_c(ℝ, ℝ)) (e : Edge) :
    0 ≤ cancelledDensity ψ e := by
  exact mul_nonneg (by positivity) (sourcePair_nonneg ψ e)

theorem hasCompactSupport_cancelledDensity (ψ : C_c(ℝ, ℝ)) :
    HasCompactSupport (cancelledDensity ψ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-2*multiplierSourceRadius ψ) (2*multiplierSourceRadius ψ) ×ˢ
        Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)))
  intro e he
  have hp : sourcePair ψ e ≠ 0 := by
    intro hp
    simp [Function.mem_support, cancelledDensity, hp] at he
  rcases sourcePair_endpoints ψ e hp with ⟨h₁,h₂⟩
  exact ⟨⟨by linarith [h₁.2,h₂.1], by linarith [h₁.1,h₂.2]⟩,h₁⟩

theorem integrable_cancelledDensity (ψ : C_c(ℝ, ℝ)) :
    Integrable (cancelledDensity ψ) (volume.prod volume) :=
  (continuous_cancelledDensity ψ).integrable_of_hasCompactSupport
    (hasCompactSupport_cancelledDensity ψ)

theorem resistance_arch_cancellation (h u : ℝ) (hh : 0 < h) :
    resistance (h,u)*archLevySinhWeight h =
      2*Real.exp (u+h/2)/(1+Real.exp (-h)) := by
  have hs := (Real.sinh_pos_iff.mpr hh).ne'
  have hd : 1+Real.exp (-h) ≠ 0 := ne_of_gt (by positivity)
  have he : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
  have hu : u ≤ u+h := by linarith
  simp only [resistance, upper, lower, max_eq_right hu, min_eq_left hu]
  rw [archLevySinhWeight, Real.exp_add, Real.exp_add]
  field_simp [hs, hd]
  rw [Real.sinh_eq]
  linear_combination (Real.exp u * Real.exp (h/2)) * he

theorem diffuse_resistance_density (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0)
    (e : Edge) (he : 0 < e.1) :
    (compactMixture ψ λ).diffuseWeight e * ENNReal.ofReal (resistance e) =
      ENNReal.ofReal (cancelledDensity ψ e) := by
  rw [← ENNReal.ofReal_mul (mul_nonneg (archLevySinhWeight_nonneg he.le)
    (sourcePair_nonneg ψ e))]
  congr 1
  dsimp [cancelledDensity]
  rw [← resistance_arch_cancellation e.1 e.2 he]
  ring

def atomCutoff (ψ : C_c(ℝ, ℝ)) : ℕ := ⌈Real.exp (2*multiplierSourceRadius ψ)⌉₊+1

theorem large_lag_sourcePair_zero (ψ : C_c(ℝ, ℝ)) (n : ℕ)
    (hn : atomCutoff ψ ≤ n) (u : ℝ) :
    sourcePair ψ (Real.log ((n : ℝ)+2),u) = 0 := by
  by_contra hp
  rcases sourcePair_endpoints ψ _ hp with ⟨h₁,h₂⟩
  have hn' : (⌈Real.exp (2*multiplierSourceRadius ψ)⌉₊ : ℝ)+1 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hlag : 2*multiplierSourceRadius ψ < Real.log ((n : ℝ)+2) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    linarith [Nat.le_ceil (Real.exp (2*multiplierSourceRadius ψ))]
  dsimp at h₁ h₂
  linarith [h₁.1,h₂.2]

theorem compactLine_eq_zero (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (n : ℕ)
    (hn : atomCutoff ψ ≤ n) : (compactMixture ψ λ).lineWeight n = 0 := by
  funext u
  simp [compactMixture, large_lag_sourcePair_zero ψ n hn u]

def lineResistanceDensity (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (n : ℕ) (u : ℝ) : ℝ :=
  ((λ n : ℝ)*sourcePair ψ (Real.log ((n : ℝ)+2),u)) *
    resistance (Real.log ((n : ℝ)+2),u)

theorem integrable_lineResistanceDensity (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (lineResistanceDensity ψ λ n) := by
  have hc : Continuous (lineResistanceDensity ψ λ n) := by
    dsimp [lineResistanceDensity, sourcePair, resistance, lower, upper]
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)))
  intro u hu
  have hp : sourcePair ψ (Real.log ((n : ℝ)+2),u) ≠ 0 := by
    intro hp
    simp [Function.mem_support, lineResistanceDensity, hp] at hu
  exact (sourcePair_endpoints ψ _ hp).1

theorem lineResistanceDensity_nonneg (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (n : ℕ) (u : ℝ) :
    0 ≤ lineResistanceDensity ψ λ n u :=
  mul_nonneg (mul_nonneg (λ n).coe_nonneg (sourcePair_nonneg ψ _)) (resistance_nonneg _)

private theorem ae_positiveLag :
    ∀ᵐ e : Edge ∂(volume.restrict (Ioi (0 : ℝ))).prod volume, 0 < e.1 := by
  apply (ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact Eventually.of_forall (fun _ => hh)

theorem compactDiffuse_resistance_integral (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) :
    (∫⁻ e, ENNReal.ofReal (resistance e) ∂diffuseMeasure (compactMixture ψ λ)) =
      ∫⁻ e, ENNReal.ofReal (cancelledDensity ψ e)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod volume := by
  rw [diffuseMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_compactDiffuse ψ λ) measurable_resistance.ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [ae_positiveLag] with e he
  exact diffuse_resistance_density ψ λ e he

theorem compactLine_resistance_integral (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) (n : ℕ) :
    (∫⁻ e, ENNReal.ofReal (resistance e) ∂lineMeasure (compactMixture ψ λ) n) =
      ∫⁻ u, ENNReal.ofReal (lineResistanceDensity ψ λ n u) := by
  rw [lineMeasure, lintegral_map measurable_resistance.ennreal_ofReal
    (measurable_const.prodMk measurable_id), lintegral_withDensity_eq_lintegral_mul _
      (measurable_compactLine ψ λ n)
      (measurable_resistance.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal]
  apply lintegral_congr
  intro u
  exact (ENNReal.ofReal_mul (mul_nonneg (λ n).coe_nonneg (sourcePair_nonneg ψ _))).symm

/-- Finite controlling coefficient; the unweighted total edge mass need not be finite. -/
def resistanceMass (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ e, ENNReal.ofReal (resistance e) ∂edgeMeasure (compactMixture ψ λ)

/-- The entire countable mixture has an exact finite-sum resistance formula. -/
theorem resistanceMass_eq_finite (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) :
    resistanceMass ψ λ =
      (∫⁻ e, ENNReal.ofReal (cancelledDensity ψ e)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod volume) +
      ∑ n ∈ Finset.range (atomCutoff ψ), ∫⁻ u, ENNReal.ofReal (lineResistanceDensity ψ λ n u) := by
  rw [resistanceMass, edgeMeasure, lintegral_add_measure, lintegral_sum_measure,
    compactDiffuse_resistance_integral]
  simp_rw [compactLine_resistance_integral]
  congr 1
  apply tsum_eq_sum
  intro n hn
  have hn' : atomCutoff ψ ≤ n := Nat.le_of_not_lt (by simpa using hn)
  simp [lineResistanceDensity, large_lag_sourcePair_zero ψ n hn']

theorem resistanceMass_ne_top (ψ : C_c(ℝ, ℝ)) (λ : ℕ → ℝ≥0) :
    resistanceMass ψ λ ≠ ∞ := by
  rw [resistanceMass_eq_finite, ENNReal.add_ne_top]
  constructor
  · apply ne_of_lt
    apply (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (cancelledDensity_nonneg ψ))).mp
    exact ((integrable_cancelledDensity ψ).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)).hasFiniteIntegral
  · apply ENNReal.sum_ne_top.mpr
    intro n _
    exact ne_of_lt ((hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (lineResistanceDensity_nonneg ψ λ n))).mp
        (integrable_lineResistanceDensity ψ λ n).hasFiniteIntegral)

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
