import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeightCutoffEnergy
import GaloisForLFunctions.HTGeometry.ResolutionAmplification

/-!
# Height marginals of truncated resonant states

Complete-horocycle cancellation identifies the actual height-energy measure.
Normalizing its mass gives a cutoff-one component and an explicit power-density
band. No high-frequency limit is used in this identity.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower
open scoped ENNReal

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The height pushforward of the actual truncated state's squared norm. -/
def heightEnergyMeasure (u : ℂ) (Y : ℝ) : Measure ℝ :=
  Measure.map UpperHalfPlane.im ((volume.restrict fd).withDensity
    (fun z => ENNReal.ofReal (‖truncatedLineModel u Y z‖ ^ 2)))

theorem heightEnergyMeasure_finite (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    IsFiniteMeasure (heightEnergyMeasure u Y) := by
  letI := isFiniteMeasure_withDensity_ofReal (cutoff_norm_sq_integrable u hY).hasFiniteIntegral
  unfold heightEnergyMeasure
  infer_instance

/-- Integration against the height pushforward is integration of the height test. -/
theorem integral_heightEnergyMeasure (u : ℂ) (Y : ℝ) (g : ℝ → ℝ)
    (hg : Measurable g) :
    (∫ y, g y ∂heightEnergyMeasure u Y) =
      ∫ z in fd, g z.im * ‖truncatedLineModel u Y z‖ ^ 2 := by
  unfold heightEnergyMeasure
  rw [integral_map UpperHalfPlane.continuous_im.measurable.aemeasurable
    hg.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_truncatedLineModel u Y).norm.pow_const 2).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]

/-- The unnormalized power density on a positive height interval. -/
def heightPowerBand (κ a b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc a b)).withDensity (fun y => ENNReal.ofReal (y ^ (κ - 1)))

theorem heightPowerBand_finite (κ : ℝ) {a b : ℝ} (ha : 0 < a) :
    IsFiniteMeasure (heightPowerBand κ a b) := by
  have hi : IntegrableOn (fun y : ℝ => y ^ (κ - 1)) (Icc a b) :=
    (continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (ha.trans_le hy.1)))).integrableOn_Icc
  exact isFiniteMeasure_withDensity_ofReal (hi.mono_set Ioc_subset_Icc_self).hasFiniteIntegral

theorem integral_heightPowerBand (κ : ℝ) {a b : ℝ} (ha : 0 ≤ a) (g : ℝ → ℝ) :
    (∫ y, g y ∂heightPowerBand κ a b) = ∫ y in Ioc a b, g y * y ^ (κ - 1) := by
  unfold heightPowerBand
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (y ^ (κ - 1))) :=
    (measurable_id.pow_const (κ - 1)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (ha.trans hy.1.le) _), smul_eq_mul, mul_comm]

private theorem bounded_height_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (g : ℝ → ℝ) (hg : Measurable g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable g μ :=
  (integrable_const M).mono' hg.aestronglyMeasurable (Eventually.of_forall hM)

/-- Exact equality of actual height measures, including every measurable height test. -/
theorem resonant_heightEnergyMeasure {u : ℂ} (hAu : msA u = 0)
    {Y : ℝ} (hY : 1 ≤ Y) :
    heightEnergyMeasure u Y = heightEnergyMeasure u 1 +
      ENNReal.ofReal (‖msB u‖ ^ 2) • heightPowerBand (-2 * u.re) 1 Y := by
  letI := heightEnergyMeasure_finite u hY
  letI := heightEnergyMeasure_finite u (Y := 1) le_rfl
  letI := heightPowerBand_finite (-2 * u.re) (b := Y) zero_lt_one
  letI := (heightPowerBand (-2 * u.re) 1 Y).smul_finite
    (c := ENNReal.ofReal (‖msB u‖ ^ 2)) ENNReal.ofReal_ne_top
  apply measure_eq_of_integral_lipschitz_eq
  intro g hg hgb
  rcases hg with ⟨K, hK⟩
  have hM : ∀ y, ‖g y‖ ≤ 1 := fun y => by
    rw [Real.norm_of_nonneg (hgb y).1]
    exact (hgb y).2
  have hi₁ := bounded_height_integrable (heightEnergyMeasure u 1) g hK.continuous.measurable hM
  have hi₂ := bounded_height_integrable
    (ENNReal.ofReal (‖msB u‖ ^ 2) • heightPowerBand (-2 * u.re) 1 Y)
    g hK.continuous.measurable hM
  rw [integral_add_measure hi₁ hi₂, integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
    integral_heightEnergyMeasure u Y g hK.continuous.measurable,
    integral_heightEnergyMeasure u 1 g hK.continuous.measurable,
    integral_heightPowerBand _ zero_le_one]
  exact resonant_height_weighted_energy g hK.continuous hM hAu hY

/-- The total height-energy mass is the Maass--Selberg norm. -/
theorem heightEnergyMeasure_mass (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    heightEnergyMeasure u Y univ =
      ENNReal.ofReal (∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2) := by
  unfold heightEnergyMeasure
  rw [Measure.map_apply UpperHalfPlane.continuous_im.measurable MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (cutoff_norm_sq_integrable u hY)
      (Eventually.of_forall fun _ => sq_nonneg _)]

/-- The actual height marginal divided by its exact resonant squared norm. -/
def heightProbabilityMeasure (u : ℂ) (Y : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((-2 * u.re) / (‖msB u‖ ^ 2 * Y ^ (-2 * u.re))) •
    heightEnergyMeasure u Y

theorem heightProbabilityMeasure_probability {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y) :
    IsProbabilityMeasure (heightProbabilityMeasure u Y) := by
  have hk : 0 < -2 * u.re := by linarith
  have hB : 0 < ‖msB u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
    (msB_ne_zero_of_negative_re hu hur))
  have hB0 : ‖msB u‖ ≠ 0 := norm_ne_zero_iff.mpr (msB_ne_zero_of_negative_re hu hur)
  have hp : 0 < Y ^ (-2 * u.re) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hY) _
  rw [isProbabilityMeasure_iff, heightProbabilityMeasure, Measure.smul_apply, smul_eq_mul,
    heightEnergyMeasure_mass u hY, integral_norm_sq_of_msA_eq_zero hu hur hAu hY,
    ← ENNReal.ofReal_mul (div_nonneg hk.le (mul_nonneg hB.le hp.le))]
  have he : (-2 * u.re) / (‖msB u‖ ^ 2 * Y ^ (-2 * u.re)) *
      (‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / (-2 * u.re)) = 1 := by
    field_simp [hur.ne, hB0, hp.ne']
  rw [he, ENNReal.ofReal_one]

/-- The cutoff-one probability survives with mass `Y^(-κ)`; the rest is an explicit band. -/
theorem resonant_heightProbabilityMeasure {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y) :
    heightProbabilityMeasure u Y =
      ENNReal.ofReal (Y ^ (2 * u.re)) • heightProbabilityMeasure u 1 +
      ENNReal.ofReal ((-2 * u.re) * Y ^ (2 * u.re)) •
        heightPowerBand (-2 * u.re) 1 Y := by
  have hk : 0 < -2 * u.re := by linarith
  have hB : 0 < ‖msB u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
    (msB_ne_zero_of_negative_re hu hur))
  have hB0 : ‖msB u‖ ≠ 0 := norm_ne_zero_iff.mpr (msB_ne_zero_of_negative_re hu hur)
  have hp : 0 < Y ^ (-2 * u.re) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hY) _
  have hn : Y ^ (2 * u.re) = (Y ^ (-2 * u.re))⁻¹ := by
    rw [show 2 * u.re = -(-2 * u.re) by ring,
      Real.rpow_neg (zero_lt_one.trans_le hY).le]
  have hc : 0 ≤ (-2 * u.re) / (‖msB u‖ ^ 2 * Y ^ (-2 * u.re)) := by positivity
  unfold heightProbabilityMeasure
  rw [resonant_heightEnergyMeasure hAu hY, smul_add, smul_smul, smul_smul,
    Real.one_rpow, mul_one, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (zero_lt_one.trans_le hY).le _)]
  congr 1
  · congr 1
    apply congrArg ENNReal.ofReal
    rw [hn]
    field_simp [hur.ne, hB0, hp.ne']
  · congr 1
    apply congrArg ENNReal.ofReal
    rw [hn]
    field_simp [hur.ne, hB0, hp.ne']

/-- Positive powers remain integrable at height zero. -/
theorem heightPowerBand_finite_of_pos {κ a b : ℝ} (hk : 0 < κ) :
    IsFiniteMeasure (heightPowerBand κ a b) := by
  have hi : IntegrableOn (fun y : ℝ => y ^ (κ - 1)) (Ioc a b) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < κ - 1)).1
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

/-- The exact mass of a power-density band. -/
theorem heightPowerBand_mass {κ a b : ℝ} (hk : 0 < κ) (ha : 0 ≤ a) (hab : a ≤ b) :
    heightPowerBand κ a b univ = ENNReal.ofReal ((b ^ κ - a ^ κ) / κ) := by
  have hi : IntegrableOn (fun y : ℝ => y ^ (κ - 1)) (Ioc a b) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < κ - 1)).1
  have hp : 0 ≤ᵐ[volume.restrict (Ioc a b)] (fun y : ℝ => y ^ (κ - 1)) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy =>
      Real.rpow_nonneg (ha.trans hy.1.le) _)
  rw [heightPowerBand, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hp, ← intervalIntegral.integral_of_le hab,
    integral_rpow (Or.inl (by linarith : -1 < κ - 1))]
  simp only [sub_add_cancel]

theorem heightPowerBand_below {κ C Y : ℝ} (hCY : C ≤ Y) :
    heightPowerBand κ 1 Y (Ioc 0 C) = heightPowerBand κ 1 C univ := by
  have he : Ioc 0 C ∩ Ioc 1 Y = Ioc 1 C := by
    ext y
    simp only [mem_inter_iff, mem_Ioc]
    constructor
    · exact fun h => ⟨h.2.1, h.1.2⟩
    · exact fun h => ⟨⟨zero_lt_one.trans h.1, h.2⟩, ⟨h.1, h.2.trans hCY⟩⟩
  rw [heightPowerBand, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, he, heightPowerBand,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
