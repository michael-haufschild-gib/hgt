import GaloisForLFunctions.RHTower.SteinhausEulerCompactMass
import Mathlib.Probability.Distributions.Cauchy

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

local notation "ν" => ProbabilityTheory.cauchyMeasure (0 : ℝ) (1 / 2)

/-- The literal normalized Euler mass against the Mellin-Parseval Cauchy kernel. -/
def steinhausEulerCauchyMass (N : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t, steinhausEulerSpatialDensity N t ω ∂ν

private def cauchyTailMass (N m : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∫⁻ t in (Icc (-(m : ℝ)) m)ᶜ, steinhausEulerSpatialDensity N t ω ∂ν

theorem measurable_steinhausEulerCauchyMass (N : ℕ) :
    Measurable (steinhausEulerCauchyMass N) :=
  (measurable_steinhausEulerSpatialDensity_joint N).lintegral_prod_right'

private theorem measurable_cauchyTailMass (N m : ℕ) : Measurable (cauchyTailMass N m) :=
  (measurable_steinhausEulerSpatialDensity_joint N).lintegral_prod_right'

private theorem half_cauchy_le_volume : ν ≤ volume := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  apply withDensity_mono
  filter_upwards with t
  change ENNReal.ofReal (ProbabilityTheory.cauchyPDFReal 0 (1 / 2) t) ≤ 1
  apply ENNReal.ofReal_le_one.mpr
  have hden : (1 / 4 : ℝ) ≤ t ^ 2 + 1 / 4 := by nlinarith [sq_nonneg t]
  have hi : (t ^ 2 + 1 / 4)⁻¹ ≤ (4 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hden
    norm_num [one_div] at h
    exact h
  have heq : ProbabilityTheory.cauchyPDFReal 0 (1 / 2) t =
      Real.pi⁻¹ * (1 / 2) * (t ^ 2 + 1 / 4)⁻¹ := by
    norm_num [ProbabilityTheory.cauchyPDFReal]
  rw [heq]
  calc
    _ ≤ Real.pi⁻¹ * (1 / 2) * 4 := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 2 / Real.pi := by ring
    _ ≤ 1 := (div_le_one Real.pi_pos).mpr Real.two_le_pi

private theorem lintegral_cauchy_spatial_set (N : ℕ) (B : Set ℝ) :
    (∫⁻ ω, ∫⁻ t in B, steinhausEulerSpatialDensity N t ω ∂ν ∂steinhausMeasure) = ν B := by
  rw [lintegral_lintegral_swap (measurable_steinhausEulerSpatialDensity_joint N).aemeasurable]
  simp_rw [lintegral_steinhausEulerSpatialDensity]
  simp

/-- Exact unit mean for the whole-line Cauchy mass. -/
theorem lintegral_steinhausEulerCauchyMass (N : ℕ) :
    (∫⁻ ω, steinhausEulerCauchyMass N ω ∂steinhausMeasure) = 1 := by
  have h := lintegral_cauchy_spatial_set N univ
  simpa [steinhausEulerCauchyMass] using h

private theorem lintegral_cauchyTailMass_rpow_le (N m : ℕ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    (∫⁻ ω, cauchyTailMass N m ω ^ q ∂steinhausMeasure) ≤
      (ν (Icc (-(m : ℝ)) m)ᶜ) ^ q := by
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := steinhausMeasure)
    (measurable_cauchyTailMass N m).aemeasurable
    (measurable_const : Measurable (fun _ : Omega => (1 : ℝ≥0∞))).aemeasurable
    hq.le (sub_pos.mpr hq1).le (by ring : q + (1 - q) = 1)
  have hmean := lintegral_cauchy_spatial_set N (Icc (-(m : ℝ)) m)ᶜ
  change (∫⁻ ω, cauchyTailMass N m ω ∂steinhausMeasure) = _ at hmean
  simpa only [ENNReal.one_rpow, mul_one, lintegral_const, measure_univ, hmean] using h

/-- Compact decay and deterministic Cauchy tail mass control the full fractional moment. -/
theorem lintegral_steinhausEulerCauchyMass_rpow_le (N m : ℕ) {q : ℝ}
    (hq : 0 < q) (hq1 : q < 1) :
    (∫⁻ ω, steinhausEulerCauchyMass N ω ^ q ∂steinhausMeasure) ≤
      (∫⁻ ω, steinhausEulerCompactMass N m ω ^ q ∂steinhausMeasure) +
        (ν (Icc (-(m : ℝ)) m)ᶜ) ^ q := by
  have hpt (ω : Omega) : steinhausEulerCauchyMass N ω ^ q ≤
      steinhausEulerCompactMass N m ω ^ q + cauchyTailMass N m ω ^ q := by
    have hs : (∫⁻ t in Icc (-(m : ℝ)) m, steinhausEulerSpatialDensity N t ω ∂ν) ≤
        steinhausEulerCompactMass N m ω :=
      lintegral_mono' (Measure.restrict_mono le_rfl half_cauchy_le_volume) le_rfl
    have hsplit := lintegral_add_compl (μ := ν)
      (fun t => steinhausEulerSpatialDensity N t ω) (measurableSet_Icc (a := -(m : ℝ)) (b := m))
    change _ + cauchyTailMass N m ω = steinhausEulerCauchyMass N ω at hsplit
    rw [← hsplit]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hq.le hq1.le).trans
      (add_le_add (ENNReal.rpow_le_rpow hs hq.le) le_rfl)
  calc
    _ ≤ ∫⁻ ω, steinhausEulerCompactMass N m ω ^ q + cauchyTailMass N m ω ^ q
        ∂steinhausMeasure := lintegral_mono hpt
    _ = (∫⁻ ω, steinhausEulerCompactMass N m ω ^ q ∂steinhausMeasure) +
        ∫⁻ ω, cauchyTailMass N m ω ^ q ∂steinhausMeasure :=
      lintegral_add_left (ENNReal.continuous_rpow_const.measurable.comp
        (measurable_steinhausEulerCompactMass N m)) _
    _ ≤ _ := add_le_add le_rfl (lintegral_cauchyTailMass_rpow_le N m hq hq1)

private theorem tendsto_cauchy_compl_compact :
    Tendsto (fun m : ℕ => ν (Icc (-(m : ℝ)) m)ᶜ) atTop (𝓝 0) := by
  have hanti : Antitone (fun m : ℕ => (Icc (-(m : ℝ)) (m : ℝ))ᶜ) := by
    intro m n hmn t ht hmem
    apply ht
    have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact ⟨(neg_le_neg hcast).trans hmem.1, hmem.2.trans hcast⟩
  have hinter : (⋂ m : ℕ, (Icc (-(m : ℝ)) (m : ℝ))ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨m, hm⟩ := exists_nat_gt |t|
    have hmem := Set.mem_iInter.mp ht m
    apply hmem
    exact ⟨by linarith [neg_abs_le t], (le_abs_self t).trans hm.le⟩
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun m : ℕ => (measurableSet_Icc.compl).nullMeasurableSet) hanti
    ⟨0, (measure_lt_top ν _).ne⟩
  simpa only [hinter, measure_empty, Function.comp_def] using h

/-- Every subunit moment of the literal whole-line Cauchy energy tends to zero. -/
theorem tendsto_lintegral_steinhausEulerCauchyMass_rpow {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun N => ∫⁻ ω, steinhausEulerCauchyMass N ω ^ q ∂steinhausMeasure)
      atTop (𝓝 0) := by
  have htail : Tendsto (fun m : ℕ => (ν (Icc (-(m : ℝ)) m)ᶜ) ^ q) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_rpow_of_pos hq] using tendsto_cauchy_compl_compact.ennrpow_const q
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  have hb : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨m, hm⟩ := ENNReal.tendsto_atTop_zero.mp htail (δ / 2) hb
  obtain ⟨N₀, hN₀⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendsto_lintegral_steinhausEulerCompactMass_rpow m hq hq1) (δ / 2) hb
  refine ⟨N₀, fun N hN => ?_⟩
  exact (lintegral_steinhausEulerCauchyMass_rpow_le N m hq hq1).trans
    ((add_le_add (hN₀ N hN) (hm m le_rfl)).trans_eq (ENNReal.add_halves δ))

/-- The first-mean arithmetic bridge uses the square-root Cauchy energy moment. -/
theorem tendsto_lintegral_steinhausEulerCauchyMass_sqrt :
    Tendsto (fun N => ∫⁻ ω, steinhausEulerCauchyMass N ω ^ (1 / 2 : ℝ) ∂steinhausMeasure)
      atTop (𝓝 0) :=
  tendsto_lintegral_steinhausEulerCauchyMass_rpow (by norm_num) (by norm_num)

end RHTower
