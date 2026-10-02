import GaloisForLFunctions.RHTower.PMDilationMellin
import GaloisForLFunctions.RHTower.DivisorContinuousHeadRegularity
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.RHTower.ZetaPoleSplit

/-!
# The native divisor square's combined Möbius budget

The reciprocal weight is formed from the actual unsigned divisor head. Its
Möbius dilation has an absolutely convergent Mellin transform to the right
of one. The continued budget vanishes at one, with strictly positive first
coefficient. This controls the combined signed source, not its endpoint square.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex

namespace RHTower

/-- The reciprocal-variable square of the native unsigned divisor head. -/
def routePCoprimeSquareWeight (y : ℝ) : ℝ :=
  y * divisorContinuousUnitHead y⁻¹ ^ 2

theorem routePCoprimeSquareWeight_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    routePCoprimeSquareWeight y = 0 := by
  have hi : y⁻¹ ≤ 1 := le_trans (inv_nonpos.mpr hy) (by norm_num)
  simp [routePCoprimeSquareWeight, divisorContinuousUnitHead_eq_zero hi]

theorem routePCoprimeSquareWeight_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    routePCoprimeSquareWeight y = 0 := by
  have hp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hi : y⁻¹ ≤ 1 := (inv_le_iff_one_le_mul₀ hp).mpr (by simpa using hy)
  simp [routePCoprimeSquareWeight, divisorContinuousUnitHead_eq_zero hi]

theorem routePCoprimeSquareWeight_nonneg (y : ℝ) :
    0 ≤ routePCoprimeSquareWeight y := by
  by_cases hy : 0 ≤ y
  · exact mul_nonneg hy (sq_nonneg _)
  · rw [routePCoprimeSquareWeight_eq_zero_of_nonpos (le_of_not_ge hy)]

theorem routePCoprimeSquareWeight_le (y : ℝ) :
    routePCoprimeSquareWeight y ≤ 9 / 25 := by
  by_cases hy : 0 < y
  · have hu := divisorContinuousUnitHead_le_sqrt y⁻¹
    have hn := divisorContinuousUnitHead_nonneg y⁻¹
    have hs := Real.sq_sqrt (inv_nonneg.mpr hy.le)
    have hq : divisorContinuousUnitHead y⁻¹ ^ 2 ≤ (9 / 25 : ℝ) * y⁻¹ := by
      nlinarith [Real.sqrt_nonneg y⁻¹]
    calc
      routePCoprimeSquareWeight y ≤ y * ((9 / 25 : ℝ) * y⁻¹) :=
        mul_le_mul_of_nonneg_left hq hy.le
      _ = 9 / 25 := by field_simp
  · rw [routePCoprimeSquareWeight_eq_zero_of_nonpos (le_of_not_gt hy)]
    norm_num

theorem measurable_routePCoprimeSquareWeight : Measurable routePCoprimeSquareWeight :=
  measurable_id.mul ((measurable_divisorContinuousUnitHead.comp measurable_inv).pow_const 2)

theorem norm_routePCoprimeSquareWeight (y : ℝ) :
    ‖(routePCoprimeSquareWeight y : ℂ)‖ ≤ 9 / 25 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (routePCoprimeSquareWeight_nonneg y)] using routePCoprimeSquareWeight_le y

private theorem weight_locallyIntegrable :
    LocallyIntegrable (fun y => (routePCoprimeSquareWeight y : ℂ)) := by
  apply (continuous_const : Continuous (fun _ : ℝ => (9 / 25 : ℝ))).locallyIntegrable.mono
    (Complex.continuous_ofReal.measurable.comp
      measurable_routePCoprimeSquareWeight).aestronglyMeasurable
  filter_upwards with y
  simpa using norm_routePCoprimeSquareWeight y

private theorem weight_top (a : ℝ) :
    (fun y => (routePCoprimeSquareWeight y : ℂ)) =O[atTop] (fun y : ℝ => y ^ (-a)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨0, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  simp [routePCoprimeSquareWeight_eq_zero_of_one_le hy]

private theorem weight_bottom :
    (fun y => (routePCoprimeSquareWeight y : ℂ)) =O[𝓝[>] 0]
      (fun y : ℝ => y ^ (-(0 : ℝ))) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨9 / 25, Eventually.of_forall fun y => ?_⟩
  simpa using norm_routePCoprimeSquareWeight y

theorem mellinConvergent_routePCoprimeSquareWeight {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun y => (routePCoprimeSquareWeight y : ℂ)) s :=
  mellinConvergent_of_isBigO_rpow
    (weight_locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (weight_top (s.re + 1)) (by linarith) weight_bottom hs

theorem differentiableAt_mellin_routePCoprimeSquareWeight {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun y => (routePCoprimeSquareWeight y : ℂ))) s :=
  mellin_differentiableAt_of_isBigO_rpow
    (weight_locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (weight_top (s.re + 1)) (by linarith) weight_bottom hs

/-- All Möbius terms are retained; no positive or absolute-value replacement. -/
def routePCoprimeSquareSource : ℝ → ℂ :=
  pmWeightedDilationSource (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
    (fun y => (routePCoprimeSquareWeight y : ℂ))

theorem routePCoprimeSquareSource_hasMellin {s : ℂ} (hs : 1 < s.re) :
    HasMellin routePCoprimeSquareSource s
      ((riemannZeta s)⁻¹ * mellin (fun y => (routePCoprimeSquareWeight y : ℂ)) s) := by
  have h := pmWeightedDilationSource_hasMellin
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
    (fun y => (routePCoprimeSquareWeight y : ℂ)) (by simp)
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
    (mellinConvergent_routePCoprimeSquareWeight (by linarith : 0 < s.re))
  rw [LSeries_moebius_eq_inv_riemannZeta hs] at h
  exact h

theorem integrableOn_routePCoprimeSquareWeight :
    IntegrableOn routePCoprimeSquareWeight (Ioi 0) := by
  have h : IntegrableOn (fun y => (routePCoprimeSquareWeight y : ℂ)) (Ioi 0) := by
    simpa [MellinConvergent] using
      (mellinConvergent_routePCoprimeSquareWeight (s := 1) (by norm_num))
  change Integrable routePCoprimeSquareWeight (volume.restrict (Ioi 0))
  have hn := h.norm
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (routePCoprimeSquareWeight_nonneg _)] using hn

/-- The native positive coefficient of the combined budget's boundary zero. -/
def routePCoprimeSquareMass : ℝ := ∫ y in Ioi (0 : ℝ), routePCoprimeSquareWeight y

theorem routePCoprimeSquareMass_pos : 0 < routePCoprimeSquareMass := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall routePCoprimeSquareWeight_nonneg)
    integrableOn_routePCoprimeSquareWeight).mpr
  have hsub : Ioo (1 / 2 : ℝ) 1 ⊆ Function.support routePCoprimeSquareWeight := by
    intro y hy
    have hp : 0 < y := by have := hy.1; linarith
    have hi : y⁻¹ ∈ Ioo (1 : ℝ) 2 :=
      ⟨(one_lt_inv₀ hp).mpr hy.2,
        (inv_lt_iff_one_lt_mul₀ hp).mpr (by have := hy.1; linarith)⟩
    exact ne_of_gt (mul_pos hp (pow_pos (divisorContinuousUnitHead_pos_first hi) 2))
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Measure.restrict_apply measurableSet_Ioo]
  have he : Ioo (1 / 2 : ℝ) 1 ∩ Ioi 0 = Ioo (1 / 2 : ℝ) 1 :=
    inter_eq_left.mpr (fun y hy => by have := hy.1; exact show 0 < y by linarith)
  rw [he, Real.volume_Ioo]
  norm_num

theorem mellin_routePCoprimeSquareWeight_one :
    mellin (fun y => (routePCoprimeSquareWeight y : ℂ)) 1 =
      (routePCoprimeSquareMass : ℂ) := by
  simp [mellin, routePCoprimeSquareMass, integral_complex_ofReal]

theorem mellin_routePCoprimeSquareSource_eq_poleUnit {s : ℂ} (hs : 1 < s.re) :
    mellin routePCoprimeSquareSource s =
      (s - 1) * mellin (fun y => (routePCoprimeSquareWeight y : ℂ)) s / zetaPoleUnit s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [(routePCoprimeSquareSource_hasMellin hs).2, zetaPoleUnit_of_ne hs1]
  field_simp [sub_ne_zero.mpr hs1, riemannZeta_ne_zero_of_one_lt_re hs]

private theorem one_add_tendsto :
    Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa using tendsto_const_nhds.add hε

/-- An actual admitted signed-source integral has a positive first-order coefficient. -/
theorem mellin_routePCoprimeSquareSource_simpleJet :
    Tendsto (fun ε : ℝ => mellin routePCoprimeSquareSource (1 + (ε : ℂ)) / (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (routePCoprimeSquareMass : ℂ)) := by
  have hc : ContinuousAt (fun s : ℂ =>
      mellin (fun y => (routePCoprimeSquareWeight y : ℂ)) s / zetaPoleUnit s) 1 :=
    (differentiableAt_mellin_routePCoprimeSquareWeight (by norm_num : 0 < (1 : ℂ).re)).continuousAt.div
      (differentiable_zetaPoleUnit 1).continuousAt (by simp [zetaPoleUnit_one])
  have hlim := hc.tendsto.comp one_add_tendsto
  simp only [mellin_routePCoprimeSquareWeight_one, zetaPoleUnit_one, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  have hs : 1 < ((1 : ℂ) + (ε : ℂ)).re := by simpa using hε
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  simp only [Function.comp_def]
  rw [mellin_routePCoprimeSquareSource_eq_poleUnit hs,
    show (1 : ℂ) + (ε : ℂ) - 1 = (ε : ℂ) by ring]
  field_simp [he]

/-- Vanishing of the combined budget does not assert integrability at the boundary. -/
theorem mellin_routePCoprimeSquareSource_tendsto_zero :
    Tendsto (fun ε : ℝ => mellin routePCoprimeSquareSource (1 + (ε : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := mellin_routePCoprimeSquareSource_simpleJet.mul hε
  simp only [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hε.ne')

/-- The admitted source is the literal complete finite cutoff at every positive argument. -/
theorem routePCoprimeSquareSource_eq_sum {y : ℝ} (hy : 0 < y) :
    routePCoprimeSquareSource y =
      ∑ n ∈ Finset.Icc 1 ⌊y⁻¹⌋₊,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          (routePCoprimeSquareWeight ((n : ℝ) * y) : ℂ) := by
  unfold routePCoprimeSquareSource pmWeightedDilationSource
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hnf : ⌊y⁻¹⌋₊ < n := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
    have hny : 1 ≤ (n : ℝ) * y :=
      ((inv_lt_iff_one_lt_mul₀ hy).mp (Nat.lt_of_floor_lt hnf)).le
    simp [routePCoprimeSquareWeight_eq_zero_of_one_le hny]

end RHTower
