import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothArithmeticCellSections
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# Smooth arithmetic sections recover the whole Weil form

One pole-preserving operator realizes every complete-cell vector as an original
compact C² test. The limit retains the Gamma jump form, every prime translation,
and both signed pole terms.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
open _root_.RHTower hiding mollifier
open _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry SpacingScaleHarmonicAnalysis

theorem integrable_compact_bv_mul {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable (fun x => f x * w x) := by
  have hon := (memLp_compact_bv hv hc).locallyIntegrable (by norm_num) |>.integrableOn_isCompact hc
  have hp := hon.mul_continuousOn hw.continuousOn hc
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left f w).trans (subset_tsupport _))).mp hp

theorem halfMoments_eq_exp {f : ℝ → ℝ}
    (hp : Integrable (fun x => Real.exp (x / 2) * f x))
    (hm : Integrable (fun x => Real.exp (-(x / 2)) * f x)) :
    coshHalfMoment f = ((∫ x, Real.exp (x / 2) * f x) +
      ∫ x, Real.exp (-(x / 2)) * f x) / 2 ∧
    sinhHalfMoment f = ((∫ x, Real.exp (x / 2) * f x) -
      ∫ x, Real.exp (-(x / 2)) * f x) / 2 := by
  constructor
  · have he (x : ℝ) : f x * Real.cosh (x / 2) =
        (Real.exp (x / 2) * f x + Real.exp (-(x / 2)) * f x) / 2 := by
      rw [Real.cosh_eq]
      ring
    simp only [coshHalfMoment, he, integral_div, integral_add hp hm]
  · have he (x : ℝ) : f x * Real.sinh (x / 2) =
        (Real.exp (x / 2) * f x - Real.exp (-(x / 2)) * f x) / 2 := by
      rw [Real.sinh_eq]
      ring
    simp only [sinhHalfMoment, he, integral_div, integral_sub hp hm]

/-- The two signed pole coordinates are unchanged at every smoothing scale. -/
theorem poleSmooth_halfMoments {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) (n : ℕ) :
    coshHalfMoment (poleSmooth f n) = coshHalfMoment f ∧
      sinhHalfMoment (poleSmooth f n) = sinhHalfMoment f := by
  have hp : Integrable (fun x => Real.exp (x / 2) * f x) := by
    simpa only [Function.comp_apply, id_eq, Pi.neg_apply, mul_comm] using integrable_compact_bv_mul hv hc
      (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hm : Integrable (fun x => Real.exp (-(x / 2)) * f x) := by
    simpa only [Function.comp_apply, id_eq, Pi.neg_apply, mul_comm] using integrable_compact_bv_mul hv hc
      (Real.continuous_exp.comp (continuous_id.div_const 2).neg)
  have hsc := poleSmooth_compact hc n
  have hsd := poleSmooth_contDiff (memLp_compact_bv hv hc) n
  have hsp : Integrable (fun x => Real.exp (x / 2) * poleSmooth f n x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hsd.continuous).integrable_of_hasCompactSupport
      hsc.mul_left
  have hsm : Integrable (fun x => Real.exp (-(x / 2)) * poleSmooth f n x) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2).neg).mul hsd.continuous).integrable_of_hasCompactSupport
      hsc.mul_left
  have he := poleSmooth_expMoments hp hm n
  exact ⟨by rw [(halfMoments_eq_exp hsp hsm).1, he.1, he.2, (halfMoments_eq_exp hp hm).1],
    by rw [(halfMoments_eq_exp hsp hsm).2, he.1, he.2, (halfMoments_eq_exp hp hm).2]⟩

theorem mollifier_support_abs_le (n : ℕ) {x : ℝ} (hx : mollifier n x ≠ 0) :
    |x| ≤ 1 / 4 := by
  have hx' : x ∈ Function.support ((WeilOneSided.narrowBump n).normed volume) := hx
  rw [(WeilOneSided.narrowBump n).support_normed_eq] at hx'
  have hd : |x| < 1 / (4 * ((n : ℝ) + 1)) := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, WeilOneSided.narrowBump] using hx'
  refine hd.le.trans (one_div_le_one_div_of_le (by norm_num) ?_)
  nlinarith only [Nat.cast_nonneg (α := ℝ) n]

theorem poleSmooth_supported {f : ℝ → ℝ} {R : ℝ} (hR : SupportedIn R f) (n : ℕ) :
    SupportedIn (R + 1 / 2) (poleSmooth f n) := by
  intro x hx
  suffices smooth f n x = 0 by simp only [poleSmooth, this, mul_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : mollifier n t = 0
  · simp only [ht, zero_mul, Pi.zero_apply]
  · have hb := mollifier_support_abs_le n ht
    have he : |x| ≤ |x - t| + |t| := by
      simpa only [sub_add_cancel] using abs_add_le (x - t) t
    have hx' : R < |x - t| := by linarith only [hb, he, hx]
    simp only [hR (x - t) hx', mul_zero, Pi.zero_apply]

theorem volume_shift_inner_of_ae {f : ℝ → ℝ} (u : StationaryVolumeSpace)
    (hu : u =ᵐ[volume] f) (t : ℝ) :
    ⟪u, volumeTranslate t u⟫_ℝ = ∫ x, f x * f (x + t) := by
  rw [volume_inner_realLp]
  apply integral_congr_ae
  filter_upwards [hu, volumeTranslate_ae t u,
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hu]
    with x hx ht hx'
  rw [hx, ht, hx']

theorem tendsto_poleSmooth_correlation {f : ℝ → ℝ} (hf : MemLp f 2 volume) (t : ℝ) :
    Tendsto (fun n => ∫ x, poleSmooth f n x * poleSmooth f n (x + t)) atTop
      (𝓝 (∫ x, f x * f (x + t))) := by
  have h := volumePoleSmooth_tendsto (hf.toLp f)
  have hi : Tendsto (fun n => ⟪volumePoleSmooth n (hf.toLp f),
      volumeTranslate t (volumePoleSmooth n (hf.toLp f))⟫_ℝ) atTop
      (𝓝 ⟪hf.toLp f, volumeTranslate t (hf.toLp f)⟫_ℝ) :=
    h.inner ((volumeTranslate t).continuous.tendsto (hf.toLp f) |>.comp h)
  simpa only [Function.comp_apply, volume_shift_inner_of_ae _ (volumePoleSmooth_ae hf _) t,
    volume_shift_inner_of_ae _ hf.coeFn_toLp t] using hi

/-- The finite active prime horizon is common to all smoothing scales. -/
theorem tendsto_poleSmooth_primeSum {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {R : ℝ} (hR : SupportedIn R f) :
    Tendsto (fun n => primeSum (poleSmooth f n)) atTop (𝓝 (primeSum f)) := by
  have hfR : SupportedIn (R + 1 / 2) f := fun x hx => hR x (by linarith)
  simp_rw [primeSum_eq_sum_of_supportedIn (poleSmooth_supported hR _),
    primeSum_eq_sum_of_supportedIn hfR]
  apply tendsto_finsetSum
  intro k _
  apply tendsto_const_nhds.mul
  have hm := tendsto_poleSmooth_correlation hf (-Real.log k)
  have hp := tendsto_poleSmooth_correlation hf (Real.log k)
  simpa only [sub_eq_add_neg] using hm.add hp

/-- The full signed arithmetic form evaluated directly on a compact BV source. -/
def roughWeil (f : ℝ → ℝ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ x, f x ^ 2) + levyEnergy f - primeSum f +
    (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)

/-- Smooth regularization recovers all terms of the original Weil form. -/
theorem tendsto_poleSmooth_weilQuad {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) {R : ℝ} (hR : SupportedIn R f) :
    Tendsto (fun n => weilQuad (poleSmooth f n)) atTop (𝓝 (roughWeil f)) := by
  have hf2 := memLp_compact_bv hv hc
  have hs (n : ℕ) : weilQuad (poleSmooth f n) =
      2 * gammaHardyPhaseRate 0 * (∫ x, poleSmooth f n x ^ 2) +
        levyEnergy (poleSmooth f n) - primeSum (poleSmooth f n) +
          (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
    rw [weilQuad_eq (poleSmooth_contDiff hf2 n) (poleSmooth_compact hc n),
      (poleSmooth_halfMoments hv hc n).1, (poleSmooth_halfMoments hv hc n).2]
  simp_rw [hs]
  exact (((tendsto_const_nhds.mul (tendsto_poleSmooth_square_mass hf2)).add
    (tendsto_poleSmooth_levyEnergy hv hc)).sub
    (tendsto_poleSmooth_primeSum hf2 hR)).add tendsto_const_nhds

theorem rawSection_supported {X : ℕ} (c : Fin X → ℝ) :
    SupportedIn (Real.log (X + 1 : ℕ)) (rawSection c) := by
  intro x hx
  apply Finset.sum_eq_zero
  intro i _
  have hn : x ∉ Ico (Real.log (i.val + 1 : ℕ)) (Real.log (i.val + 1 + 1 : ℕ)) := by
    intro hi
    have h0 : 0 ≤ Real.log (i.val + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val))
    have hhi : Real.log (i.val + 1 + 1 : ℕ) ≤ Real.log (X + 1 : ℕ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show i.val + 1 + 1 ≤ X + 1 by omega)
    rw [abs_of_nonneg (h0.trans hi.1)] at hx
    exact (not_lt_of_ge (hi.2.trans_le hhi).le) hx
  rw [rawCell, indicator_of_notMem hn, mul_zero]

/-- Every coefficient vector has genuine smooth sections with exact pole degrees
and convergence in the original full Weil form. -/
theorem complete_cells_smooth_realization {X : ℕ} (c : Fin X → ℝ) :
    (∀ n, ContDiff ℝ 2 (poleSmooth (rawSection c) n) ∧
      HasCompactSupport (poleSmooth (rawSection c) n) ∧
      coshHalfMoment (poleSmooth (rawSection c) n) = coshHalfMoment (rawSection c) ∧
      sinhHalfMoment (poleSmooth (rawSection c) n) = sinhHalfMoment (rawSection c)) ∧
    Tendsto (fun n => ∫ x, (poleSmooth (rawSection c) n x - rawSection c x) ^ 2)
      atTop (𝓝 0) ∧
    Tendsto (fun n => weilQuad (poleSmooth (rawSection c) n)) atTop
      (𝓝 (roughWeil (rawSection c))) := by
  have hv := rawSection_bv c
  have hc := rawSection_compact c
  have hf2 := memLp_compact_bv hv hc
  refine ⟨fun n => ⟨poleSmooth_contDiff hf2 n, poleSmooth_compact hc n, ?_⟩,
    tendsto_poleSmooth_L2_error hf2, tendsto_poleSmooth_weilQuad hv hc (rawSection_supported c)⟩
  exact poleSmooth_halfMoments hv hc n

#print axioms poleSmooth_halfMoments
#print axioms tendsto_poleSmooth_primeSum
#print axioms tendsto_poleSmooth_weilQuad
#print axioms complete_cells_smooth_realization

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
