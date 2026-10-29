import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EndpointDecayRemovesTheCrossKernelGapLoss

/-!
# Absolute-mass continuity of the actual separated cross term

The autocorrelation difference is paid by the absolute mass of the profile
difference. Fubini is justified before integrating the bounded separated
archimedean density. Every sign of both profiles is retained.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis
open _root_.RHTower (archLevyDensity)

private theorem integrable_mixed_shift_prod {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (Function.uncurry fun z u => f u * g (u + z)) (volume.prod volume) := by
  have h := integrable_mul_shift_prod (hf.abs.add hg.abs) (hfc.norm.add hgc.norm)
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
  change ‖f p.2 * g (p.2 + p.1)‖ ≤
    (|f p.2| + |g p.2|) * (|f (p.2 + p.1)| + |g (p.2 + p.1)|)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_add_of_nonneg_right (abs_nonneg _))
    (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg _)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The actual autocorrelation has the quadratic absolute-mass modulus. -/
theorem integral_abs_bumpAutocorr_sub_le {f g : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ z, |bumpAutocorr f z - bumpAutocorr g z|) ≤
      (∫ u, |f u - g u|) * ((∫ u, |f u|) + ∫ u, |g u|) := by
  let d : ℝ → ℝ := fun u => f u - g u
  have hd : Continuous d := hf.sub hg
  have hdc : HasCompactSupport d := hfc.sub hgc
  have hp := integrable_mixed_shift_prod hd.abs hdc.norm hf.abs hfc.norm
  have hq := integrable_mixed_shift_prod hg.abs hgc.norm hd.abs hdc.norm
  have hGf : Integrable (bumpAutocorr f) := (integrable_mul_shift_prod hf hfc).integral_prod_left
  have hGg : Integrable (bumpAutocorr g) := (integrable_mul_shift_prod hg hgc).integral_prod_left
  have hpoint : ∀ z, |bumpAutocorr f z - bumpAutocorr g z| ≤
      (∫ u, |d u| * |f (u + z)|) + ∫ u, |g u| * |d (u + z)| := by
    intro z
    have hff : Integrable fun u => f u * f (u + z) :=
      (hf.mul (hf.comp (continuous_add_const z))).integrable_of_hasCompactSupport hfc.mul_right
    have hgg : Integrable fun u => g u * g (u + z) :=
      (hg.mul (hg.comp (continuous_add_const z))).integrable_of_hasCompactSupport hgc.mul_right
    have hpf : Integrable fun u => |d u| * |f (u + z)| :=
      (hd.abs.mul (hf.abs.comp (continuous_add_const z))).integrable_of_hasCompactSupport hdc.norm.mul_right
    have hqg : Integrable fun u => |g u| * |d (u + z)| :=
      (hg.abs.mul (hd.abs.comp (continuous_add_const z))).integrable_of_hasCompactSupport hgc.norm.mul_right
    unfold bumpAutocorr
    rw [← integral_sub hff hgg, ← integral_add hpf hqg]
    refine abs_integral_le_integral_abs.trans (integral_mono (hff.sub hgg).abs (hpf.add hqg) ?_)
    intro u
    rw [show f u * f (u + z) - g u * g (u + z) =
      d u * f (u + z) + g u * d (u + z) by dsimp only [d]; ring]
    simpa only [abs_mul] using abs_add_le (d u * f (u + z)) (g u * d (u + z))
  calc
    _ ≤ ∫ z, ((∫ u, |d u| * |f (u + z)|) + ∫ u, |g u| * |d (u + z)|) :=
      integral_mono (hGf.sub hGg).abs (hp.integral_prod_left.add hq.integral_prod_left) hpoint
    _ = (∫ z, ∫ u, |d u| * |f (u + z)|) + ∫ z, ∫ u, |g u| * |d (u + z)| :=
      integral_add hp.integral_prod_left hq.integral_prod_left
    _ = (∫ u, ∫ z, |d u| * |f (u + z)|) + ∫ u, ∫ z, |g u| * |d (u + z)| := by
      rw [integral_integral_swap hp, integral_integral_swap hq]
    _ = _ := by
      have he₁ (u : ℝ) : (∫ z, |d u| * |f (u + z)|) = |d u| * ∫ z, |f z| := by
        rw [integral_const_mul, integral_add_left_eq_self (fun z => |f z|) u]
      have he₂ (u : ℝ) : (∫ z, |g u| * |d (u + z)|) = |g u| * ∫ z, |d z| := by
        rw [integral_const_mul, integral_add_left_eq_self (fun z => |d z|) u]
      simp_rw [he₁, he₂]
      rw [integral_mul_const, integral_mul_const]
      dsimp only [d]
      ring

private theorem autocorr_eq_zero_off_window {g : ℝ → ℝ} {w z : ℝ}
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hz : z ∉ Icc (-w) w) :
    bumpAutocorr g z = 0 := by
  apply bumpAutocorr_eq_zero hsupp
  by_contra h
  exact hz (abs_le.mp (not_lt.mp h))

/-- The literal separated cross integral is the full shifted-density reading. -/
theorem atomCrossTerm_eq_full_shift_integral {g : ℝ → ℝ} {w s : ℝ}
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hws : w < s) :
    atomCrossTerm g s = ∫ z, archLevyDensity (s + z) * bumpAutocorr g z := by
  unfold atomCrossTerm
  rw [← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self
    (fun y => (Ioi (0 : ℝ)).indicator (fun y => archLevyDensity y * bumpAutocorr g (y - s)) y) s]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : z ∈ Icc (-w) w
  · have hpos : z + s ∈ Ioi (0 : ℝ) := by
      show 0 < z + s
      linarith only [hz.1, hws]
    rw [Set.indicator_of_mem hpos, add_sub_cancel_right, add_comm z s]
  · rw [autocorr_eq_zero_off_window hsupp hz, mul_zero]
    by_cases hpos : z + s ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hpos, add_sub_cancel_right,
        autocorr_eq_zero_off_window hsupp hz, mul_zero]
    · rw [Set.indicator_of_notMem hpos]

private theorem integrable_weighted_autocorr {g : ℝ → ℝ} {w s : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hws : w < s) :
    Integrable (fun z => archLevyDensity (s + z) * bumpAutocorr g z) := by
  have hG : Integrable (bumpAutocorr g) := (integrable_mul_shift_prod hg hgc).integral_prod_left
  refine (hG.abs.const_mul (archLevyDensity (s - w))).mono'
    (((_root_.RHTower.measurable_archLevyDensity.comp
      (measurable_const.add measurable_id)).aestronglyMeasurable).mul hG.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : z ∈ Icc (-w) w
  · have hsz : 0 < s + z := by linarith only [hz.1, hws]
    rw [abs_of_pos (archLevyDensity_pos hsz)]
    exact mul_le_mul_of_nonneg_right
      (archLevyDensity_antitoneOn (sub_pos.mpr hws) hsz (by linarith only [hz.1])) (abs_nonneg _)
  · rw [autocorr_eq_zero_off_window hsupp hz, abs_zero, mul_zero, mul_zero]

/-- The original cross term is Lipschitz in absolute profile mass on every
separated pair window. The estimate preserves arbitrary profile signs. -/
theorem abs_atomCrossTerm_sub_le_absolute_mass {f g : ℝ → ℝ} {w s : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hfsupp : ∀ u, u ∉ Icc 0 w → f u = 0)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hws : w < s) :
    |atomCrossTerm f s - atomCrossTerm g s| ≤
      archLevyDensity (s - w) * (∫ u, |f u - g u|) * ((∫ u, |f u|) + ∫ u, |g u|) := by
  have hfi := integrable_weighted_autocorr hf hfc hfsupp hws
  have hgi := integrable_weighted_autocorr hg hgc hgsupp hws
  have hGf : Integrable (bumpAutocorr f) := (integrable_mul_shift_prod hf hfc).integral_prod_left
  have hGg : Integrable (bumpAutocorr g) := (integrable_mul_shift_prod hg hgc).integral_prod_left
  have hD : 0 ≤ archLevyDensity (s - w) := (archLevyDensity_pos (sub_pos.mpr hws)).le
  have hpoint : ∀ z,
      |archLevyDensity (s + z) * bumpAutocorr f z - archLevyDensity (s + z) * bumpAutocorr g z| ≤
        archLevyDensity (s - w) * |bumpAutocorr f z - bumpAutocorr g z| := by
    intro z
    rw [← mul_sub, abs_mul]
    by_cases hz : z ∈ Icc (-w) w
    · have hsz : 0 < s + z := by linarith only [hz.1, hws]
      rw [abs_of_pos (archLevyDensity_pos hsz)]
      exact mul_le_mul_of_nonneg_right
        (archLevyDensity_antitoneOn (sub_pos.mpr hws) hsz (by linarith only [hz.1])) (abs_nonneg _)
    · rw [autocorr_eq_zero_off_window hfsupp hz, autocorr_eq_zero_off_window hgsupp hz,
        sub_self, abs_zero, mul_zero, mul_zero]
  rw [atomCrossTerm_eq_full_shift_integral hfsupp hws,
    atomCrossTerm_eq_full_shift_integral hgsupp hws, ← integral_sub hfi hgi]
  calc
    _ ≤ ∫ z, |archLevyDensity (s + z) * bumpAutocorr f z -
        archLevyDensity (s + z) * bumpAutocorr g z| := abs_integral_le_integral_abs
    _ ≤ ∫ z, archLevyDensity (s - w) * |bumpAutocorr f z - bumpAutocorr g z| :=
      integral_mono (hfi.sub hgi).abs ((hGf.sub hGg).abs.const_mul _) hpoint
    _ = archLevyDensity (s - w) * ∫ z, |bumpAutocorr f z - bumpAutocorr g z| :=
      integral_const_mul _ _
    _ ≤ archLevyDensity (s - w) *
        ((∫ u, |f u - g u|) * ((∫ u, |f u|) + ∫ u, |g u|)) :=
      mul_le_mul_of_nonneg_left (integral_abs_bumpAutocorr_sub_le hf hfc hg hgc) hD
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.integral_abs_bumpAutocorr_sub_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_atomCrossTerm_sub_le_absolute_mass
