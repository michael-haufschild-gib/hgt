import GaloisForLFunctions.RHTower.CHMDCompactStationaryJump
import GaloisForLFunctions.RHTower.CHMDWeakCoreAdmission
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth compact approximation in the complete arithmetic jump graph

Normalized convolution controls the stationary archimedean norm. Together with
finite full-prime mass and weak closedness, this admits bounded compact maximal
domain functions into the actual compact C2 core.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped Convolution
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump WeilOneSided
open GaloisForLFunctions.HTGeometry

def mollifier (n : ℕ) : ℝ → ℝ := (narrowBump n).normed volume
def smooth (v : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := lineConvolution (mollifier n) v

theorem mollifier_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mollifier n x := (narrowBump n).nonneg_normed x
theorem mollifier_contDiff (n : ℕ) : ContDiff ℝ 2 (mollifier n) := (narrowBump n).contDiff_normed
theorem mollifier_compact (n : ℕ) : HasCompactSupport (mollifier n) := (narrowBump n).hasCompactSupport_normed
theorem mollifier_integrable (n : ℕ) : Integrable (mollifier n) :=
  (mollifier_contDiff n).continuous.integrable_of_hasCompactSupport (mollifier_compact n)
theorem mollifier_integral (n : ℕ) : ∫ x, mollifier n x = 1 := (narrowBump n).integral_normed

theorem smooth_contDiff {v : ℝ → ℝ} (h2 : MemLp v 2 volume) (n : ℕ) : ContDiff ℝ 2 (smooth v n) :=
  (mollifier_compact n).contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifier_contDiff n) (h2.locallyIntegrable (by norm_num))

theorem smooth_compact {v : ℝ → ℝ} (hc : HasCompactSupport v) (n : ℕ) : HasCompactSupport (smooth v n) :=
  (mollifier_compact n).convolution (lsmul ℝ ℝ) hc

theorem integrable_mollifier_mul {v : ℝ → ℝ} (hv : Measurable v) {M : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, |v x| ≤ M) (n : ℕ) (x : ℝ) : Integrable (fun a => mollifier n a * v (x - a)) := by
  apply ((mollifier_integrable n).mul_const M).mono'
    (((mollifier_contDiff n).continuous.measurable).mul (hv.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  exact Eventually.of_forall fun a => by
    change ‖mollifier n a * v (x - a)‖ ≤ mollifier n a * M
    rw [norm_mul, Real.norm_of_nonneg (mollifier_nonneg n a), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb _) (mollifier_nonneg n a)

theorem smooth_bound {v : ℝ → ℝ} {M : ℝ} (_hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M) (n : ℕ) (x : ℝ) :
    |smooth v n x| ≤ M := by
  have h := norm_integral_le_of_norm_le ((mollifier_integrable n).mul_const M)
    (Eventually.of_forall fun a => show ‖mollifier n a * v (x - a)‖ ≤ mollifier n a * M from by
      rw [norm_mul, Real.norm_of_nonneg (mollifier_nonneg n a), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb _) (mollifier_nonneg n a))
  simpa only [smooth, lineConvolution, Real.norm_eq_abs, integral_mul_const, mollifier_integral, one_mul] using h

theorem difference_smooth {v : ℝ → ℝ} (hv : Measurable v) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |v x| ≤ M) (n : ℕ) (t x : ℝ) :
    smooth v n x - smooth v n (x + t) =
      lineConvolution (mollifier n) (fun y => v y - v (y + t)) x := by
  change (∫ a, mollifier n a * v (x - a)) - (∫ a, mollifier n a * v (x + t - a)) =
    ∫ a, mollifier n a * (v (x - a) - v (x - a + t))
  rw [← integral_sub (integrable_mollifier_mul hv hM hb n x) (integrable_mollifier_mul hv hM hb n (x + t))]
  apply integral_congr_ae
  filter_upwards with a
  rw [show x + t - a = x - a + t by ring]
  ring

theorem smooth_difference_L2_le {v : ℝ → ℝ} (hv : Measurable v) (hc : HasCompactSupport v)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M) (n : ℕ) (t : ℝ) :
    (∫ x, (smooth v n x - smooth v n (x + t)) ^ 2) ≤ ∫ x, (v x - v (x + t)) ^ 2 := by
  have hv2 := bounded_compact_memLp_volume hv hc hM hb
  have hs2 := bounded_compact_memLp_volume (smooth_contDiff hv2 n).continuous.measurable
    (smooth_compact hc n) hM (smooth_bound hM hb n)
  have hshift (f : ℝ → ℝ) (hf : MemLp f 2 volume) : MemLp (fun x => f x - f (x + t)) 2 volume :=
    hf.sub (hf.comp_measurePreserving (measurePreserving_add_right volume t))
  have hrho : Integrable (fun a => |mollifier n a|) := by
    simpa only [Real.norm_eq_abs] using (mollifier_integrable n).norm
  have hi := integral_sq_lineConvolution_le (u := fun x => v x - v (x + t))
    (mollifier_contDiff n).continuous.measurable
    (hv.sub (hv.comp (measurable_id.add_const t))) hrho (hshift v hv2).integrable_sq
    (by simpa only [← difference_smooth hv hM hb n t] using (hshift (smooth v n) hs2).integrable_sq)
  have hr : (∫ a, |mollifier n a|) = 1 := by
    simpa only [abs_of_nonneg (mollifier_nonneg n _)] using mollifier_integral n
  simpa only [← difference_smooth hv hM hb n t, hr, one_pow, one_mul] using hi

theorem stationaryEnergy_smooth_le {v : ℝ → ℝ} (hv : Measurable v) (hc : HasCompactSupport v)
    (hd : MemLp (difference v) 2 edgeMeasure) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |v x| ≤ M) (n : ℕ) : stationaryEnergy (smooth v n) ≤ stationaryEnergy v := by
  have hv2 := bounded_compact_memLp_volume hv hc hM hb
  have hs := smooth_contDiff hv2 n
  have hsc := smooth_compact hc n
  have hsi := integrable_stationaryJump hs.continuous.measurable hsc
    (bounded_compact_memLp_volume hs.continuous.measurable hsc hM (smooth_bound hM hb n))
    (compact_memLp_difference hs hsc)
  have hvi := integrable_stationaryJump hv hc hv2 hd
  rw [stationaryEnergy_eq_iterated hsi, stationaryEnergy_eq_iterated hvi]
  apply integral_mono_ae (integrable_stationary_outer hsi) (integrable_stationary_outer hvi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_mul_of_nonneg_left (smooth_difference_L2_le hv hc hM hb n t) (archLevyDensity_pos ht).le

theorem compactLift_norm_sq_bound {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v)
    {M C B : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M) (hC : 0 ≤ C)
    (hθ : ∀ x, riemannKernelReal x ≤ C) (hB : stationaryEnergy v ≤ B) :
    ‖compactLift v hv hc‖ ^ 2 ≤
      (∫ _ : ℝ, M ^ 2 ∂massMeasure) +
        (C ^ 2 * B + ∫ _ : ℝ × ℝ, 4 * M ^ 2 ∂Measure.sum primeMeasure) := by
  have hvi := integrable_stationaryJump hv.continuous.measurable hc
    (bounded_compact_memLp_volume hv.continuous.measurable hc hM hb) (compact_memLp_difference hv hc)
  have hmass : (∫ x, v x ^ 2 ∂massMeasure) ≤ ∫ _ : ℝ, M ^ 2 ∂massMeasure := by
    apply integral_mono (compact_memLp_mass hv.continuous hc).integrable_sq (integrable_const _)
    intro x
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr (hb x)
  have harch : (∫ e, difference v e ^ 2 ∂archMeasure) ≤ C ^ 2 * B := by
    rw [archMeasure, integral_weighted archBase measurable_archWeight archWeight_nonneg_ae]
    apply le_trans (b := C ^ 2 * stationaryEnergy v) _ (mul_le_mul_of_nonneg_left hB (sq_nonneg C))
    rw [stationaryEnergy, ← integral_const_mul]
    apply integral_mono_ae (integrable_arch_weighted_sq hv hc) (hvi.const_mul _)
    have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [ht] with e he
    have hp := mul_le_mul (hθ e.2) (hθ (e.2 + e.1)) (riemannKernelReal_pos _).le hC
    have hmul := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (archLevyDensity_pos he).le (sq_nonneg (difference v e)))
    dsimp [archWeight, stationaryJump]
    nlinarith only [hmul]
  have hprime : (∫ e, difference v e ^ 2 ∂Measure.sum primeMeasure) ≤
      ∫ _ : ℝ × ℝ, 4 * M ^ 2 ∂Measure.sum primeMeasure := by
    apply integral_mono (integrable_all_prime_sq hv.continuous hc) (integrable_const _)
    intro e
    have habs : |difference v e| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [hb (left e), hb (right e)])
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
  change ‖(compactLift v hv hc).val‖ ^ 2 ≤ _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(compact_memLp_mass hv.continuous hc).toLp v‖ ^ 2 +
    ‖(compact_memLp_difference hv hc).toLp (difference v)‖ ^ 2 ≤ _
  rw [norm_toLp_sq, norm_toLp_sq, edgeMeasure,
    integral_add_measure (integrable_arch_sq hv hc) (integrable_all_prime_sq hv.continuous hc)]
  exact add_le_add hmass (add_le_add harch hprime)

theorem narrowBump_rOut_tendsto : Tendsto (fun n => (narrowBump n).rOut) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi := (tendsto_inv_atTop_zero.comp hn).div_const 4
  simpa only [narrowBump, Function.comp_def, one_div, mul_inv_rev, div_eq_mul_inv, zero_mul, one_mul] using hi

theorem smooth_tendsto_ae {v : ℝ → ℝ} (h2 : MemLp v 2 volume) :
    ∀ᵐ x ∂massMeasure, Tendsto (fun n => smooth v n x) atTop (𝓝 (v x)) := by
  have hr : ∀ᶠ n : ℕ in atTop, (narrowBump n).rOut ≤ 2 * (narrowBump n).rIn :=
    Eventually.of_forall fun n => by
      apply le_of_eq
      dsimp [narrowBump]
      field_simp
      ring
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℝ)) narrowBump_rOut_tendsto hr (h2.locallyIntegrable (by norm_num))
  exact h.filter_mono (withDensity_absolutelyContinuous volume _).ae_le

/-- Rough bounded compact domain vectors belong to the actual compact C2 completion. -/
theorem bounded_compact_mem_core (v : ℝ → ℝ) (hv : Measurable v) (hc : HasCompactSupport v)
    (hs : MemLp v 2 massMeasure) (hd : MemLp (difference v) 2 edgeMeasure)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |v x| ≤ M) :
    ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right v hs hd ∈ compactCore := by
  have hv2 := bounded_compact_memLp_volume hv hc hM hb
  let u : ℕ → SourceGraph := fun n => compactLift (smooth v n) (smooth_contDiff hv2 n) (smooth_compact hc n)
  obtain ⟨C, hC, hθ, _⟩ := theta_global_and_exponential_bound
  let B := (∫ _ : ℝ, M ^ 2 ∂massMeasure) +
    (C ^ 2 * stationaryEnergy v + ∫ _ : ℝ × ℝ, 4 * M ^ 2 ∂Measure.sum primeMeasure)
  have hnorm (n : ℕ) : ‖u n‖ ≤ Real.sqrt B := by
    have hh := compactLift_norm_sq_bound (smooth_contDiff hv2 n) (smooth_compact hc n)
      hM (smooth_bound hM hb n) hC hθ (stationaryEnergy_smooth_le hv hc hd hM hb n)
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hh
  apply mem_core_of_bounded_source_approx _ u
    (fun n => compactLift_mem_core _ _ _) (Real.sqrt B) hnorm
  apply toLp_tendsto_of_sq_dom
    (fun n => compact_memLp_mass (smooth_contDiff hv2 n).continuous (smooth_compact hc n))
    hs (integrable_const (4 * M ^ 2))
  · intro n
    filter_upwards with x
    have ha : |smooth v n x - v x| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [smooth_bound hM hb n x, hb x])
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr ha
  · exact smooth_tendsto_ae hv2

end RHTower.CHMDDoobGraph
