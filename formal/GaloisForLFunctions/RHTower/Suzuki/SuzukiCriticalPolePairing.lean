import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalTranslatedCusp
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalLogKernel
import Mathlib.Analysis.Convolution

/-!
# Compact testing of the critical Suzuki pole convolution

The growing pole exponential is cut off only after multiplication by the compact
test. The primary density is used in `L¹`; its square need not be integrable.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower

noncomputable section

/-- The causal pole convolution paired with a translated autocorrelation. -/
def suzukiCriticalPoleCusp (f : ℝ → ℝ) (omega u : ℝ) : ℝ :=
  ∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalPoleDensity omega t

/-- The full literal archimedean kernel paired with a translated autocorrelation. -/
def suzukiCriticalSourceCusp (f : ℝ → ℝ) (omega u : ℝ) : ℝ :=
  ∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalSourceDensity omega t

private def primaryRay (omega : ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (suzukiCriticalPrimaryDensity omega)

private def poleWindow (omega A : ℝ) : ℝ → ℝ :=
  (Ioo (0 : ℝ) A).indicator (fun s => Real.exp ((1 / 2 - omega) * s))

private theorem primaryRay_integrable {omega : ℝ}
    (homega : 0 < omega) (homega5 : omega < 5 / 2) : Integrable (primaryRay omega) :=
  (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_suzukiCriticalPrimaryDensity homega homega5)

private theorem poleWindow_integrable (omega A : ℝ) : Integrable (poleWindow omega A) := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  have hc : Continuous (fun s : ℝ => Real.exp ((1 / 2 - omega) * s)) := by fun_prop
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem tested_convolution_integrable {b p C : ℝ → ℝ} {R : ℝ}
    (hb : Integrable b) (hp : Integrable p) (hC : Measurable C)
    (hCb : ∀ t, |C t| ≤ R) :
    Integrable (fun t => C t * ∫ r, b r * p (t - r)) := by
  have hc := hb.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hp
  have hm := hc.bdd_mul hC.aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hCb t)
  simpa only [convolution_def, ContinuousLinearMap.mul_apply'] using hm

private theorem tested_convolution_eq {b p C : ℝ → ℝ} {R : ℝ}
    (hb : Integrable b) (hp : Integrable p) (hC : Measurable C)
    (hCb : ∀ t, |C t| ≤ R) :
    (∫ t, C t * ∫ r, b r * p (t - r)) =
      ∫ s, p s * ∫ r, C (s + r) * b r := by
  have hj := hp.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hb
  have hF : Integrable (fun q : ℝ × ℝ => C q.1 * (p q.2 * b (q.1 - q.2)))
      (volume.prod volume) := by
    have h := hj.bdd_mul (hC.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun q => by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using hCb q.1)
    simpa only [ContinuousLinearMap.mul_apply', Function.comp_apply] using h
  have hflip (t : ℝ) : (∫ r, b r * p (t - r)) = ∫ s, p s * b (t - s) := by
    rw [← integral_sub_left_eq_self (fun r => b r * p (t - r)) volume t]
    apply integral_congr_ae
    filter_upwards with s
    rw [sub_sub_cancel]
    ring
  calc
    _ = ∫ t, ∫ s, C t * (p s * b (t - s)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hflip, integral_const_mul]
    _ = ∫ s, ∫ t, C t * (p s * b (t - s)) := integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_add_right_eq_self (fun t => C t * (p s * b (t - s))) s,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      rw [add_sub_cancel_right]
      simp only [add_comm s r]
      ring

private theorem window_convolution_eq_pole {omega A t : ℝ} (ht : t ≤ A) :
    (∫ r, primaryRay omega r * poleWindow omega A (t - r)) =
      suzukiCriticalPoleDensity omega t := by
  rw [suzukiCriticalPoleDensity, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : 0 < r
  · by_cases hrt : r < t
    · have htr : t - r ∈ Ioo (0 : ℝ) A := ⟨by linarith, by linarith⟩
      simp only [primaryRay, poleWindow,
        indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr), indicator_of_mem htr,
        indicator_of_mem (show r ∈ Ioo (0 : ℝ) t from ⟨hr, hrt⟩)]
    · have htr : t - r ∉ Ioo (0 : ℝ) A := fun h => hrt (by linarith [h.1])
      have hnot : r ∉ Ioo (0 : ℝ) t := fun h => hrt h.2
      simp only [poleWindow, indicator_of_notMem htr, indicator_of_notMem hnot, mul_zero]
  · have hnot : r ∉ Ioo (0 : ℝ) t := fun h => hr h.1
    simp only [primaryRay, indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
      indicator_of_notMem hnot, zero_mul]

private theorem tested_window_eq_indicator {f : ℝ → ℝ} {A u : ℝ}
    (hA : 0 < A) (hu : 0 ≤ u)
    (hcut : ∀ t, A ≤ t → autocorr f t = 0) (omega t : ℝ) :
    autocorr f (u + t) * (∫ r, primaryRay omega r * poleWindow omega A (t - r)) =
      (Ioi (0 : ℝ)).indicator
        (fun t => autocorr f (u + t) * suzukiCriticalPoleDensity omega t) t := by
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    by_cases htop : t ≤ A
    · rw [window_convolution_eq_pole htop]
    · have hz := hcut (u + t) (by linarith)
      rw [hz, zero_mul, zero_mul]
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
      window_convolution_eq_pole (by linarith : t ≤ A),
      suzukiCriticalPoleDensity]
    have hempty : Ioo (0 : ℝ) t = ∅ := Ioo_eq_empty_of_le (le_of_not_gt ht)
    rw [hempty]
    simp

/-- Absolute integrability of the compactly tested pole term, at every positive small shift. -/
theorem integrableOn_suzukiCriticalPoleCusp_integrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {A u omega : ℝ}
    (hA : 0 < A) (hu : 0 ≤ u) (hcut : ∀ t, A ≤ t → autocorr f t = 0)
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    IntegrableOn (fun t => autocorr f (u + t) * suzukiCriticalPoleDensity omega t) (Ioi 0) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mp
  have hc : Measurable (fun t : ℝ => autocorr f (u + t)) :=
    ((continuous_autocorr hf hfc).comp (continuous_const.add continuous_id)).measurable
  have hi := tested_convolution_integrable
    (primaryRay_integrable homega homega5) (poleWindow_integrable omega A)
    hc
    (fun t => abs_autocorr_le_zero hfc hf.continuous (u + t))
  exact hi.congr (Eventually.of_forall (tested_window_eq_indicator hA hu hcut omega))

/-- Fubini on the compact test transports the pole onto the primary translated cusps. -/
theorem suzukiCriticalPoleCusp_eq_integral_primaryCusp {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {A u omega : ℝ}
    (hA : 0 < A) (hu : 0 ≤ u) (hcut : ∀ t, A ≤ t → autocorr f t = 0)
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    suzukiCriticalPoleCusp f omega u =
      ∫ s in Ioo 0 A, Real.exp ((1 / 2 - omega) * s) *
        suzukiCriticalPrimaryCusp f omega (u + s) := by
  have hc : Measurable (fun t : ℝ => autocorr f (u + t)) :=
    ((continuous_autocorr hf hfc).comp (continuous_const.add continuous_id)).measurable
  have he := tested_convolution_eq
    (primaryRay_integrable homega homega5) (poleWindow_integrable omega A)
    hc
    (fun t => abs_autocorr_le_zero hfc hf.continuous (u + t))
  have hleft : (∫ t, autocorr f (u + t) *
      (∫ r, primaryRay omega r * poleWindow omega A (t - r))) =
      suzukiCriticalPoleCusp f omega u := by
    rw [suzukiCriticalPoleCusp, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact Eventually.of_forall (tested_window_eq_indicator hA hu hcut omega)
  rw [hleft] at he
  rw [he, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ioo (0 : ℝ) A
  · rw [poleWindow, indicator_of_mem hs, indicator_of_mem hs]
    congr 1
    rw [suzukiCriticalPrimaryCusp, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · simp only [primaryRay, indicator_of_mem hr, add_assoc]
    · simp only [primaryRay, indicator_of_notMem hr, mul_zero]
  · simp only [poleWindow, indicator_of_notMem hs, zero_mul]

/-- The exact signed decomposition survives compact testing; both terms are absolutely integrable. -/
theorem suzukiCriticalSourceCusp_eq {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {A u omega : ℝ}
    (hA : 0 < A) (hu : 0 ≤ u) (hcut : ∀ t, A ≤ t → autocorr f t = 0)
    (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    suzukiCriticalSourceCusp f omega u = suzukiCriticalPrimaryCusp f omega u -
      2 * omega * suzukiCriticalPoleCusp f omega u := by
  have hiB := integrableOn_suzukiCriticalPrimaryCusp_integrand hf hfc homega homega5 u
  have hiP := integrableOn_suzukiCriticalPoleCusp_integrand hf hfc hA hu hcut homega homega5
  unfold suzukiCriticalSourceCusp suzukiCriticalPrimaryCusp suzukiCriticalPoleCusp
  calc
    _ = ∫ t in Ioi 0, autocorr f (u + t) * suzukiCriticalPrimaryDensity omega t -
        (2 * omega) * (autocorr f (u + t) * suzukiCriticalPoleDensity omega t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [suzukiCriticalSourceDensity_eq omega ht]
      ring
    _ = _ := by rw [integral_sub hiB (hiP.const_mul _), integral_const_mul]

private theorem poleWindow_pairing_tendsto {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (A u : ℝ) :
    Tendsto (fun omega : ℝ => ∫ s in Ioo 0 A,
      Real.exp ((1 / 2 - omega) * s) * suzukiCriticalPrimaryCusp f omega (u + s))
      (𝓝[>] 0) (𝓝 (∫ s in Ioo 0 A, Real.exp (s / 2) * autocorr f (u + s))) := by
  have hR := GaloisForLFunctions.BiScaleUncertainty.autocorr_zero_nonneg f
  have hm : ∀ᶠ omega in 𝓝[>] (0 : ℝ), suzukiCriticalPrimaryMass omega < 2 :=
    (tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => Real.exp (A / 2) * (2 * autocorr f 0))
  · exact Eventually.of_forall fun omega =>
      ((show Measurable (fun s : ℝ => Real.exp ((1 / 2 - omega) * s)) by fun_prop).mul
        ((measurable_suzukiCriticalPrimaryCusp hf hfc omega).comp
          (measurable_const.add measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, ho, hm] with omega homega ho hm
    change 0 < omega at homega
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hb := abs_suzukiCriticalPrimaryCusp_le hf hfc homega (by linarith) (u + s)
    have he : Real.exp ((1 / 2 - omega) * s) ≤ Real.exp (A / 2) := by
      apply Real.exp_le_exp.mpr
      have hos : 0 ≤ omega * s := mul_nonneg homega.le hs.1.le
      nlinarith only [hos, hs.2]
    have hb' : |suzukiCriticalPrimaryCusp f omega (u + s)| ≤ 2 * autocorr f 0 :=
      hb.trans (mul_le_mul_of_nonneg_right hm.le hR)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he hb' (abs_nonneg _) (Real.exp_pos _).le
  · exact (continuous_const.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards with s
    have he : Tendsto (fun omega : ℝ => Real.exp ((1 / 2 - omega) * s))
        (𝓝[>] 0) (𝓝 (Real.exp (s / 2))) := by
      have hc : Continuous (fun omega : ℝ => Real.exp ((1 / 2 - omega) * s)) := by fun_prop
      have heq : (1 / 2 - (0 : ℝ)) * s = s / 2 := by ring
      simpa only [heq] using
        (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact he.mul ((tendstoUniformly_suzukiCriticalPrimaryCusp hf hfc).tendsto_at (u + s))

/-- The tested pole convolution converges to its growing critical exponential. -/
theorem tendsto_suzukiCriticalPoleCusp {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {A u : ℝ}
    (hA : 0 < A) (hu : 0 ≤ u) (hcut : ∀ t, A ≤ t → autocorr f t = 0) :
    Tendsto (fun omega : ℝ => suzukiCriticalPoleCusp f omega u) (𝓝[>] 0)
      (𝓝 (∫ s in Ioi 0, Real.exp (s / 2) * autocorr f (u + s))) := by
  have hcutint : (∫ s in Ioi 0, Real.exp (s / 2) * autocorr f (u + s)) =
      ∫ s in Ioo 0 A, Real.exp (s / 2) * autocorr f (u + s) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ hs => hs.1)
    intro s hs
    have hsA : A ≤ s := le_of_not_gt (fun h => hs.2 ⟨hs.1, h⟩)
    rw [hcut (u + s) (by linarith), mul_zero]
  rw [hcutint]
  apply (poleWindow_pairing_tendsto hf hfc A u).congr'
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  exact (suzukiCriticalPoleCusp_eq_integral_primaryCusp hf hfc hA hu hcut homega (by linarith)).symm

/-- Compact source support supplies a positive cutoff for its correlation. -/
theorem exists_pos_autocorr_cutoff {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ A : ℝ, 0 < A ∧ ∀ t, A ≤ t → autocorr f t = 0 := by
  have hc : IsCompact (tsupport (autocorr f)) := hasCompactSupport_autocorr hfc
  obtain ⟨M, hM⟩ := hc.bddAbove
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro t ht
  by_contra hne
  have hmem : t ∈ tsupport (autocorr f) := subset_closure (Function.mem_support.mpr hne)
  have hb := hM hmem
  linarith [le_abs_self M]

/-- Compact support makes the complete signed cusp absolutely integrable. -/
theorem integrableOn_suzukiCriticalSourceCusp_integrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {u omega : ℝ}
    (hu : 0 ≤ u) (homega : 0 < omega) (homega5 : omega < 5 / 2) :
    IntegrableOn (fun t => autocorr f (u + t) * suzukiCriticalSourceDensity omega t)
      (Ioi 0) := by
  obtain ⟨A, hA, hcut⟩ := exists_pos_autocorr_cutoff hfc
  have hiB := integrableOn_suzukiCriticalPrimaryCusp_integrand hf hfc homega homega5 u
  have hiP := integrableOn_suzukiCriticalPoleCusp_integrand hf hfc hA hu hcut homega homega5
  apply (hiB.sub (hiP.const_mul (2 * omega))).congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.sub_apply]
  rw [suzukiCriticalSourceDensity_eq omega ht]
  ring

/-- Every nonnegative translated cusp of the full signed source tends to the correlation. -/
theorem tendsto_suzukiCriticalSourceCusp {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun omega : ℝ => suzukiCriticalSourceCusp f omega u)
      (𝓝[>] 0) (𝓝 (autocorr f u)) := by
  obtain ⟨A, hA, hcut⟩ := exists_pos_autocorr_cutoff hfc
  have hp := tendsto_suzukiCriticalPoleCusp hf hfc hA hu hcut
  have hi : Tendsto (fun omega : ℝ => omega) (𝓝[>] 0) (𝓝 0) := continuousWithinAt_id
  have h := ((tendstoUniformly_suzukiCriticalPrimaryCusp hf hfc).tendsto_at u).sub
    ((hi.const_mul 2).mul hp)
  simp only [mul_zero, zero_mul, sub_zero] at h
  apply h.congr'
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  exact (suzukiCriticalSourceCusp_eq hf hfc hA hu hcut homega (by linarith)).symm

/-- The full literal archimedean source has its critical first variation, including
the growing pole. Compact support supplies the aperture; no pole integrability is assumed. -/
theorem tendsto_suzukiCriticalSourceCusp_firstVariation {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun omega : ℝ =>
      (suzukiCriticalSourceCusp f omega 0 - autocorr f 0) / omega)
      (𝓝[>] 0)
      (𝓝 (((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) -
        2 * ∫ t in Ioi 0, Real.exp (t / 2) * autocorr f t)) := by
  obtain ⟨A, hA, hcut⟩ := exists_pos_autocorr_cutoff hfc
  have hp := tendsto_suzukiCriticalPoleCusp hf hfc hA (le_refl (0 : ℝ)) hcut
  simp only [zero_add] at hp
  have h := (tendsto_suzukiCriticalPrimaryCusp_firstVariation hf hfc).sub (hp.const_mul 2)
  apply h.congr'
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  change 0 < omega at homega
  rw [suzukiCriticalSourceCusp_eq hf hfc hA (le_refl (0 : ℝ)) hcut homega (by linarith)]
  field_simp [ne_of_gt homega]
  ring

end
end RHTower
