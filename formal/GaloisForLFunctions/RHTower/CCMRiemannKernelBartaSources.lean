import GaloisForLFunctions.RHTower.RiemannKernelTailDecayRate
import GaloisForLFunctions.RHTower.SuzukiCCMMixedScrewWeilBridge
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# Truncations of Riemann's kernel as interior sources

For `c > 0` and `w > 0` let `χ_{c,w}(t) = ϑ((c-t)/w) ϑ((c+t)/w)`, built from the canonical smooth
transition `ϑ`. It equals `1` on `|t| ≤ c - w`, vanishes on `|t| ≥ c`, and takes values in
`[0,1]`. The profile `Φ χ_{c,w}`, with Riemann's kernel `Φ > 0`, is a smooth source supported in
`[-c, c]`, hence an interior source at every aperture `a > c` (`bartaSource`).

These are the test vectors of the Barta argument for nonnegative ground states.
-/

open Real Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The cutoff `χ_{c,w}(t) = ϑ((c-t)/w) ϑ((c+t)/w)`. -/
def bartaCutoff (c w t : ℝ) : ℝ :=
  Real.smoothTransition ((c - t) / w) * Real.smoothTransition ((c + t) / w)

theorem contDiff_bartaCutoff (c w : ℝ) {n : ℕ∞} : ContDiff ℝ n (bartaCutoff c w) := by
  unfold bartaCutoff
  have h1 : ContDiff ℝ n fun t : ℝ => (c - t) / w := (contDiff_const.sub contDiff_id).div_const w
  have h2 : ContDiff ℝ n fun t : ℝ => (c + t) / w := (contDiff_const.add contDiff_id).div_const w
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem bartaCutoff_nonneg (c w t : ℝ) : 0 ≤ bartaCutoff c w t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bartaCutoff_le_one (c w t : ℝ) : bartaCutoff c w t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bartaCutoff_eq_one {c w t : ℝ} (hw : 0 < w) (ht : |t| ≤ c - w) : bartaCutoff c w t = 1 := by
  have h1 := neg_abs_le t
  have h2 := le_abs_self t
  unfold bartaCutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hw]; linarith
  · rw [le_div_iff₀ hw]; linarith

theorem bartaCutoff_eq_zero {c w t : ℝ} (hw : 0 < w) (ht : c ≤ |t|) : bartaCutoff c w t = 0 := by
  unfold bartaCutoff
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le),
      zero_mul]
  · rw [abs_of_nonpos h] at ht
    rw [Real.smoothTransition.zero_of_nonpos (x := (c + t) / w)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le), mul_zero]

theorem contDiff_riemannKernelReal {n : ℕ∞} : ContDiff ℝ n riemannKernelReal := by
  have hΦ : ContDiff ℝ n riemannPhiKernel := by
    rw [← riemannKernelDeriv_zero]
    exact (contDiff_infty.mpr fun m => contDiff_riemannKernelDeriv m 0).of_le
      (by exact_mod_cast le_top)
  have h : riemannKernelReal = fun t => (riemannPhiKernel t).re := by
    funext t; rw [riemannPhiKernel_eq_ofReal, Complex.ofReal_re]
  rw [h]
  exact Complex.reCLM.contDiff.comp hΦ

/-- The real profile `Φ χ_{c,w}`. -/
def bartaProfile (c w t : ℝ) : ℝ := riemannKernelReal t * bartaCutoff c w t

theorem contDiff_bartaProfile (c w : ℝ) {n : ℕ∞} : ContDiff ℝ n (bartaProfile c w) :=
  contDiff_riemannKernelReal.mul (contDiff_bartaCutoff c w)

theorem bartaProfile_nonneg (c w t : ℝ) : 0 ≤ bartaProfile c w t :=
  mul_nonneg (riemannKernelReal_pos t).le (bartaCutoff_nonneg c w t)

theorem bartaProfile_le (c w t : ℝ) : bartaProfile c w t ≤ riemannKernelReal t := by
  unfold bartaProfile
  calc riemannKernelReal t * bartaCutoff c w t ≤ riemannKernelReal t * 1 :=
        mul_le_mul_of_nonneg_left (bartaCutoff_le_one c w t) (riemannKernelReal_pos t).le
    _ = riemannKernelReal t := mul_one _

theorem bartaProfile_eq_zero {c w t : ℝ} (hw : 0 < w) (ht : c ≤ |t|) : bartaProfile c w t = 0 := by
  rw [bartaProfile, bartaCutoff_eq_zero hw ht, mul_zero]

theorem bartaProfile_eq {c w t : ℝ} (hw : 0 < w) (ht : |t| ≤ c - w) :
    bartaProfile c w t = riemannKernelReal t := by
  rw [bartaProfile, bartaCutoff_eq_one hw ht, mul_one]

theorem support_bartaProfile_subset {c w : ℝ} (hw : 0 < w) :
    Function.support (bartaProfile c w) ⊆ Icc (-c) c := by
  intro t ht
  by_contra hmem
  apply ht
  apply bartaProfile_eq_zero hw
  rw [mem_Icc, not_and_or, not_le, not_le] at hmem
  rcases hmem with h | h
  · exact le_trans (by linarith) (neg_le_abs t)
  · exact le_trans h.le (le_abs_self t)

theorem tsupport_bartaProfile_subset {c w : ℝ} (hw : 0 < w) :
    tsupport (bartaProfile c w) ⊆ Icc (-c) c :=
  closure_minimal (support_bartaProfile_subset hw) isClosed_Icc

/-- The complex profile `t ↦ (Φ χ_{c,w})(t)`. -/
def bartaTest (c w : ℝ) (t : ℝ) : ℂ := ((bartaProfile c w t : ℝ) : ℂ)

theorem tsupport_bartaTest_subset {c w : ℝ} (hw : 0 < w) : tsupport (bartaTest c w) ⊆ Icc (-c) c := by
  have h : Function.support (bartaTest c w) ⊆ Icc (-c) c := by
    intro t ht
    apply support_bartaProfile_subset hw
    intro h0
    apply ht
    simp [bartaTest, h0]
  exact closure_minimal h isClosed_Icc

/-- **The truncated kernel as an interior source.** For `0 < w` and `c < a`, `Φ χ_{c,w}` is a
smooth interior source at aperture `a`. -/
def bartaSource (a : SuzukiPositiveAperture) (c w : ℝ) (hw : 0 < w) (hca : c < a.1) :
    CCMComplexSmoothInteriorSource a where
  toFun := bartaTest c w
  smooth := Complex.ofRealCLM.contDiff.comp (contDiff_bartaProfile c w)
  hasCompactSupport := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (tsupport_bartaTest_subset hw))
  tsupport_subset := (tsupport_bartaTest_subset hw).trans (Icc_subset_Ioo (by linarith) hca)

@[simp] theorem bartaSource_apply (a : SuzukiPositiveAperture) (c w : ℝ) (hw : 0 < w)
    (hca : c < a.1) (t : ℝ) : bartaSource a c w hw hca t = ((bartaProfile c w t : ℝ) : ℂ) := rfl

/-- The edge layer `Φ(χ_{c₂,w₂} - χ_{c₁,w₁})` as an interior source at aperture `a > c₂`. -/
def bartaLayerSource (a : SuzukiPositiveAperture) (c₁ w₁ c₂ w₂ : ℝ) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hc₁ : c₁ < a.1) (hc₂ : c₂ < a.1) : CCMComplexSmoothInteriorSource a where
  toFun := fun t => bartaTest c₂ w₂ t - bartaTest c₁ w₁ t
  smooth := (Complex.ofRealCLM.contDiff.comp (contDiff_bartaProfile c₂ w₂)).sub
    (Complex.ofRealCLM.contDiff.comp (contDiff_bartaProfile c₁ w₁))
  hasCompactSupport := by
    have h1 : HasCompactSupport (bartaTest c₂ w₂) :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport _).trans (tsupport_bartaTest_subset hw₂))
    have h2 : HasCompactSupport (bartaTest c₁ w₁) :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport _).trans (tsupport_bartaTest_subset hw₁))
    exact h1.sub h2
  tsupport_subset := by
    have h := tsupport_sub (bartaTest c₂ w₂) (bartaTest c₁ w₁)
    refine h.trans (union_subset ((tsupport_bartaTest_subset hw₂).trans ?_)
      ((tsupport_bartaTest_subset hw₁).trans ?_))
    · exact Icc_subset_Ioo (by linarith) hc₂
    · exact Icc_subset_Ioo (by linarith) hc₁

@[simp] theorem bartaLayerSource_apply (a : SuzukiPositiveAperture) (c₁ w₁ c₂ w₂ : ℝ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hc₁ : c₁ < a.1) (hc₂ : c₂ < a.1) (t : ℝ) :
    bartaLayerSource a c₁ w₁ c₂ w₂ hw₁ hw₂ hc₁ hc₂ t =
      ((bartaProfile c₂ w₂ t - bartaProfile c₁ w₁ t : ℝ) : ℂ) := by
  simp [bartaLayerSource, bartaTest]

/-- On the nested layer `c₁ ≤ c₂ - w₂`, the layer profile lies between `0` and `Φ` and vanishes
on `|t| ≤ c₁ - w₁`. -/
theorem bartaLayer_bounds {c₁ w₁ c₂ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hc : c₁ ≤ c₂ - w₂)
    (t : ℝ) :
    0 ≤ bartaProfile c₂ w₂ t - bartaProfile c₁ w₁ t ∧
      bartaProfile c₂ w₂ t - bartaProfile c₁ w₁ t ≤ riemannKernelReal t := by
  have hΦ := (riemannKernelReal_pos t).le
  rcases le_or_gt |t| (c₂ - w₂) with ht | ht
  · rw [bartaProfile_eq hw₂ ht]
    constructor
    · linarith [bartaProfile_le c₁ w₁ t]
    · linarith [bartaProfile_nonneg c₁ w₁ t]
  · rw [bartaProfile_eq_zero hw₁ (by linarith : c₁ ≤ |t|)]
    exact ⟨by linarith [bartaProfile_nonneg c₂ w₂ t], by linarith [bartaProfile_le c₂ w₂ t]⟩

theorem bartaLayer_eq_zero {c₁ w₁ c₂ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hc : c₁ ≤ c₂ - w₂) {t : ℝ} (ht : |t| ≤ c₁ - w₁) :
    bartaProfile c₂ w₂ t - bartaProfile c₁ w₁ t = 0 := by
  rw [bartaProfile_eq hw₂ (by linarith), bartaProfile_eq hw₁ ht, sub_self]

end

end RHTower
