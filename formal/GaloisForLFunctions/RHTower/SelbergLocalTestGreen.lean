import GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import GaloisForLFunctions.HTGeometry.CompactSmoothCutoff

/-!
# Local upper-half-plane Green identities on actual compact tests

Compact support inside the upper half-plane gives global continuity and
integrability of each test/source product. The source needs C² regularity only
there. Two directional integrations by parts move the literal planar Laplacian
onto the test, retaining every support and differentiability condition.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergLocalTestGreen
open SelbergMaassTraceEnergy
noncomputable section

/-- A continuous test supported in the upper half-plane localizes a continuous source. -/
theorem continuous_test_mul {phi G : ℂ → ℝ} (hp : Continuous phi)
    (hG : ContinuousOn G {z : ℂ | 0 < z.im})
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) : Continuous (fun z => phi z * G z) := by
  exact (hp.continuousOn.mul hG).continuous_of_tsupport_subset isOpen_upperHalfPlaneSet
    (tsupport_mul_subset_left.trans hs)

/-- Every localized compact test/source product is genuinely integrable. -/
theorem integrable_test_mul {phi G : ℂ → ℝ} (hp : Continuous phi) (hc : HasCompactSupport phi)
    (hG : ContinuousOn G {z : ℂ | 0 < z.im})
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) : Integrable (fun z => phi z * G z) :=
  (continuous_test_mul hp hG hs).integrable_of_hasCompactSupport hc.mul_right

/-- The absolute-test pairing remains integrable under local source continuity. -/
theorem integrable_norm_test_mul {phi G : ℂ → ℝ} (hp : Continuous phi) (hc : HasCompactSupport phi)
    (hG : ContinuousOn G {z : ℂ | 0 < z.im})
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) : Integrable (fun z => ‖phi z‖ * G z) := by
  have hsN : tsupport (fun z => ‖phi z‖) ⊆ tsupport phi :=
    tsupport_comp_subset (g := fun x : ℝ => ‖x‖) (by simp) phi
  exact integrable_test_mul hp.norm hc.norm hG (hsN.trans hs)

/-- A local pointwise error majorant controls the difference of actual test integrals. -/
theorem norm_pairing_sub_le {phi F G w : ℂ → ℝ} (hp : Continuous phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (hG : ContinuousOn G {z : ℂ | 0 < z.im})
    (hw : ContinuousOn w {z : ℂ | 0 < z.im}) {c : ℝ}
    (hb : ∀ z, 0 < z.im → ‖F z - G z‖ ≤ c * w z) :
    ‖(∫ z, phi z * F z) - ∫ z, phi z * G z‖ ≤ c * ∫ z, ‖phi z‖ * w z := by
  rw [← integral_sub (integrable_test_mul hp hc hF hs) (integrable_test_mul hp hc hG hs),
    ← integral_const_mul]
  apply norm_integral_le_of_norm_le ((integrable_norm_test_mul hp hc hw hs).const_mul c)
  filter_upwards with z
  by_cases hz : 0 < z.im
  · rw [← mul_sub, norm_mul]
    calc
      ‖phi z‖ * ‖F z - G z‖ ≤ ‖phi z‖ * (c * w z) := mul_le_mul_of_nonneg_left (hb z hz) (norm_nonneg _)
      _ = c * (‖phi z‖ * w z) := by ring
  · have hpz : phi z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    simp only [hpz, zero_mul, sub_self, norm_zero, mul_zero, le_refl]

/-- One literal directional derivative consumes one order of global regularity. -/
theorem dir_contDiff {phi : ℂ → ℝ} {n m : WithTop ℕ∞} (hp : ContDiff ℝ n phi)
    (hmn : m + 1 ≤ n) (v : ℂ) : ContDiff ℝ m (dir v phi) :=
  (hp.fderiv_right hmn).clm_apply contDiff_const

/-- A literal directional derivative does not enlarge topological support. -/
theorem tsupport_dir_subset (phi : ℂ → ℝ) (v : ℂ) : tsupport (dir v phi) ⊆ tsupport phi :=
  tsupport_fderiv_apply_subset ℝ v

/-- Directional derivatives preserve compact support. -/
theorem hasCompactSupport_dir {phi : ℂ → ℝ} (hc : HasCompactSupport phi) (v : ℂ) :
    HasCompactSupport (dir v phi) := hc.fderiv_apply ℝ v

/-- Each second directional derivative of a C² test is continuous. -/
theorem second_continuous {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi) (v : ℂ) :
    Continuous (dir v (dir v phi)) :=
  (dir_contDiff (dir_contDiff hp (m := 1) (by norm_num) v) (m := 0) (by norm_num) v).continuous

/-- Two integrations by parts move a second directional derivative onto the compact test; source regularity is needed only in the upper half-plane. -/
theorem integral_test_second {phi F : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) (v : ℂ) :
    (∫ z, phi z * dir v (dir v F) z) = ∫ z, dir v (dir v phi) z * F z := by
  have hp1 := dir_contDiff hp (m := 1) (by norm_num) v
  have hc1 := hasCompactSupport_dir hc v
  have hc2 := hasCompactSupport_dir hc1 v
  have hs1 := (tsupport_dir_subset phi v).trans hs
  have hs2 := (tsupport_dir_subset (dir v phi) v).trans hs1
  have hF1 := dir_contDiffOn hF (m := 1) (by norm_num) v
  have hF2 := dir_contDiffOn hF1 (m := 0) (by norm_num) v
  have hi := integrable_test_mul hp1.continuous hc1 hF1.continuousOn hs1
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := phi) (g := dir v F) (v := v)
    hi (integrable_test_mul hp.continuous hc hF2.continuousOn hs)
    (integrable_test_mul hp.continuous hc hF1.continuousOn hs)
    (fun z _ => hp.differentiable (by norm_num) z)
    (fun z hz => (hF1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds (hs hz))).differentiableAt (by norm_num))
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := dir v phi) (g := F) (v := v)
    (integrable_test_mul (second_continuous hp v) hc2 hF.continuousOn hs2) hi
    (integrable_test_mul hp1.continuous hc1 hF.continuousOn hs1)
    (fun z _ => hp1.differentiable (by norm_num) z)
    (fun z hz => (hF.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds (hs1 hz))).differentiableAt (by norm_num))
  change (∫ z, phi z * dir v (dir v F) z) = -(∫ z, dir v phi z * dir v F z) at hfirst
  change (∫ z, dir v phi z * dir v F z) = -(∫ z, dir v (dir v phi) z * F z) at hsecond
  rw [hfirst, hsecond, neg_neg]

/-- The literal planar Laplacian of a C² test is continuous. -/
theorem laplacian_continuous {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi) :
    Continuous (realLaplacian phi) :=
  (second_continuous hp 1).add (second_continuous hp Complex.I)

/-- The planar Laplacian preserves compact support. -/
theorem laplacian_hasCompactSupport {phi : ℂ → ℝ} (hc : HasCompactSupport phi) :
    HasCompactSupport (realLaplacian phi) :=
  (hasCompactSupport_dir (hasCompactSupport_dir hc 1) 1).add
    (hasCompactSupport_dir (hasCompactSupport_dir hc Complex.I) Complex.I)

/-- The planar Laplacian does not enlarge topological support. -/
theorem laplacian_tsupport_subset (phi : ℂ → ℝ) : tsupport (realLaplacian phi) ⊆ tsupport phi := by
  apply (tsupport_add _ _).trans
  exact union_subset ((tsupport_dir_subset (dir 1 phi) 1).trans (tsupport_dir_subset phi 1))
    ((tsupport_dir_subset (dir Complex.I phi) Complex.I).trans (tsupport_dir_subset phi Complex.I))

/-- Local upper-half-plane Green identity with every product integrable and both original derivatives retained. -/
theorem integral_test_laplacian {phi F : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) :
    (∫ z, phi z * realLaplacian F z) = ∫ z, realLaplacian phi z * F z := by
  have hi (v : ℂ) : Integrable (fun z => phi z * dir v (dir v F) z) :=
    integrable_test_mul hp.continuous hc
      (dir_contDiffOn (dir_contDiffOn hF (m := 1) (by norm_num) v) (m := 0) (by norm_num) v).continuousOn hs
  have hj (v : ℂ) : Integrable (fun z => dir v (dir v phi) z * F z) :=
    integrable_test_mul (second_continuous hp v) (hasCompactSupport_dir (hasCompactSupport_dir hc v) v)
      hF.continuousOn ((tsupport_dir_subset (dir v phi) v).trans ((tsupport_dir_subset phi v).trans hs))
  simp_rw [realLaplacian, mul_add, add_mul]
  rw [integral_add (hi 1) (hi Complex.I), integral_add (hj 1) (hj Complex.I),
    integral_test_second hp hc hs hF 1, integral_test_second hp hc hs hF Complex.I]

/-- Every compact subset of the upper half-plane has an actual nonnegative C² compact cutoff equal to one on it. -/
theorem exists_nonnegative_cutoff {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ chi : ℂ → ℝ, ContDiff ℝ 2 chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {z : ℂ | 0 < z.im} ∧ (∀ z, 0 ≤ chi z) ∧ ∀ z ∈ K, chi z = 1 := by
  obtain ⟨chi, W, _, hKW, hp, hc, hs, hone⟩ :=
    HTGeometry.exists_smooth_cutoff hK isOpen_upperHalfPlaneSet hKU
  have hp2 : ContDiff ℝ 2 chi := hp.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun z => chi z * chi z, hp2.mul hp2, hc.mul_right,
    tsupport_mul_subset_left.trans hs, ?_, ?_⟩
  · intro z
    exact mul_self_nonneg _
  · intro z hz
    change chi z * chi z = 1
    rw [hone z (hKW hz), one_mul]

end
end GaloisForLFunctions.RHTower.SelbergLocalTestGreen
