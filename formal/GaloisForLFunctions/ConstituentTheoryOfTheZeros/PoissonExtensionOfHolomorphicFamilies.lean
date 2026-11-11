import GaloisForLFunctions.Bottcher.HarmonicReflection
import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.HardyProductArcGluing

/-!
# Poisson extension of holomorphic circle families

Harmonic measure extends continuous circle data to the closed disc, preserves
uniform bounds, and commutes with holomorphic dependence on an external
parameter. When the data are holomorphic disc traces, the extension reproduces
that holomorphic function.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Classical

noncomputable section
namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- Circle data, viewed as a function on the ambient plane. -/
def circleBoundaryValue (f : Circle → ℂ) (z : ℂ) : ℂ :=
  if hz : z ∈ sphere (0 : ℂ) 1 then f ⟨z, hz⟩ else 0

@[simp] theorem circleBoundaryValue_coe (f : Circle → ℂ) (z : Circle) :
    circleBoundaryValue f (z : ℂ) = f z := by
  unfold circleBoundaryValue
  split_ifs with hz
  · rfl
  · exact False.elim (hz z.2)

theorem continuousOn_circleBoundaryValue {f : Circle → ℂ} (hf : Continuous f) :
    ContinuousOn (circleBoundaryValue f) (sphere (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun z : Circle => circleBoundaryValue f (z : ℂ))
  have heq : (fun z : Circle => circleBoundaryValue f (z : ℂ)) = f := by
    funext z
    exact circleBoundaryValue_coe f z
  rw [heq]
  exact hf

/-- Poisson extension agrees with the given data on the circle. -/
def circlePoissonExtension (f : Circle → ℂ) (w : ℂ) : ℂ :=
  if w ∈ ball (0 : ℂ) 1 then
    Real.circleAverage (fun z => (poissonKernel 0 w z : ℂ) * circleBoundaryValue f z) 0 1
  else circleBoundaryValue f w

theorem circlePoissonExtension_coe (f : Circle → ℂ) (w : Circle) :
    circlePoissonExtension f (w : ℂ) = f w := by
  have hw : (w : ℂ) ∉ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_zero_right, Circle.norm_coe, lt_self_iff_false, not_false_eq_true]
  simp only [circlePoissonExtension, if_neg hw, circleBoundaryValue_coe]

theorem circlePoissonExtension_eq_integral {f : Circle → ℂ} (hf : Continuous f)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    circlePoissonExtension f w = ∫ ζ : Circle, f ζ ∂circlePoissonMeasure ⟨w, hw⟩ := by
  rw [circlePoissonExtension, if_pos hw,
    ← integral_circlePoissonMeasure_eq_circleAverage ⟨w, hw⟩ (circleBoundaryValue f)]
  · simp only [circleBoundaryValue_coe]
  · simpa only [circleBoundaryValue_coe] using hf

/-- Only continuity of the boundary trace is needed for Poisson boundary continuity. -/
private theorem continuousOn_real_poissonExt {g : ℂ → ℝ}
    (hg : ContinuousOn g (sphere (0 : ℂ) 1)) :
    ContinuousOn (Bottcher.poissonExt 0 1 g) (closedBall (0 : ℂ) 1) := by
  intro ζ hζ
  rcases eq_or_lt_of_le (mem_closedBall.mp hζ) with hsp | hin
  · have hs : ζ ∈ sphere (0 : ℂ) 1 := mem_sphere.mpr hsp
    have hcover : closedBall (0 : ℂ) 1 = ball 0 1 ∪ sphere 0 1 := ball_union_sphere.symm
    rw [ContinuousWithinAt, Bottcher.poissonExt_eq_on_sphere ζ hs,
      hcover, nhdsWithin_union, tendsto_sup]
    constructor
    · apply (Bottcher.poissonInt_tendsto_boundary (by norm_num) hg hs).congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Bottcher.poissonExt, if_pos hz]
    · have hfc : Tendsto g (𝓝[sphere (0 : ℂ) 1] ζ) (𝓝 (g ζ)) := hg ζ hs
      apply hfc.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (Bottcher.poissonExt_eq_on_sphere z hz).symm
  · exact ((Bottcher.poissonExt_harmonicOnNhd (by norm_num) hg ζ hin).1.continuousAt).continuousWithinAt

theorem continuousOn_circlePoissonExtension {f : Circle → ℂ} (hf : Continuous f) :
    ContinuousOn (circlePoissonExtension f) (closedBall (0 : ℂ) 1) := by
  let g := circleBoundaryValue f
  have hg : ContinuousOn g (sphere (0 : ℂ) 1) := continuousOn_circleBoundaryValue hf
  have hre := continuousOn_real_poissonExt (Complex.continuous_re.comp_continuousOn hg)
  have him := continuousOn_real_poissonExt (Complex.continuous_im.comp_continuousOn hg)
  have heq : circlePoissonExtension f = fun w =>
      (Bottcher.poissonExt 0 1 (fun z => (g z).re) w : ℂ) +
        (Bottcher.poissonExt 0 1 (fun z => (g z).im) w : ℂ) * I := by
    funext w
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · have hci : CircleIntegrable
          (fun z => (poissonKernel 0 w z : ℂ) * g z) 0 1 := by
        apply ContinuousOn.circleIntegrable'
        rw [abs_one]
        convert (Complex.continuous_ofReal.comp_continuousOn
          (Bottcher.poissonKernel_continuousOn_sphere hw)).mul hg using 1
        rfl
      simp only [circlePoissonExtension, Bottcher.poissonExt, if_pos hw]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          sub_zero, add_zero]
        change Complex.reCLM (Real.circleAverage
          (fun z => (poissonKernel 0 w z : ℂ) * g z) 0 1) = _
        rw [← ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hci]
        apply Real.circleAverage_congr_sphere
        intro z _
        simp [Function.comp_apply, Complex.mul_re]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          zero_add, add_zero]
        change Complex.imCLM (Real.circleAverage
          (fun z => (poissonKernel 0 w z : ℂ) * g z) 0 1) = _
        rw [← ContinuousLinearMap.circleAverage_comp_comm Complex.imCLM hci]
        apply Real.circleAverage_congr_sphere
        intro z _
        simp [Function.comp_apply, Complex.mul_im]
    · simp only [circlePoissonExtension, Bottcher.poissonExt, if_neg hw]
      exact (Complex.re_add_im (g w)).symm
  rw [heq]
  exact (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul continuousOn_const)

/-- Poisson averaging reproduces every holomorphic continuous disc function. -/
theorem circlePoissonExtension_eq_of_diffContOnCl {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    circlePoissonExtension (fun ζ : Circle => F ζ) w = F w := by
  by_cases hwi : w ∈ ball (0 : ℂ) 1
  · rw [circlePoissonExtension, if_pos hwi]
    have heq : Real.circleAverage
        (fun z => (poissonKernel 0 w z : ℂ) * circleBoundaryValue (fun ζ : Circle => F ζ) z) 0 1 =
        Real.circleAverage (poissonKernel 0 w • F) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hz' : z ∈ sphere (0 : ℂ) 1 := by simpa only [abs_one] using hz
      have hval : circleBoundaryValue (fun ζ : Circle => F ζ) z = F z :=
        circleBoundaryValue_coe (fun ζ : Circle => F ζ) ⟨z, hz'⟩
      exact (congrArg (fun t : ℂ => (poissonKernel 0 w z : ℂ) * t) hval).trans
        (Complex.real_smul : poissonKernel 0 w z • F z =
          (poissonKernel 0 w z : ℂ) * F z).symm
    rw [heq]
    exact hF.circleAverage_poissonKernel_smul hwi
  · have hs : w ∈ sphere (0 : ℂ) 1 := by
      exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hw) (not_lt.mp hwi))
    exact circlePoissonExtension_coe (fun ζ : Circle => F ζ) ⟨w, hs⟩

/-- Harmonic measure preserves a uniform bound on the boundary data. -/
theorem norm_circlePoissonExtension_le {f : Circle → ℂ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ ζ, ‖f ζ‖ ≤ M) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    ‖circlePoissonExtension f w‖ ≤ M := by
  by_cases hwi : w ∈ ball (0 : ℂ) 1
  · rw [circlePoissonExtension_eq_integral hf hwi]
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := circlePoissonMeasure ⟨w, hwi⟩) (Eventually.of_forall hM))
  · have hs : w ∈ sphere (0 : ℂ) 1 :=
      mem_sphere.mpr (le_antisymm (mem_closedBall.mp hw) (not_lt.mp hwi))
    rw [circlePoissonExtension_coe f ⟨w, hs⟩]
    exact hM ⟨w, hs⟩

/-- Poisson extension contracts the uniform distance between boundary functions. -/
theorem norm_circlePoissonExtension_sub_le {f g : Circle → ℂ}
    (hf : Continuous f) (hg : Continuous g) {M : ℝ}
    (hM : ∀ ζ, ‖f ζ - g ζ‖ ≤ M) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    ‖circlePoissonExtension f w - circlePoissonExtension g w‖ ≤ M := by
  by_cases hwi : w ∈ ball (0 : ℂ) 1
  · rw [circlePoissonExtension_eq_integral hf hwi,
      circlePoissonExtension_eq_integral hg hwi,
      ← integral_sub
        (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := circlePoissonMeasure ⟨w, hwi⟩) (Eventually.of_forall hM))
  · have hs : w ∈ sphere (0 : ℂ) 1 :=
      mem_sphere.mpr (le_antisymm (mem_closedBall.mp hw) (not_lt.mp hwi))
    rw [circlePoissonExtension_coe f ⟨w, hs⟩, circlePoissonExtension_coe g ⟨w, hs⟩]
    exact hM ⟨w, hs⟩

/-- Joint continuity of boundary data persists on the entire closed disc. -/
theorem continuousOn_circlePoissonExtension_family
    {U : Set ℂ} {B : ℂ → Circle → ℂ}
    (hB : ContinuousOn (Function.uncurry B) (U ×ˢ univ)) :
    ContinuousOn (fun q : ℂ × ℂ => circlePoissonExtension (B q.1) q.2)
      (U ×ˢ closedBall (0 : ℂ) 1) := by
  have hb (s : ℂ) (hs : s ∈ U) : Continuous (B s) := by
    rw [← continuousOn_univ]
    exact hB.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun ζ _ => ⟨hs, mem_univ ζ⟩)
  intro q hq
  let p : Filter (ℂ × ℂ) := 𝓝[U ×ˢ closedBall (0 : ℂ) 1] q
  have hm : ∀ᶠ v in p, v ∈ U ×ˢ closedBall (0 : ℂ) 1 := self_mem_nhdsWithin
  have hs : Tendsto (fun v : ℂ × ℂ => v.1) p (𝓝[U] q.1) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_fst.continuousWithinAt, hm.mono fun _ hv => hv.1⟩
  have hw : Tendsto (fun v : ℂ × ℂ => v.2) p (𝓝[closedBall (0 : ℂ) 1] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_snd.continuousWithinAt, hm.mono fun _ hv => hv.2⟩
  have hbase := Filter.Tendsto.comp
    ((continuousOn_circlePoissonExtension (hb q.1 hq.1)) q.2 hq.2) hw
  change Tendsto (fun v : ℂ × ℂ => circlePoissonExtension (B v.1) v.2) p
    (𝓝 (circlePoissonExtension (B q.1) q.2))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V, hV, hclose⟩ := isCompact_univ.mem_uniformity_of_prod hB hq.1
    (dist_mem_uniformity (half_pos hε))
  filter_upwards [hm, hs.eventually hV,
    (Metric.tendsto_nhds.mp hbase) (ε / 2) (half_pos hε)] with v hv hvV hvbase
  have hbd : ∀ ζ, ‖B v.1 ζ - B q.1 ζ‖ ≤ ε / 2 := by
    intro ζ
    have hc : dist (B v.1 ζ) (B q.1 ζ) < ε / 2 := hclose v.1 hvV ζ (mem_univ ζ)
    simpa only [dist_eq_norm] using hc.le
  have hp := norm_circlePoissonExtension_sub_le (hb v.1 hv.1) (hb q.1 hq.1) hbd hv.2
  have ht := dist_triangle (circlePoissonExtension (B v.1) v.2)
    (circlePoissonExtension (B q.1) v.2) (circlePoissonExtension (B q.1) q.2)
  have hp' : dist (circlePoissonExtension (B v.1) v.2)
      (circlePoissonExtension (B q.1) v.2) ≤ ε / 2 := by
    simpa only [dist_eq_norm] using hp
  have hbase' : dist (circlePoissonExtension (B q.1) v.2)
      (circlePoissonExtension (B q.1) q.2) < ε / 2 := by
    simpa only [Function.comp_apply] using hvbase
  exact ht.trans_lt (by linarith only [hp', hbase'])

/-- A bounded holomorphic circle family remains holomorphic after Poisson averaging. -/
theorem differentiableOn_circlePoissonExtension_parameter
    {U : Set ℂ} (hU : IsOpen U) {B : ℂ → Circle → ℂ} {M : ℝ}
    (hcont : ∀ s ∈ U, Continuous (B s))
    (hhol : ∀ ζ, DifferentiableOn ℂ (fun s => B s ζ) U)
    (hbound : ∀ s ∈ U, ∀ ζ, ‖B s ζ‖ ≤ M)
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    DifferentiableOn ℂ (fun s => circlePoissonExtension (B s) w) U := by
  by_cases hwi : w ∈ ball (0 : ℂ) 1
  · intro s hs
    obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU s hs
    have hi : DifferentiableAt ℂ
        (fun s => ∫ ζ : Circle, B s ζ ∂circlePoissonMeasure ⟨w, hwi⟩) s :=
      differentiableAt_integral_of_cauchy_dominated hR
        (fun z hz => (hcont z (hRU hz)).aestronglyMeasurable)
        (fun ζ => (hhol ζ).mono hRU)
        (fun ζ z hz => hbound z (hRU hz) ζ) (integrable_const M)
    apply hi.differentiableWithinAt.congr
    · intro z hz
      exact circlePoissonExtension_eq_integral (hcont z hz) hwi
    · exact circlePoissonExtension_eq_integral (hcont s hs) hwi
  · have hs : w ∈ sphere (0 : ℂ) 1 :=
      mem_sphere.mpr (le_antisymm (mem_closedBall.mp hw) (not_lt.mp hwi))
    have heq : (fun s => circlePoissonExtension (B s) w) = fun s => B s ⟨w, hs⟩ := by
      funext s
      exact circlePoissonExtension_coe (B s) ⟨w, hs⟩
    rw [heq]
    exact hhol ⟨w, hs⟩

/-- The circle Cauchy kernel has no pole at an interior evaluation point. -/
theorem continuous_circleCauchyKernel {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    Continuous (fun ζ : Circle => (ζ : ℂ) / ((ζ : ℂ) - w)) := by
  apply Continuous.div continuous_subtype_val (continuous_subtype_val.sub continuous_const)
  intro ζ heq
  have hzw : (ζ : ℂ) = w := sub_eq_zero.mp heq
  have hn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  rw [← hzw, Circle.norm_coe] at hn
  exact (lt_irrefl 1) hn

/-- The Cauchy transform of integrable circle data is holomorphic inside the disc. -/
theorem differentiableOn_circleL1CauchyTransform {f : Circle → ℂ}
    (hf : Integrable f circleLebesgue) :
    DifferentiableOn ℂ (circleL1CauchyTransform f) (ball (0 : ℂ) 1) := by
  intro w hw
  have hn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  apply (differentiableAt_circleL1CauchyTransform_of_ae_zero_near f hf w
    (sub_pos.mpr hn) ?_).differentiableWithinAt
  filter_upwards with ζ
  intro hnear
  have ht : 1 ≤ ‖(ζ : ℂ) - w‖ + ‖w‖ := by
    simpa only [sub_add_cancel, Circle.norm_coe] using norm_add_le ((ζ : ℂ) - w) w
  rw [dist_eq_norm] at hnear
  linarith

/-- The normalized circle Cauchy transform reproduces holomorphic disc traces. -/
theorem circleL1CauchyTransform_eq_of_diffContOnCl {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (ball (0 : ℂ) 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    circleL1CauchyTransform (fun ζ : Circle => F ζ) w = F w := by
  have hc : Continuous (fun ζ : Circle => F ζ) :=
    (hF.continuousOn_ball.mono sphere_subset_closedBall).restrict
  rw [circleL1CauchyTransform,
    integral_circleLebesgue_eq_circleAverage_complex
      (fun z => F z * (z / (z - w)))
      ((hc.mul (continuous_circleCauchyKernel hw)).aestronglyMeasurable),
    Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  have hi : (∮ z in C(0, 1), (z - 0)⁻¹ • (F z * (z / (z - w)))) =
      ∮ z in C(0, 1), (z - w)⁻¹ • F z := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hn
    simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
    calc
      z⁻¹ * (F z * (z * (z - w)⁻¹)) = (z⁻¹ * z) * ((z - w)⁻¹ * F z) := by ring
      _ = (z - w)⁻¹ * F z := by rw [inv_mul_cancel₀ hz0, one_mul]
  rw [hi]
  exact hF.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

/-- External holomorphic dependence commutes with the circle Cauchy transform. -/
theorem differentiableOn_circleCauchyTransform_parameter
    {U : Set ℂ} (hU : IsOpen U) {B : ℂ → Circle → ℂ} {M : ℝ}
    (hcont : ∀ s ∈ U, Continuous (B s))
    (hhol : ∀ ζ, DifferentiableOn ℂ (fun s => B s ζ) U)
    (hbound : ∀ s ∈ U, ∀ ζ, ‖B s ζ‖ ≤ M)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (fun s => circleL1CauchyTransform (B s) w) U := by
  intro s hs
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU s hs
  have hK := continuous_circleCauchyKernel hw
  apply (differentiableAt_integral_of_cauchy_dominated
    (F := fun (z : ℂ) (ζ : Circle) => B z ζ * ((ζ : ℂ) / ((ζ : ℂ) - w)))
    (μ := circleLebesgue) (bound := fun ζ : Circle => M * ‖(ζ : ℂ) / ((ζ : ℂ) - w)‖) hR
    (fun z hz => ((hcont z (hRU hz)).mul hK).aestronglyMeasurable)
    (fun ζ => ((hhol ζ).mono hRU).mul_const ((ζ : ℂ) / ((ζ : ℂ) - w)))
    (fun ζ z hz => ?_)
    ((continuous_const.mul hK.norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).differentiableWithinAt
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound z (hRU hz) ζ) (norm_nonneg _)

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
