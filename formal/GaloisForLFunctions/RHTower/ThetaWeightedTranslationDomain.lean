import GaloisForLFunctions.RHTower.ThetaRealShiftHistory
import Mathlib.Analysis.Convex.PathConnected

/-!
# The full complex theta translation domain in every weighted Hilbert carrier

The paper's exact Gaussian-slack domain is open and star-convex about
zero. On this entire domain the literal complete theta translation orbit
is a Hilbert-valued holomorphic map, with the actual ordinary derivatives
as its origin jets. Every complex orbit vector lies in derivative history.
-/

open MeasureTheory Set Metric Filter Topology

namespace RHTower

open HedenmalmThetaSource DominatedL2Sections

noncomputable section

/-- The literal full Gaussian-slack domain of the weighted translation orbit. -/
def thetaWeightedTranslationDomain (q : ℝ) : Set ℂ :=
  {z | |z.im| < Real.pi / 4 ∧
    q < 2 * Real.exp (-2 * |z.re|) * Real.cos (2 * z.im)}

theorem isOpen_thetaWeightedTranslationDomain (q : ℝ) :
    IsOpen (thetaWeightedTranslationDomain q) := by
  have hc : Continuous (fun z : ℂ =>
      2 * Real.exp (-2 * |z.re|) * Real.cos (2 * z.im)) := by fun_prop
  exact (isOpen_Iio.preimage Complex.continuous_im.abs).inter (isOpen_Ioi.preimage hc)

theorem zero_mem_thetaWeightedTranslationDomain (q : ℝ) (hq2 : q < 2) :
    (0 : ℂ) ∈ thetaWeightedTranslationDomain q := by
  change |(0 : ℂ).im| < Real.pi / 4 ∧
    q < 2 * Real.exp (-2 * |(0 : ℂ).re|) * Real.cos (2 * (0 : ℂ).im)
  simpa using And.intro (by positivity : (0 : ℝ) < Real.pi / 4) hq2

theorem ofReal_mem_thetaWeightedTranslationDomain_iff (q a : ℝ) :
    (a : ℂ) ∈ thetaWeightedTranslationDomain q ↔ q < 2 * Real.exp (-2 * |a|) := by
  simp [thetaWeightedTranslationDomain, Real.pi_pos]

theorem ofReal_mem_thetaWeightedTranslationDomain_iff_log (q a : ℝ) (hq : 0 < q) :
    (a : ℂ) ∈ thetaWeightedTranslationDomain q ↔ |a| < Real.log (2 / q) / 2 :=
  (ofReal_mem_thetaWeightedTranslationDomain_iff q a).trans
    (thetaRealShiftSource_threshold_iff q a hq)

private theorem theta_cos_two_abs (x : ℝ) : Real.cos (2 * |x|) = Real.cos (2 * x) := by
  rw [show 2 * |x| = |2 * x| by simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)],
    Real.cos_abs]

/-- Every point has a strict enclosing rectangle with the complete Gaussian slack. -/
theorem theta_weighted_rectangle_exists_of_domain (q : ℝ) {z : ℂ}
    (hz : z ∈ thetaWeightedTranslationDomain q) :
    ∃ δ A : ℝ, 0 < δ ∧ |z.re| < A ∧ |z.im| < δ ∧ 2 * δ < Real.pi / 2 ∧
      q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ) := by
  have hqa : q < 2 * Real.exp (-2 * |z.re|) * Real.cos (2 * |z.im|) := by
    rw [theta_cos_two_abs]
    exact hz.2
  have hcont : ContinuousAt (fun v : ℝ =>
      2 * Real.exp (-2 * v) * Real.cos (2 * |z.im|)) |z.re| := by fun_prop
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.tendsto.eventually (Ioi_mem_nhds hqa))
  let A := |z.re| + r / 2
  have haA : |z.re| < A := by dsimp [A]; linarith
  have hAr : A ∈ ball |z.re| r := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr haA)]
    dsimp [A]
    linarith
  have hqA : q < 2 * Real.exp (-2 * A) * Real.cos (2 * |z.im|) := hball A hAr
  have hc : ContinuousAt (fun v : ℝ =>
      2 * Real.exp (-2 * A) * Real.cos (2 * v)) |z.im| := by fun_prop
  obtain ⟨d, hd, hdmargin⟩ := Metric.eventually_nhds_iff_ball.mp
    (hc.tendsto.eventually (Ioi_mem_nhds hqA))
  let δ := |z.im| + min d (Real.pi / 4 - |z.im|) / 2
  have hmin : 0 < min d (Real.pi / 4 - |z.im|) :=
    lt_min hd (sub_pos.mpr hz.1)
  have hiδ : |z.im| < δ := by dsimp [δ]; linarith
  have hδ : 0 < δ := (abs_nonneg z.im).trans_lt hiδ
  have hδd : δ - |z.im| < d := by
    have := min_le_left d (Real.pi / 4 - |z.im|)
    dsimp [δ]
    linarith
  have hδ4 : 2 * δ < Real.pi / 2 := by
    have := min_le_right d (Real.pi / 4 - |z.im|)
    dsimp [δ]
    linarith
  refine ⟨δ, A, hδ, haA, hiδ, hδ4, hdmargin δ ?_⟩
  rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hiδ)]
  exact hδd

/-- Shrinking any complex translation toward zero increases its Gaussian admission margin. -/
theorem starConvex_thetaWeightedTranslationDomain (q : ℝ) :
    StarConvex ℝ (0 : ℂ) (thetaWeightedTranslationDomain q) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  have hre : (b • z : ℂ).re = b * z.re := by simp only [Complex.smul_re, smul_eq_mul]
  have him : (b • z : ℂ).im = b * z.im := by simp only [Complex.smul_im, smul_eq_mul]
  have hbre : |b * z.re| = b * |z.re| := by rw [abs_mul, abs_of_nonneg hb]
  have hbim : |b * z.im| = b * |z.im| := by rw [abs_mul, abs_of_nonneg hb]
  have hbR : b * |z.re| ≤ |z.re| := by nlinarith [abs_nonneg z.re]
  have hbI : b * |z.im| ≤ |z.im| := by nlinarith [abs_nonneg z.im]
  have he : Real.exp (-2 * |z.re|) ≤ Real.exp (-2 * |(b • z : ℂ).re|) := by
    rw [hre, hbre]
    exact Real.exp_le_exp.mpr (by linarith)
  have hc : Real.cos (2 * z.im) ≤ Real.cos (2 * (b • z : ℂ).im) := by
    rw [him, ← theta_cos_two_abs z.im, ← theta_cos_two_abs (b * z.im), hbim]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_pos, hz.1] : 2 * |z.im| ≤ Real.pi)
    linarith
  have hcos : 0 ≤ Real.cos (2 * z.im) := by
    rw [← theta_cos_two_abs]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, abs_nonneg z.im],
      by linarith [hz.1]⟩).le
  constructor
  · rw [him, hbim]
    exact hbI.trans_lt hz.1
  · have hp := mul_le_mul he hc hcos (Real.exp_pos _).le
    have h2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
    exact hz.2.trans_le (by simpa only [mul_assoc] using h2)

theorem isPathConnected_thetaWeightedTranslationDomain (q : ℝ) (hq2 : q < 2) :
    IsPathConnected (thetaWeightedTranslationDomain q) :=
  (starConvex_thetaWeightedTranslationDomain q).isPathConnected
    (zero_mem_thetaWeightedTranslationDomain q hq2)

theorem isConnected_thetaWeightedTranslationDomain (q : ℝ) (hq2 : q < 2) :
    IsConnected (thetaWeightedTranslationDomain q) :=
  (isPathConnected_thetaWeightedTranslationDomain q hq2).isConnected

/-- The literal complete source defines a locally dominated family on its entire domain. -/
def thetaWeightedDomainTranslationFamily (q : ℝ) (hq : 0 < q) :
    Family (thetaPowerWeightedMeasure q) where
  domain := thetaWeightedTranslationDomain q
  isOpen_domain := isOpen_thetaWeightedTranslationDomain q
  value z x := thetaCuspStripSource ((x : ℂ) + z)
  measurable z hz := (continuous_thetaCuspStripSource_translation hz.1).aestronglyMeasurable
  holomorphic x := by
    intro z hz
    have hp : (x : ℂ) + z ∈ thetaCuspStrip := by
      change |((x : ℂ) + z).im| < Real.pi / 4
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hz.1
    exact ((differentiableAt_thetaCuspStripSource hp).comp z (by fun_prop)).differentiableWithinAt
  local_bound z hz := by
    obtain ⟨δ, A, hδ, hA, hiδ, hδ4, hmargin⟩ := theta_weighted_rectangle_exists_of_domain q hz
    have hzR : z ∈ thetaTranslationRectangle δ A := ⟨hA, hiδ⟩
    obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp
      ((isOpen_thetaWeightedTranslationDomain q).inter (isOpen_thetaTranslationRectangle δ A))
      z ⟨hz, hzR⟩
    refine ⟨R, hR, fun w hw => (hsub hw).1, thetaRectangleGaussianMajorant δ A,
      thetaRectangleGaussianMajorant_memLp δ A q ((abs_nonneg z.re).trans hA.le)
        hδ.le hδ4 hq hmargin, ?_⟩
    intro x w hw
    exact norm_thetaCuspStripSource_translate_le_rectangle δ A hδ.le hδ4 w
      (hsub hw).2.1.le (hsub hw).2.2.le x

theorem thetaWeightedDomainTranslationFamily_section (q : ℝ) (hq : 0 < q) {z : ℂ}
    (hz : z ∈ thetaWeightedTranslationDomain q) :
    (thetaWeightedDomainTranslationFamily q hq).section z = thetaWeightedTranslationClass q z :=
  Family.section_eq_l2Family _ hz

theorem thetaCuspStripSource_translation_memLp_of_domain (q : ℝ) (hq : 0 < q) {z : ℂ}
    (hz : z ∈ thetaWeightedTranslationDomain q) :
    MemLp (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + z)) 2 (thetaPowerWeightedMeasure q) :=
  (thetaWeightedDomainTranslationFamily q hq).memLp hz

theorem thetaWeightedTranslationClass_coe_of_domain (q : ℝ) (hq : 0 < q) {z : ℂ}
    (hz : z ∈ thetaWeightedTranslationDomain q) :
    (thetaWeightedTranslationClass q z : ℝ → ℂ) =ᵐ[thetaPowerWeightedMeasure q]
      fun x => thetaCuspStripSource ((x : ℂ) + z) := by
  rw [← thetaWeightedDomainTranslationFamily_section q hq hz]
  exact (thetaWeightedDomainTranslationFamily q hq).section_coe hz

/-- Hilbert holomorphy holds on the full paper domain, not only individual real rectangles. -/
theorem analyticOnNhd_thetaWeightedTranslationClass (q : ℝ) (hq : 0 < q) :
    AnalyticOnNhd ℂ (thetaWeightedTranslationClass q) (thetaWeightedTranslationDomain q) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_thetaWeightedTranslationDomain q)
  intro z hz
  have h := (thetaWeightedDomainTranslationFamily q hq).hasDerivAt_section hz
  have he : thetaWeightedTranslationClass q =ᶠ[𝓝 z]
      (thetaWeightedDomainTranslationFamily q hq).section := by
    filter_upwards [(isOpen_thetaWeightedTranslationDomain q).mem_nhds hz] with w hw
    exact (thetaWeightedDomainTranslationFamily_section q hq hw).symm
  exact (h.congr_of_eventuallyEq he).differentiableAt.differentiableWithinAt

/-- Origin jets of the full-domain map are the actual ordinary derivative classes. -/
theorem iteratedDeriv_thetaWeightedTranslationClass_zero
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (n : ℕ) :
    iteratedDeriv n (thetaWeightedTranslationClass q) 0 = thetaWeightedDerivativeVector q n := by
  obtain ⟨δ, A, hδ, hA, hδ4, hmargin⟩ := theta_weighted_rectangle_exists 0 q (by simpa using hq2)
  have hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(0 : ℂ).re| < A ∧ |(0 : ℂ).im| < δ
    simpa using And.intro hA hδ
  have he : thetaWeightedTranslationClass q =ᶠ[𝓝 0]
      (thetaWeightedTranslationFamily q δ A hA.le hδ.le hδ4 hq hmargin).section := by
    filter_upwards [(isOpen_thetaTranslationRectangle δ A).mem_nhds hzero] with z hz
    exact (thetaWeightedTranslationFamily_section q δ A hA.le hδ.le hδ4 hq hmargin hz).symm
  rw [he.iteratedDeriv_eq n]
  exact thetaWeightedTranslationFamily_iteratedDeriv_zero q δ A hA.le hδ.le hδ4 hq hmargin hzero n

/-- Every complex orbit vector on the whole connected domain belongs to actual history. -/
theorem thetaWeightedTranslationClass_mem_derivativeHistory_of_domain
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) {z : ℂ}
    (hz : z ∈ thetaWeightedTranslationDomain q) :
    thetaWeightedTranslationClass q z ∈ thetaWeightedDerivativeHistory q := by
  let F := thetaWeightedDomainTranslationFamily q hq
  have hzero := zero_mem_thetaWeightedTranslationDomain q hq2
  have h := F.section_mem_closed_span_jets
    (isConnected_thetaWeightedTranslationDomain q hq2).isPreconnected hzero hz
  have he : F.section =ᶠ[𝓝 0] thetaWeightedTranslationClass q := by
    filter_upwards [(isOpen_thetaWeightedTranslationDomain q).mem_nhds hzero] with w hw
    exact thetaWeightedDomainTranslationFamily_section q hq hw
  have hjets : (fun n : ℕ => iteratedDeriv n F.section 0) = thetaWeightedDerivativeVector q := by
    funext n
    rw [he.iteratedDeriv_eq n, iteratedDeriv_thetaWeightedTranslationClass_zero q hq hq2 n]
  rw [hjets, thetaWeightedDomainTranslationFamily_section q hq hz] at h
  exact h

/-- The original reciprocal-weight domain is exactly the domain displayed in the paper. -/
theorem mem_thetaWeightedTranslationDomain_reciprocal (z : ℂ) :
    z ∈ thetaWeightedTranslationDomain 1 ↔ |z.im| < Real.pi / 4 ∧
      1 < 2 * Real.exp (-2 * |z.re|) * Real.cos (2 * z.im) := Iff.rfl

/-- At `q = 1`, the literal power weight is the actual Hedenmalm source measure. -/
theorem thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure :
    thetaPowerWeightedMeasure 1 = volume.withDensity
      (GaloisForLFunctions.HTGeometry.realDensity (HedenmalmQuantile.sourceWeight thetaSource)) := by
  change volume.withDensity (fun x : ℝ => ENNReal.ofReal (thetaCuspFullSource x ^ (-1 : ℝ))) =
    volume.withDensity (fun x : ℝ => ENNReal.ofReal ((thetaSource.k x)⁻¹))
  congr 1
  funext x
  rw [Real.rpow_neg_one, thetaSource_k]

/-- The exact sharp admission theorem on the original literal source carrier. -/
theorem thetaRealShiftSource_ofReal_memLp_source_iff (a : ℝ) :
    MemLp (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) 2
      (volume.withDensity (GaloisForLFunctions.HTGeometry.realDensity
        (HedenmalmQuantile.sourceWeight thetaSource))) ↔ |a| < Real.log 2 / 2 := by
  rw [← thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure]
  simpa only [div_one] using thetaRealShiftSource_ofReal_memLp_iff_log 1 a (by norm_num)

end

end RHTower
