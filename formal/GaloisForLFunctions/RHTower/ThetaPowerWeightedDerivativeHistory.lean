import GaloisForLFunctions.RHTower.ThetaPowerWeightedComplexTranslations
import GaloisForLFunctions.RHTower.AnalyticDominatedL2Derivatives
import GaloisForLFunctions.HTGeometry.SampledSmallSmooth
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay

/-!
# Actual theta derivatives generate every admitted translation

The strict Gaussian admission margin supplies a connected complex rectangle
containing the origin and the requested real translation. The literal source
orbit is holomorphic in its actual power-weighted L² carrier. Its jets are
the actual derivatives of the real complete theta source, so analytic
uniqueness gives membership in their closed span.
-/

open MeasureTheory Set Metric Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry DominatedL2Sections

noncomputable section

def thetaTranslationRectangle (δ A : ℝ) : Set ℂ :=
  {z | |z.re| < A ∧ |z.im| < δ}

theorem isOpen_thetaTranslationRectangle (δ A : ℝ) :
    IsOpen (thetaTranslationRectangle δ A) :=
  (isOpen_Iio.preimage Complex.continuous_re.abs).inter
    (isOpen_Iio.preimage Complex.continuous_im.abs)

theorem convex_thetaTranslationRectangle (δ A : ℝ) :
    Convex ℝ (thetaTranslationRectangle δ A) := by
  have he : thetaTranslationRectangle δ A =
      (fun z : ℂ => z.re) ⁻¹' Ioo (-A) A ∩ (fun z : ℂ => z.im) ⁻¹' Ioo (-δ) δ := by
    ext z
    simp only [thetaTranslationRectangle, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
  rw [he]
  exact ((convex_Ioo (-A) A).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioo (-δ) δ).linear_preimage Complex.imCLM.toLinearMap)

/-- Strict real admission leaves a nonzero complex aperture around the full translation interval. -/
theorem theta_weighted_rectangle_exists (a q : ℝ)
    (hqa : q < 2 * Real.exp (-2 * a)) :
    ∃ δ A : ℝ, 0 < δ ∧ a < A ∧ 2 * δ < Real.pi / 2 ∧
      q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ) := by
  have hcont : ContinuousAt (fun v : ℝ => 2 * Real.exp (-2 * v)) a := by fun_prop
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.tendsto.eventually (Ioi_mem_nhds hqa))
  let A := a + r / 2
  have haA : a < A := by dsimp [A]; linarith
  have hAr : A ∈ ball a r := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr haA)]
    dsimp [A]
    linarith
  have hqA : q < 2 * Real.exp (-2 * A) := hball A hAr
  have hc : ContinuousAt (fun v : ℝ =>
      2 * Real.exp (-2 * A) * Real.cos (2 * v)) 0 := by fun_prop
  have hqA0 : q < 2 * Real.exp (-2 * A) * Real.cos (2 * 0) := by simpa using hqA
  obtain ⟨d, hd, hdmargin⟩ := Metric.eventually_nhds_iff_ball.mp
    (hc.tendsto.eventually (Ioi_mem_nhds hqA0))
  let δ := min d (Real.pi / 4) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min hd (by positivity)) (by norm_num)
  have hδd : δ < d := by
    have := min_le_left d (Real.pi / 4)
    dsimp [δ]
    linarith
  have hδ4 : 2 * δ < Real.pi / 2 := by
    have := min_le_right d (Real.pi / 4)
    dsimp [δ]
    linarith [Real.pi_pos]
  refine ⟨δ, A, hδ, haA, hδ4, hdmargin δ ?_⟩
  simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ] using hδd

/-- Canonical classes use the actual complete source wherever it is admitted. -/
def thetaWeightedTranslationClass (q : ℝ) (z : ℂ) : Lp ℂ 2 (thetaPowerWeightedMeasure q) :=
  l2Family (thetaPowerWeightedMeasure q) (fun w x => thetaCuspStripSource ((x : ℂ) + w)) z

/-- The generators are the real complete source's actual derivatives. -/
def thetaWeightedDerivativeVector (q : ℝ) (n : ℕ) : Lp ℂ 2 (thetaPowerWeightedMeasure q) :=
  l2Family (thetaPowerWeightedMeasure q)
    (fun _ x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 0

def thetaWeightedDerivativeHistory (q : ℝ) : Submodule ℂ (Lp ℂ 2 (thetaPowerWeightedMeasure q)) :=
  (Submodule.span ℂ (range (thetaWeightedDerivativeVector q))).topologicalClosure

/-- At a real translation the canonical class is the literal real-source class. -/
theorem thetaWeightedTranslationClass_eq_toLp (q a : ℝ)
    (h : MemLp (fun x : ℝ => ((thetaCuspFullSource (x + a) : ℝ) : ℂ)) 2
      (thetaPowerWeightedMeasure q)) :
    thetaWeightedTranslationClass q (a : ℂ) = h.toLp _ := by
  have he : (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + (a : ℂ))) =
      (fun x : ℝ => ((thetaCuspFullSource (x + a) : ℝ) : ℂ)) := by
    funext x
    rw [← Complex.ofReal_add, thetaCuspStripSource_ofReal]
  have hm : MemLp (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + (a : ℂ))) 2
      (thetaPowerWeightedMeasure q) := by rw [he]; exact h
  rw [thetaWeightedTranslationClass, l2Family_eq_toLp (thetaPowerWeightedMeasure q)
    (fun w x => thetaCuspStripSource ((x : ℂ) + w)) (a : ℂ) hm]
  exact hm.toLp_congr h (ae_of_all _ fun x => congrFun he x)

/-- Real and complex jets coincide for the literal complete theta source. -/
theorem thetaCuspStripSource_iteratedDeriv_ofReal (n : ℕ) (x : ℝ) :
    iteratedDeriv n thetaCuspStripSource (x : ℂ) = ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) := by
  have h := HTGeometry.iteratedDeriv_comp_ofReal_of_analyticAt (T := x - 1) n
    (H := thetaCuspStripSource)
    (fun t _ => analyticOnNhd_thetaCuspStripSource (t : ℂ) (by
      change |(t : ℂ).im| < Real.pi / 4
      simp only [Complex.ofReal_im, abs_zero]
      positivity)) x (by linarith)
  have he : (fun t : ℝ => thetaCuspStripSource (t : ℂ)) =
      (fun t : ℝ => (thetaCuspFullSource t : ℂ)) := funext thetaCuspStripSource_ofReal
  rw [he, GaloisForLFunctions.iteratedDeriv_ofReal_comp contDiff_thetaCuspFullSource n] at h
  exact h.symm

/-- Concrete local domination places the actual orbit in the fixed weighted carrier. -/
def thetaWeightedTranslationFamily (q δ A : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hq : 0 < q)
    (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ)) :
    Family (thetaPowerWeightedMeasure q) where
  domain := thetaTranslationRectangle δ A
  isOpen_domain := isOpen_thetaTranslationRectangle δ A
  value z x := thetaCuspStripSource ((x : ℂ) + z)
  measurable z hz := (continuous_thetaCuspStripSource_translation (by
    change |z.im| < Real.pi / 4
    exact lt_of_lt_of_le hz.2 (by linarith))).aestronglyMeasurable
  holomorphic x := by
    intro z hz
    have hp : (x : ℂ) + z ∈ thetaCuspStrip := by
      change |((x : ℂ) + z).im| < Real.pi / 4
      simp only [Complex.add_im, Complex.ofReal_im, zero_add]
      exact lt_of_lt_of_le hz.2 (by linarith)
    exact ((differentiableAt_thetaCuspStripSource hp).comp z (by fun_prop)).differentiableWithinAt
  local_bound z hz := by
    obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp (isOpen_thetaTranslationRectangle δ A) z hz
    refine ⟨R, hR, hsub, thetaRectangleGaussianMajorant δ A,
      thetaRectangleGaussianMajorant_memLp δ A q hA hδ hδ4 hq hmargin, ?_⟩
    intro x w hw
    exact norm_thetaCuspStripSource_translate_le_rectangle δ A hδ hδ4 w
      (hsub hw).1.le (hsub hw).2.le x

theorem thetaWeightedTranslationFamily_section
    (q δ A : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (hq : 0 < q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ))
    {z : ℂ} (hz : z ∈ thetaTranslationRectangle δ A) :
    (thetaWeightedTranslationFamily q δ A hA hδ hδ4 hq hmargin).section z =
      thetaWeightedTranslationClass q z :=
  Family.section_eq_l2Family _ hz

private theorem thetaWeightedTranslationFamily_pointwise_jet
    (q δ A : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (hq : 0 < q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ))
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n
      (fun z => (thetaWeightedTranslationFamily q δ A hA hδ hδ4 hq hmargin).value z x) 0 =
      ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ) := by
  change iteratedDeriv n (fun z => thetaCuspStripSource ((x : ℂ) + z)) 0 = _
  rw [iteratedDeriv_comp_const_add]
  simp only [add_zero, thetaCuspStripSource_iteratedDeriv_ofReal]

theorem thetaWeightedTranslationFamily_memLp_jet
    (q δ A : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (hq : 0 < q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ))
    (hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A) (n : ℕ) :
    MemLp (fun x : ℝ => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 2
      (thetaPowerWeightedMeasure q) := by
  have h := (thetaWeightedTranslationFamily q δ A hA hδ hδ4 hq
    hmargin).memLp_iteratedDeriv n hzero
  convert h using 1
  funext x
  exact (thetaWeightedTranslationFamily_pointwise_jet q δ A hA hδ hδ4 hq hmargin n x).symm

/-- All Hilbert orbit jets at the origin are the actual real-source derivative vectors. -/
theorem thetaWeightedTranslationFamily_iteratedDeriv_zero
    (q δ A : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2)
    (hq : 0 < q) (hmargin : q < 2 * Real.exp (-2 * A) * Real.cos (2 * δ))
    (hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A) (n : ℕ) :
    iteratedDeriv n (thetaWeightedTranslationFamily q δ A hA hδ hδ4 hq hmargin).section 0 =
      thetaWeightedDerivativeVector q n := by
  have hm := thetaWeightedTranslationFamily_memLp_jet q δ A hA hδ hδ4 hq hmargin hzero n
  rw [thetaWeightedDerivativeVector, l2Family_eq_toLp (thetaPowerWeightedMeasure q)
    (fun _ x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 0 hm]
  apply Lp.ext
  filter_upwards [(thetaWeightedTranslationFamily q δ A hA hδ hδ4 hq
    hmargin).coe_iteratedDeriv_section n hzero, hm.coeFn_toLp] with x hx hy
  exact hx.trans ((thetaWeightedTranslationFamily_pointwise_jet
    q δ A hA hδ hδ4 hq hmargin n x).trans hy.symm)

/-- Every admitted real translate lies in the closed span of actual weighted derivatives. -/
theorem thetaWeightedTranslationClass_mem_derivativeHistory
    (q a : ℝ) (hq : 0 < q) (ha : 0 ≤ a) (hqa : q < 2 * Real.exp (-2 * a)) :
    thetaWeightedTranslationClass q (a : ℂ) ∈ thetaWeightedDerivativeHistory q := by
  obtain ⟨δ, A, hδ, haA, hδ4, hmargin⟩ := theta_weighted_rectangle_exists a q hqa
  have hA : 0 ≤ A := le_trans ha haA.le
  have hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(0 : ℂ).re| < A ∧ |(0 : ℂ).im| < δ
    simpa using And.intro (lt_of_le_of_lt ha haA) hδ
  have haU : (a : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(a : ℂ).re| < A ∧ |(a : ℂ).im| < δ
    simpa only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, abs_of_nonneg ha] using
      And.intro haA hδ
  let F := thetaWeightedTranslationFamily q δ A hA hδ.le hδ4 hq hmargin
  have h := F.section_mem_closed_span_jets
    (convex_thetaTranslationRectangle δ A).isPreconnected hzero haU
  have he : (fun n : ℕ => iteratedDeriv n F.section 0) = thetaWeightedDerivativeVector q := by
    funext n
    exact thetaWeightedTranslationFamily_iteratedDeriv_zero q δ A hA hδ.le hδ4 hq hmargin hzero n
  rw [he, thetaWeightedTranslationFamily_section q δ A hA hδ.le hδ4 hq hmargin haU] at h
  exact h

/-- Every generator is genuinely admitted for each `0 < q < 2`. -/
theorem thetaWeightedDerivative_memLp (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (n : ℕ) :
    MemLp (fun x : ℝ => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 2
      (thetaPowerWeightedMeasure q) := by
  obtain ⟨δ, A, hδ, hA, hδ4, hmargin⟩ := theta_weighted_rectangle_exists 0 q (by simpa using hq2)
  have hzero : (0 : ℂ) ∈ thetaTranslationRectangle δ A := by
    change |(0 : ℂ).re| < A ∧ |(0 : ℂ).im| < δ
    simpa using And.intro hA hδ
  exact thetaWeightedTranslationFamily_memLp_jet q δ A hA.le hδ.le hδ4 hq hmargin hzero n

theorem thetaWeightedDerivativeVector_coe (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (n : ℕ) :
    (thetaWeightedDerivativeVector q n : ℝ → ℂ) =ᵐ[thetaPowerWeightedMeasure q]
      (fun x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) := by
  have h := thetaWeightedDerivative_memLp q hq hq2 n
  rw [thetaWeightedDerivativeVector, l2Family_eq_toLp (thetaPowerWeightedMeasure q)
    (fun _ x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 0 h]
  exact h.coeFn_toLp

end

end RHTower
