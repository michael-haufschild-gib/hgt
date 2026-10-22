import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
The literal complex translation orbit of the original unscaled theta source.
Cauchy estimates give every complex jet uniform exponential decay on closed
substrips. Each translate is constructed in the actual Schwartz space.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace RHTower

private theorem thetaComplexAbsIm_le_of_norm_sub_le {w z : ℂ} {r : ℝ}
    (h : ‖w - z‖ ≤ r) : |w.im| ≤ |z.im| + r := by
  have him := (Complex.abs_im_le_norm (w - z)).trans h
  rw [Complex.sub_im] at him
  calc
    |w.im| = |(w.im - z.im) + z.im| := by congr 1; ring
    _ ≤ |w.im - z.im| + |z.im| := abs_add_le _ _
    _ ≤ r + |z.im| := by gcongr
    _ = |z.im| + r := by ring

private theorem thetaComplexAbsRe_le_of_norm_sub_le {w z : ℂ} {r : ℝ}
    (h : ‖w - z‖ ≤ r) : |w.re| ≤ |z.re| + r := by
  have hre := (Complex.abs_re_le_norm (w - z)).trans h
  rw [Complex.sub_re] at hre
  calc
    |w.re| = |(w.re - z.re) + z.re| := by congr 1; ring
    _ ≤ |w.re - z.re| + |z.re| := abs_add_le _ _
    _ ≤ r + |z.re| := by gcongr
    _ = |z.re| + r := by ring

/-- All actual complex source jets remain analytic throughout the literal strip. -/
theorem thetaCuspStripSource_complexJet_analyticAt (n : ℕ) {z : ℂ}
    (hz : z ∈ thetaCuspStrip) : AnalyticAt ℂ (iteratedDeriv n thetaCuspStripSource) z := by
  induction n with
  | zero => exact analyticOnNhd_thetaCuspStripSource z hz
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- Uniform exponential decay of every actual complex jet on every closed substrip. -/
theorem thetaCuspStripSource_complexJet_exp_decay {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ δ →
      ‖iteratedDeriv n thetaCuspStripSource z‖ ≤ C * Real.exp (-|z.re|) := by
  let r := (Real.pi / 4 - δ) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hδr0 : 0 ≤ δ + r := by linarith
  have hδr4 : 2 * (δ + r) < Real.pi / 2 := by dsimp [r]; linarith
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaCuspStripSource_le hδr0 hδr4
  refine ⟨(n.factorial : ℝ) * C * Real.exp r / r ^ n, by positivity, ?_⟩
  intro z hz
  have hdisc : Metric.closedBall z r ⊆ thetaCuspStrip := by
    intro w hw
    have hnorm : ‖w - z‖ ≤ r := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
    have him := thetaComplexAbsIm_le_of_norm_sub_le hnorm
    change |w.im| < Real.pi / 4
    linarith
  have hf := differentiableOn_thetaCuspStripSource.diffContOnCl_ball hdisc
  have hcircle : ∀ w ∈ Metric.sphere z r,
      ‖thetaCuspStripSource w‖ ≤ C * Real.exp r * Real.exp (-|z.re|) := by
    intro w hw
    have hnorm : ‖w - z‖ ≤ r := by
      have he : ‖w - z‖ = r := by
        simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
      exact he.le
    have him : |w.im| ≤ δ + r :=
      (thetaComplexAbsIm_le_of_norm_sub_le hnorm).trans (by gcongr)
    have hnorm' : ‖z - w‖ ≤ r := by rw [norm_sub_rev]; exact hnorm
    have hre := thetaComplexAbsRe_le_of_norm_sub_le hnorm'
    have he : Real.exp (-|w.re|) ≤ Real.exp r * Real.exp (-|z.re|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc
      ‖thetaCuspStripSource w‖ ≤ C * Real.exp (-|w.re|) := hbound w him
      _ ≤ C * (Real.exp r * Real.exp (-|z.re|)) :=
        mul_le_mul_of_nonneg_left he hC
      _ = C * Real.exp r * Real.exp (-|z.re|) := by ring
  have hj := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf hcircle
  calc
    ‖iteratedDeriv n thetaCuspStripSource z‖ ≤
        (n.factorial : ℝ) * (C * Real.exp r * Real.exp (-|z.re|)) / r ^ n := hj
    _ = ((n.factorial : ℝ) * C * Real.exp r / r ^ n) * Real.exp (-|z.re|) := by ring

theorem thetaCuspStripTranslate_contDiff (a : ℂ) (ha : a ∈ thetaCuspStrip) :
    ContDiff ℝ ∞ (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + a)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hz : (x : ℂ) + a ∈ thetaCuspStrip := by
    simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im,
      Complex.ofReal_im, zero_add] using ha
  have hc : ContDiffAt ℂ ∞ thetaCuspStripSource ((x : ℂ) + a) :=
    (analyticOnNhd_thetaCuspStripSource _ hz).contDiffAt
  exact (hc.restrict_scalars ℝ).comp x
    (Complex.ofRealCLM.contDiff.add contDiff_const).contDiffAt

/-- The actual real spatial jets equal the complex jets of the literal strip source. -/
theorem thetaCuspStripTranslate_iteratedDeriv (a : ℂ) (ha : a ∈ thetaCuspStrip)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => thetaCuspStripSource ((y : ℂ) + a)) x =
      iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : (iteratedDeriv n (fun y : ℝ => thetaCuspStripSource ((y : ℂ) + a))) =
        (fun y : ℝ => iteratedDeriv n thetaCuspStripSource ((y : ℂ) + a)) := funext ih
    rw [he]
    have hz : (x : ℂ) + a ∈ thetaCuspStrip := by
      simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im,
        Complex.ofReal_im, zero_add] using ha
    have hd := (thetaCuspStripSource_complexJet_analyticAt n hz).differentiableAt.hasDerivAt
    have hc := hd.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const a)
    have hc' := hc.comp_ofReal
    simpa only [Function.comp_def, id_eq, mul_one, iteratedDeriv_succ] using hc'.deriv

private theorem thetaExpAbsShift_le (a x : ℝ) :
    Real.exp (-|x + a|) ≤ Real.exp |a| * Real.exp (-|x|) := by
  have h : |x| ≤ |x + a| + |a| := by
    calc
      |x| = |(x + a) + (-a)| := by congr 1; ring
      _ ≤ |x + a| + |-a| := abs_add_le _ _
      _ = |x + a| + |a| := by rw [abs_neg]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The literal complex translate of the original unscaled source in actual Schwartz space. -/
def thetaCuspStripTranslateSchwartz (a : ℂ) (ha : a ∈ thetaCuspStrip) : 𝓢(ℝ, ℂ) where
  toFun := fun x : ℝ => thetaCuspStripSource ((x : ℂ) + a)
  smooth' := thetaCuspStripTranslate_contDiff a ha
  decay' k n := by
    have ha' : |a.im| < Real.pi / 4 := ha
    let δ := (|a.im| + Real.pi / 4) / 2
    have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith [abs_nonneg a.im, Real.pi_pos]
    have hδ4 : 2 * δ < Real.pi / 2 := by dsimp [δ]; linarith
    have haδ : |a.im| ≤ δ := by dsimp [δ]; linarith
    obtain ⟨C, hC, hbound⟩ := thetaCuspStripSource_complexJet_exp_decay hδ0 hδ4 n
    refine ⟨C * Real.exp |a.re| * (k.factorial : ℝ), ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      thetaCuspStripTranslate_iteratedDeriv a ha, Real.norm_eq_abs]
    have hz : |((x : ℂ) + a).im| ≤ δ := by
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using haδ
    have hp := hbound ((x : ℂ) + a) hz
    have he : Real.exp (-|((x : ℂ) + a).re|) ≤
        Real.exp |a.re| * Real.exp (-|x|) := by
      simpa only [Complex.add_re, Complex.ofReal_re] using thetaExpAbsShift_le a.re x
    calc
      |x| ^ k * ‖iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a)‖ ≤
          |x| ^ k * (C * Real.exp (-|((x : ℂ) + a).re|)) :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg x) k)
      _ ≤ |x| ^ k * (C * (Real.exp |a.re| * Real.exp (-|x|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hC)
          (pow_nonneg (abs_nonneg x) k)
      _ = (C * Real.exp |a.re|) * (|x| ^ k * Real.exp (-|x|)) := by ring
      _ ≤ (C * Real.exp |a.re|) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial k (abs_nonneg x))
          (mul_nonneg hC (Real.exp_pos _).le)

theorem thetaCuspStripTranslateSchwartz_apply (a : ℂ) (ha : a ∈ thetaCuspStrip) (x : ℝ) :
    thetaCuspStripTranslateSchwartz a ha x = thetaCuspStripSource ((x : ℂ) + a) := rfl

theorem thetaCuspStripTranslateSchwartz_iteratedDeriv
    (a : ℂ) (ha : a ∈ thetaCuspStrip) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (thetaCuspStripTranslateSchwartz a ha : ℝ → ℂ) x =
      iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a) :=
  thetaCuspStripTranslate_iteratedDeriv a ha n x

/-- Global section whose restriction to the literal strip is the actual Schwartz source orbit. -/
def thetaCuspSchwartzTranslationCurve (a : ℂ) : 𝓢(ℝ, ℂ) := by
  classical
  exact if ha : a ∈ thetaCuspStrip then thetaCuspStripTranslateSchwartz a ha else 0

theorem thetaCuspSchwartzTranslationCurve_eq (a : ℂ) (ha : a ∈ thetaCuspStrip) :
    thetaCuspSchwartzTranslationCurve a = thetaCuspStripTranslateSchwartz a ha := by
  rw [thetaCuspSchwartzTranslationCurve, dif_pos ha]

theorem thetaCuspSchwartzTranslationCurve_apply (a : ℂ) (ha : a ∈ thetaCuspStrip) (x : ℝ) :
    thetaCuspSchwartzTranslationCurve a x = thetaCuspStripSource ((x : ℂ) + a) := by
  rw [thetaCuspSchwartzTranslationCurve_eq a ha]
  rfl

theorem thetaCuspSchwartzTranslationCurve_spatialJet
    (a : ℂ) (ha : a ∈ thetaCuspStrip) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (thetaCuspSchwartzTranslationCurve a : ℝ → ℂ) x =
      iteratedDeriv n thetaCuspStripSource ((x : ℂ) + a) := by
  rw [thetaCuspSchwartzTranslationCurve_eq a ha]
  exact thetaCuspStripTranslateSchwartz_iteratedDeriv a ha n x

theorem thetaCuspSchwartzTranslationCurve_zero :
    thetaCuspSchwartzTranslationCurve 0 = thetaCuspSchwartz := by
  have h0 : (0 : ℂ) ∈ thetaCuspStrip := by
    change |(0 : ℂ).im| < Real.pi / 4
    simp only [Complex.zero_im, abs_zero]
    positivity
  ext x
  rw [thetaCuspSchwartzTranslationCurve_apply 0 h0, add_zero,
    thetaCuspStripSource_ofReal, thetaCuspSchwartz_apply]

theorem thetaCuspSchwartzTranslationCurve_real_apply (a x : ℝ) :
    thetaCuspSchwartzTranslationCurve (a : ℂ) x = thetaCuspSchwartz (x + a) := by
  have ha : (a : ℂ) ∈ thetaCuspStrip := by
    change |(a : ℂ).im| < Real.pi / 4
    simp only [Complex.ofReal_im, abs_zero]
    positivity
  rw [thetaCuspSchwartzTranslationCurve_apply (a : ℂ) ha, ← Complex.ofReal_add,
    thetaCuspStripSource_ofReal, thetaCuspSchwartz_apply]

end RHTower
