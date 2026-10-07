import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorWeightedQuarter
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonSmooth
import GaloisForLFunctions.RHTower.MaassConverseAutomorphy

/-!
# The actual polynomial Poisson modes satisfy the quarter equation

The compactified kernel is a constant multiple of square-root height after
inversion and real translation. The already verified Maass invariance theorem
proves its equation, which weighted integration then preserves.
-/

noncomputable section

open Complex Set Filter MeasureTheory Metric Polynomial
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

open MaassAxisContinuation MaassBesselSeries
open GaloisForLFunctions.HTGeometry.ComplexC2Laplacian

private lemma quarter_congr {F G : ℂ → ℂ} (h : EqOn F G upper) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect F z = quarterDefect G z := by
  have hD (v : ℂ) : EqOn (dirD v F) (dirD v G) upper := fun _ hx => dirD_congr h hx v
  simp only [quarterDefect, dirD_congr (hD 1) hz 1, dirD_congr (hD I) hz I, h hz]

private lemma smooth_real_translate {F : ℂ → ℂ} (hF : ContDiffOn ℝ ∞ F upper) (r : ℝ) :
    ContDiffOn ℝ ∞ (fun z => F (z + (r : ℂ))) upper := by
  apply hF.comp (contDiffOn_id.add contDiffOn_const)
  intro z hz
  simpa [upper] using hz

/-- Real translations preserve the exact quarter differential equation. -/
theorem quarterDefect_comp_real_translate {F : ℂ → ℂ} (hF : ContDiffOn ℝ ∞ F upper)
    (hQ : ∀ z ∈ upper, quarterDefect F z = 0) (r : ℝ) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (fun w => F (w + (r : ℂ))) z = 0 := by
  have hz' : z + (r : ℂ) ∈ upper := by simpa [upper] using hz
  have hC : ContDiffAt ℂ 2 (fun w : ℂ => w + (r : ℂ)) z :=
    contDiffAt_id.add contDiffAt_const
  have hL := laplacian_holomorphic_comp (g := fun w : ℂ => w + (r : ℂ)) (z := z)
    ((hF.contDiffAt (isOpen_upper.mem_nhds hz')).of_le (by decide)) hC
  have hder : deriv (fun w : ℂ => w + (r : ℂ)) z = 1 :=
    ((hasDerivAt_id z).add_const (r : ℂ)).deriv
  rw [hder, map_one, ofReal_one, one_mul] at hL
  dsimp only [Function.comp_def] at hL
  have hq := hQ _ hz'
  change laplacian (fun w => F (w + (r : ℂ))) z + quarterWeight z • F (z + (r : ℂ)) = 0
  rw [hL]
  change dirD 1 (dirD 1 F) (z + (r : ℂ)) + dirD I (dirD I F) (z + (r : ℂ)) +
    quarterWeight z • F (z + (r : ℂ)) = 0
  simpa only [quarterDefect, quarterWeight, add_im, ofReal_im, add_zero] using hq

/-- Full projective kernel, including square-root height. -/
def projectivePoissonMode (z c : ℂ) : ℂ :=
  (Real.sqrt z.im : ℂ) * (projectivePoissonKernel z c : ℂ)

theorem contDiffOn_projectivePoissonMode :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => projectivePoissonMode p.1 p.2)
      (upper ×ˢ {c : ℂ | c ≠ 0}) := by
  have hs : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => (Real.sqrt p.1.im : ℂ))
      (upper ×ˢ {c : ℂ | c ≠ 0}) := by
    intro p hp
    have hi : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1.im) p :=
      imCLM.contDiff.contDiffAt.comp p contDiffAt_fst
    have hh := ofRealCLM.contDiff.contDiffAt.comp p
      (hi.rpow_const_of_ne (p := (1 / 2 : ℝ)) (ne_of_gt hp.1))
    convert hh.contDiffWithinAt using 1
    ext q
    simp [Real.sqrt_eq_rpow]
  exact hs.mul (ofRealCLM.contDiff.comp_contDiffOn contDiffOn_projectivePoissonKernel)

private lemma sqrtHeight_constTerm (z : ℂ) :
    (Real.sqrt z.im : ℂ) = constTerm 0 1 z := by
  simp [constTerm, sqrtPart, Real.sqrt_eq_rpow]

private lemma sqrtHeight_invS {z : ℂ} (hz : z ∈ upper) :
    constTerm 0 1 (invS z) = (Real.sqrt z.im / ‖z‖ : ℝ) := by
  rw [← sqrtHeight_constTerm, invS_im, Real.sqrt_div (le_of_lt hz),
    Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]

/-- Every projective parameter gives a quarter eigenfunction; zero gives the zero function. -/
theorem quarterDefect_projectivePoissonMode (c : ℂ) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (fun w => projectivePoissonMode w c) z = 0 := by
  by_cases ha : c.im = 0
  · have heq : EqOn (fun w => projectivePoissonMode w c)
        (fun w => ((|c.re|⁻¹ : ℝ) : ℂ) * constTerm 0 1 w) upper := by
      intro w _
      simp only [projectivePoissonMode, projectivePoissonKernel_eq_norm_inv,
        ha, ofReal_zero, mul_zero, zero_add, Complex.norm_real, Real.norm_eq_abs,
        sqrtHeight_constTerm, mul_comm]
    rw [quarter_congr heq hz, quarterDefect_const_mul (contDiffOn_constTerm 0 1) _ hz,
      quarterDefect_constTerm 0 1 hz, mul_zero]
  · let r : ℝ := c.re / c.im
    have hT := smooth_real_translate (contDiffOn_comp_invS (contDiffOn_constTerm 0 1)) r
    have heq : EqOn (fun w => projectivePoissonMode w c)
        (fun w => ((|c.im|⁻¹ : ℝ) : ℂ) * constTerm 0 1 (invS (w + (r : ℂ)))) upper := by
      intro w hw
      dsimp only
      have hw' : w + (r : ℂ) ∈ upper := by simpa [upper] using hw
      have hn : ‖w * (c.im : ℂ) + (c.re : ℂ)‖ = |c.im| * ‖w + (r : ℂ)‖ := by
        have he : w * (c.im : ℂ) + (c.re : ℂ) = (c.im : ℂ) * (w + (r : ℂ)) := by
          dsimp [r]
          push_cast
          have ha' : (c.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
          field_simp [ha']
        rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [projectivePoissonMode, projectivePoissonKernel_eq_norm_inv, hn, sqrtHeight_invS hw']
      simp only [add_im, ofReal_im, add_zero, ofReal_div, ofReal_inv, ofReal_mul, mul_inv_rev]
      ring
    rw [quarter_congr heq hz, quarterDefect_const_mul hT _ hz]
    have hQ := quarterDefect_comp_real_translate (contDiffOn_comp_invS (contDiffOn_constTerm 0 1))
      (fun w hw => quarterDefect_comp_invS (contDiffOn_constTerm 0 1)
        (fun v hv => quarterDefect_constTerm 0 1 hv) hw) r hz
    rw [hQ, mul_zero]

private lemma circle_subset_punctured : sphere (0 : ℂ) 1 ⊆ {c : ℂ | c ≠ 0} := by
  intro c hc hz
  simp [hz] at hc

private lemma polarParameter_mem_circle (t : ℝ) : polarParameter t ∈ sphere (0 : ℂ) 1 := by
  simpa only [mem_sphere, dist_zero_right] using norm_polarParameter t

private lemma integrable_weighted_projectiveMode {w : ℝ → ℝ} (hw : Integrable w)
    {z : ℂ} (hz : z ∈ upper) :
    Integrable (fun t : ℝ => w t • projectivePoissonMode z (polarParameter t)) :=
  weighted_parameter_integrable isOpen_upper isOpen_ne (isCompact_sphere (0 : ℂ) 1)
    circle_subset_punctured continuous_polarParameter polarParameter_mem_circle hw
    contDiffOn_projectivePoissonMode.continuousOn hz

private lemma smooth_weighted_projectiveMode {w : ℝ → ℝ} (hw : Integrable w) :
    ContDiffOn ℝ ∞ (fun z => ∫ t : ℝ, w t • projectivePoissonMode z (polarParameter t)) upper :=
  contDiffOn_weighted_compact_parameter_infty isOpen_upper isOpen_ne (isCompact_sphere (0 : ℂ) 1)
    circle_subset_punctured continuous_polarParameter polarParameter_mem_circle hw
    contDiffOn_projectivePoissonMode

private lemma quarter_weighted_projectiveMode {w : ℝ → ℝ} (hw : Integrable w)
    {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (fun z => ∫ t : ℝ, w t • projectivePoissonMode z (polarParameter t)) z = 0 := by
  rw [quarterDefect_weighted_compact_parameter isOpen_ne (isCompact_sphere (0 : ℂ) 1)
    circle_subset_punctured continuous_polarParameter polarParameter_mem_circle hw
    contDiffOn_projectivePoissonMode hz]
  have hzero : (fun t : ℝ => w t • quarterDefect
      (fun x => projectivePoissonMode x (polarParameter t)) z) = fun _ => 0 := by
    funext t
    rw [quarterDefect_projectivePoissonMode (polarParameter t) hz, smul_zero]
  rw [hzero, integral_zero]

/-- Every actual logarithmic-polynomial mode is a quarter eigenfunction. -/
theorem quarterDefect_polynomialPolarMode {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (P : ℂ[X]) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (polynomialPolarMode ρ P) z = 0 := by
  let W : ℝ → ℂ := fun t => P.eval (Real.log |t| : ℂ) * polarKernel ρ I t
  have hW : Integrable W := integrable_polynomial_polarKernel hρ₀ hρ₁ (by simp) P
  let J : (ℝ → ℝ) → ℂ → ℂ :=
    fun w x => ∫ t : ℝ, w t • projectivePoissonMode x (polarParameter t)
  have heq : EqOn (polynomialPolarMode ρ P)
      (fun x => J (fun t => (W t).re) x + I * J (fun t => (W t).im) x) upper := by
    intro x hx
    change (Real.sqrt x.im : ℂ) * (∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ x t) = _
    have hR : Integrable (fun t : ℝ => (W t).re • projectivePoissonMode x (polarParameter t)) :=
      integrable_weighted_projectiveMode hW.re hx
    have hI : Integrable (fun t : ℝ => I * ((W t).im • projectivePoissonMode x (polarParameter t))) :=
      (integrable_weighted_projectiveMode hW.im hx).const_mul I
    dsimp only [J]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hR hI]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [polynomial_polarKernel_projective ρ x P hx t]
      change (Real.sqrt x.im : ℂ) * (W t * (projectivePoissonKernel x (polarParameter t) : ℂ)) = _
      simp only [projectivePoissonMode, Complex.real_smul]
      calc
        _ = ((W t).re + (W t).im * I) *
            ((Real.sqrt x.im : ℂ) * (projectivePoissonKernel x (polarParameter t) : ℂ)) := by
          rw [Complex.re_add_im]
          ring
        _ = _ := by ring
  have hJR : ContDiffOn ℝ ∞ (J fun t => (W t).re) upper := smooth_weighted_projectiveMode hW.re
  have hJI : ContDiffOn ℝ ∞ (J fun t => (W t).im) upper := smooth_weighted_projectiveMode hW.im
  have hQR : quarterDefect (J fun t => (W t).re) z = 0 := quarter_weighted_projectiveMode hW.re hz
  have hQI : quarterDefect (J fun t => (W t).im) z = 0 := quarter_weighted_projectiveMode hW.im hz
  rw [quarter_congr heq hz, quarterDefect_add hJR (contDiffOn_const.mul hJI) hz,
    quarterDefect_const_mul hJI I hz, hQR, hQI]
  ring

end RHTower.WeilHigherDenominator
