import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityDeBranges
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberGlobalReflection
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped FourierTransform SchwartzMap

namespace RHTower

/-!
# No-go theorem and positive source residue for completed-density orientation

The source-selected completed-density split has a strictly positive odd boundary channel and a
strictly positive derivative-drop mass.  These source facts also show that this particular split
cannot define a globally positive Hermite--Biehler gap on the whole critical half-strip: boundary
differentiation would make its real phase ratio nondecreasing, whereas Riemann--Lebesgue decay and
Schwartz decay force the ratio to vanish at positive infinity.
-/

noncomputable section

private theorem completedDensityNoGo_E_re_ofReal (t : ℝ) :
    (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re =
      2 * t ^ (2 : ℕ) * (XiC (t : ℂ)).re := by
  have h := thetaCuspTailSecondDensityPhaseValue_re_ofReal_crossed t
  have hq : (t : ℂ) ^ (2 : ℕ) + 1 / 4 = ((t ^ (2 : ℕ) + 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold thetaCuspTailSecondDensityDeBrangesE
  rw [hq]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  norm_num
  linarith

private theorem completedDensityNoGo_hasDerivAt_E {z : ℂ} (hz : -1 < z.im) :
    HasDerivAt thetaCuspTailSecondDensityDeBrangesE
      (2 * z * thetaCuspTailSecondDensityPhaseValue z +
        (z ^ (2 : ℕ) + 1 / 4) * thetaCuspTailSecondDensityPhaseDerivative z) z := by
  have hq : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + 1 / 4) (2 * z) z := by
    simpa [mul_comm] using ((hasDerivAt_id z).pow 2).add_const (1 / 4)
  have hF := hasDerivAt_thetaCuspTailSecondDensityPhaseValue (z₀ := z) hz
  unfold thetaCuspTailSecondDensityDeBrangesE
  exact (hq.mul hF).sub_const (1 / 4)

private theorem completedDensityNoGo_hasDerivAt_ESharp {z : ℂ} (hz : z.im < 1) :
    HasDerivAt thetaCuspTailSecondDensityDeBrangesESharp
      (2 * z * thetaCuspTailSecondDensityPhaseValue (-z) -
        (z ^ (2 : ℕ) + 1 / 4) * thetaCuspTailSecondDensityPhaseDerivative (-z)) z := by
  have hq : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + 1 / 4) (2 * z) z := by
    simpa [mul_comm] using ((hasDerivAt_id z).pow 2).add_const (1 / 4)
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hF0 := hasDerivAt_thetaCuspTailSecondDensityPhaseValue
    (z₀ := -z) (by simpa using neg_lt_neg hz)
  have hF := hF0.comp z hneg
  unfold thetaCuspTailSecondDensityDeBrangesESharp
  exact ((hq.mul hF).sub_const (1 / 4)).congr_deriv (by
    simp only [Function.comp_apply]
    ring)

private theorem completedDensityNoGo_vertical_gap_derivative (t : ℝ) :
    HasDerivAt
      (fun y : ℝ => thetaCuspTailSecondDensityDeBrangesGap
        ((t : ℂ) + (y : ℂ) * I))
      (-4 * (((2 * (t : ℂ) * thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
          ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
            thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)) *
        starRingEnd ℂ (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im)) 0 := by
  let E' : ℂ :=
    2 * (t : ℂ) * thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
      ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
        thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)
  have hz : HasDerivAt (fun y : ℝ => (t : ℂ) + (y : ℂ) * I) I 0 := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I
    simpa using h.const_add (t : ℂ)
  have hE0 := completedDensityNoGo_hasDerivAt_E
    (z := (t : ℂ) + ((0 : ℝ) : ℂ) * I) (by simp)
  have hE : HasDerivAt
      (fun y : ℝ => thetaCuspTailSecondDensityDeBrangesE
        ((t : ℂ) + (y : ℂ) * I)) (E' * I) 0 := by
    simpa [E', Function.comp_def] using hE0.comp 0 hz
  have hS : HasDerivAt
      (fun y : ℝ => thetaCuspTailSecondDensityDeBrangesESharp
        ((t : ℂ) + (y : ℂ) * I)) ((starRingEnd ℂ E') * I) 0 := by
    have hzneg : HasDerivAt
        (fun y : ℝ => (t : ℂ) - (y : ℂ) * I) (-I) 0 := by
      have h := (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I
      simpa using h.const_sub (t : ℂ)
    have hE0neg := completedDensityNoGo_hasDerivAt_E
      (z := (t : ℂ) - ((0 : ℝ) : ℂ) * I) (by simp)
    have hEneg : HasDerivAt
        (fun y : ℝ => thetaCuspTailSecondDensityDeBrangesE
          ((t : ℂ) - (y : ℂ) * I)) (E' * (-I)) 0 := by
      simpa [E', Function.comp_def] using hE0neg.comp 0 hzneg
    have hconj : HasDerivAt
        (fun y : ℝ => starRingEnd ℂ
          (thetaCuspTailSecondDensityDeBrangesE
            ((t : ℂ) - (y : ℂ) * I))) ((starRingEnd ℂ E') * I) 0 := by
      have hc := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt 0 hEneg
      exact hc.congr_deriv (by
        simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
          map_mul, map_neg, Complex.conj_I]
        ring)
    apply hconj.congr_of_eventuallyEq
    have hev : ∀ᶠ y : ℝ in 𝓝 0, |y| < 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)] with y hy
      exact abs_lt.mpr hy
    filter_upwards [hev] with y hy
    have hsharp := thetaCuspTailSecondDensityDeBrangesE_sharp
      (z := (t : ℂ) + (y : ℂ) * I) (by simpa using hy)
    rw [← hsharp]
    congr 2
    apply Complex.ext <;> simp
  have hEre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hE
  have hEim := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hE
  have hSre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hS
  have hSim := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hS
  have hnormE := (hEre.mul hEre).add (hEim.mul hEim)
  have hnormS := (hSre.mul hSre).add (hSim.mul hSim)
  have hnormE' : HasDerivAt
      (fun y : ℝ => Complex.normSq
        (thetaCuspTailSecondDensityDeBrangesE ((t : ℂ) + (y : ℂ) * I)))
      (-2 * (E' * starRingEnd ℂ
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im) 0 := by
    exact hnormE.congr_deriv (by
      simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
        mul_re, mul_im, I_re, I_im, mul_zero, mul_one, zero_mul, add_zero,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_zero]
      ring)
  have hsharp0 := thetaCuspTailSecondDensityDeBrangesE_sharp
    (z := (t : ℂ)) (by simp)
  have hsharp : starRingEnd ℂ
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)) =
      thetaCuspTailSecondDensityDeBrangesESharp (t : ℂ) := by
    simpa using hsharp0
  have hnormS' : HasDerivAt
      (fun y : ℝ => Complex.normSq
        (thetaCuspTailSecondDensityDeBrangesESharp ((t : ℂ) + (y : ℂ) * I)))
      (2 * (E' * starRingEnd ℂ
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im) 0 := by
    exact hnormS.congr_deriv (by
      simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
        mul_re, mul_im, I_re, I_im, mul_zero, mul_one, zero_mul, add_zero,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_zero]
      rw [← hsharp]
      simp only [Complex.conj_re, Complex.conj_im]
      ring)
  exact (hnormE'.sub hnormS').congr_deriv (by dsimp [E']; ring)

private theorem completedDensityNoGo_gap_ofReal (t : ℝ) :
    thetaCuspTailSecondDensityDeBrangesGap (t : ℂ) = 0 := by
  have hsharp := thetaCuspTailSecondDensityDeBrangesE_sharp
    (z := (t : ℂ)) (by simp)
  have hsharp' : starRingEnd ℂ
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)) =
      thetaCuspTailSecondDensityDeBrangesESharp (t : ℂ) := by
    simpa using hsharp
  unfold thetaCuspTailSecondDensityDeBrangesGap
  rw [← hsharp', Complex.normSq_conj]
  ring

private theorem completedDensityNoGo_boundary_current_nonneg_of_gap_pos
    (hgap : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      0 < thetaCuspTailSecondDensityDeBrangesGap z)
    (t : ℝ) :
    0 ≤ -4 * ((2 * (t : ℂ) *
          thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
        ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
          thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)) *
      starRingEnd ℂ
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im := by
  let g : ℝ → ℝ := fun y => thetaCuspTailSecondDensityDeBrangesGap
    ((t : ℂ) + (y : ℂ) * I)
  let D : ℝ := -4 * ((2 * (t : ℂ) *
        thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
      ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
        thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)) *
    starRingEnd ℂ
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im
  have hder : HasDerivAt g D 0 := by
    simpa [g, D] using completedDensityNoGo_vertical_gap_derivative t
  have hlim := hder.tendsto_slope_zero_right
  have hhalfN : ∀ᶠ y : ℝ in 𝓝 0, y < 1 / 2 :=
    isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 / 2))
  have hhalf : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 / 2 :=
    hhalfN.filter_mono inf_le_left
  have hnonneg : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 ≤ slope g 0 y := by
    filter_upwards [self_mem_nhdsWithin, hhalf] with y hypos hyhalf
    have hgy : 0 < g y := by
      dsimp [g]
      apply hgap
      · simpa using hypos
      · simpa using hyhalf
    have hg0 : g 0 = 0 := by
      simpa [g] using completedDensityNoGo_gap_ofReal t
    rw [slope_def_field, hg0, sub_zero, sub_zero]
    exact mul_nonneg hgy.le (inv_nonneg.mpr hypos.le)
  apply ge_of_tendsto hlim
  simpa [slope_def_field, zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hnonneg

private def completedDensityNoGo_thetaDensityDropFull (x : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun y => ((-4 * thetaCuspTailDerivative 3 y : ℝ) : ℂ)) x

private theorem completedDensityNoGo_integrable_thetaDensityDropFull :
    Integrable completedDensityNoGo_thetaDensityDropFull := by
  unfold completedDensityNoGo_thetaDensityDropFull
  have hcomplex : IntegrableOn
      (fun x : ℝ => ((-4 * thetaCuspTailDerivative 3 x : ℝ) : ℂ)) (Ioi 0) :=
    ((integrableOn_thetaCuspTailDerivative_Ioi 3).const_mul (-4)).ofReal
  exact hcomplex.integrable_indicator measurableSet_Ioi

private theorem completedDensityNoGo_fourier_thetaDensityDropFull_re (t : ℝ) :
    ((𝓕 completedDensityNoGo_thetaDensityDropFull) (t / (2 * Real.pi))).re =
      ∫ x : ℝ in Ioi 0,
        (-4 * thetaCuspTailDerivative 3 x) * Real.cos (t * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint : Integrable (fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * (t / (2 * Real.pi))) * I) •
        completedDensityNoGo_thetaDensityDropFull x) := by
    apply completedDensityNoGo_integrable_thetaDensityDropFull.bdd_mul (c := 1)
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        Complex.exp (↑(-2 * Real.pi * x * (t / (2 * Real.pi))) * I))).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp [Complex.div_im]
  calc
    (∫ x : ℝ,
      Complex.exp (↑(-2 * Real.pi * x * (t / (2 * Real.pi))) * I) •
        completedDensityNoGo_thetaDensityDropFull x).re =
        ∫ x : ℝ,
          (Complex.exp (↑(-2 * Real.pi * x * (t / (2 * Real.pi))) * I) •
            completedDensityNoGo_thetaDensityDropFull x).re := (integral_re hint).symm
    _ = ∫ x : ℝ in Ioi 0,
        (-4 * thetaCuspTailDerivative 3 x) * Real.cos (t * x) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · unfold completedDensityNoGo_thetaDensityDropFull
        rw [Set.indicator_of_mem hx]
        have harg : -2 * Real.pi * x * (t / (2 * Real.pi)) = -(t * x) := by
          field_simp [Real.pi_ne_zero]
        rw [harg, Set.indicator_of_mem hx]
        change (Complex.exp (↑(-(t * x)) * I) *
          ((-4 * thetaCuspTailDerivative 3 x : ℝ) : ℂ)).re = _
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Real.cos_neg]
        ring
      · unfold completedDensityNoGo_thetaDensityDropFull
        simp [Set.indicator, hx]

private theorem completedDensityNoGo_tendsto_densityDrop_cos_atTop_zero :
    Tendsto (fun t : ℝ => ∫ x : ℝ in Ioi 0,
      (-4 * thetaCuspTailDerivative 3 x) * Real.cos (t * x))
      atTop (𝓝 0) := by
  have hfour : Tendsto (𝓕 completedDensityNoGo_thetaDensityDropFull)
      atTop (𝓝 (0 : ℂ)) :=
    (Real.zero_at_infty_fourier completedDensityNoGo_thetaDensityDropFull).mono_left
      atTop_le_cocompact
  have hscale : Tendsto (fun t : ℝ => t / (2 * Real.pi)) atTop atTop := by
    have h : Tendsto (fun t : ℝ => (2 * Real.pi)⁻¹ * t) atTop atTop :=
      tendsto_id.const_mul_atTop
        (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
    simpa [div_eq_inv_mul] using h
  have hcomp := hfour.comp hscale
  have hre : Tendsto
      (fun t : ℝ => ((𝓕 completedDensityNoGo_thetaDensityDropFull)
        (t / (2 * Real.pi))).re) atTop (𝓝 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp hcomp
  convert hre using 1
  funext t
  exact (completedDensityNoGo_fourier_thetaDensityDropFull_re t).symm

/-- Canonical positive mass of the derivative-drop source that controls the odd boundary channel. -/
def thetaCuspTailThirdDerivativeDropMass : ℝ :=
  ∫ x : ℝ in Ioi 0, -4 * thetaCuspTailDerivative 3 x

/-- The derivative-drop source has strictly positive total mass. -/
theorem thetaCuspTailThirdDerivativeDropMass_pos :
    0 < thetaCuspTailThirdDerivativeDropMass := by
  let q : ℝ → ℝ := fun x => -4 * thetaCuspTailDerivative 3 x
  have hqcont : Continuous q :=
    continuous_const.mul (differentiable_thetaCuspTailDerivative 3).continuous
  have hqint : IntegrableOn q (Ioi 0) :=
    (integrableOn_thetaCuspTailDerivative_Ioi 3).const_mul (-4)
  have hqnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (mul_pos_of_neg_of_neg (by norm_num)
      (thetaCuspTailDerivative_three_neg hx.le)).le
  unfold thetaCuspTailThirdDerivativeDropMass
  apply (setIntegral_pos_iff_support_of_nonneg_ae hqnn hqint).2
  have hopen : IsOpen (Function.support q ∩ Ioi (0 : ℝ)) :=
    hqcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  exact (mul_pos_of_neg_of_neg (by norm_num)
    (thetaCuspTailDerivative_three_neg (x := 1) (by norm_num))).ne'

private theorem completedDensityNoGo_density_sine_scaled_eq_mass_sub_cos (t : ℝ) :
    t * (∫ x : ℝ in Ioi 0,
      thetaCuspTailSecondDensity x * Real.sin (t * x)) =
      thetaCuspTailThirdDerivativeDropMass -
        ∫ x : ℝ in Ioi 0,
          (-4 * thetaCuspTailDerivative 3 x) * Real.cos (t * x) := by
  rw [thetaCuspTailSecondDensity_sine_identity]
  unfold thetaCuspTailThirdDerivativeDropMass
  have hq : IntegrableOn (fun x : ℝ =>
      -4 * thetaCuspTailDerivative 3 x) (Ioi 0) :=
    (integrableOn_thetaCuspTailDerivative_Ioi 3).const_mul (-4)
  have hqcos : IntegrableOn (fun x : ℝ =>
      (-4 * thetaCuspTailDerivative 3 x) * Real.cos (t * x)) (Ioi 0) := by
    simpa only [MeasureTheory.IntegrableOn, mul_assoc, mul_comm, mul_left_comm] using
      (integrableOn_cos_mul_thetaCuspTailDerivative 3 t).const_mul (-4)
  rw [← integral_sub hq hqcos]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The scaled sine channel converges to the strictly positive derivative-drop mass. -/
theorem tendsto_thetaCuspTailSecondDensity_sine_scaled_atTop_dropMass :
    Tendsto (fun t : ℝ => t * (∫ x : ℝ in Ioi 0,
      thetaCuspTailSecondDensity x * Real.sin (t * x)))
      atTop (𝓝 thetaCuspTailThirdDerivativeDropMass) := by
  have h := (tendsto_const_nhds (x := thetaCuspTailThirdDerivativeDropMass)
    (f := atTop)).sub completedDensityNoGo_tendsto_densityDrop_cos_atTop_zero
  have h' := h.congr' (Eventually.of_forall fun t =>
    (completedDensityNoGo_density_sine_scaled_eq_mass_sub_cos t).symm)
  simpa only [sub_zero] using h'

private theorem completedDensityNoGo_E_im_over_t_eq
    {t : ℝ} (ht : t ≠ 0) :
    (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im / t =
      (1 + 1 / (4 * t ^ (2 : ℕ))) *
        (t * (∫ x : ℝ in Ioi 0,
          thetaCuspTailSecondDensity x * Real.sin (t * x))) := by
  have hq : (t : ℂ) ^ (2 : ℕ) + 1 / 4 = ((t ^ (2 : ℕ) + 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold thetaCuspTailSecondDensityDeBrangesE
  rw [hq]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rw [show ((1 / 4 : ℂ)).im = 0 by norm_num, sub_zero,
    thetaCuspTailSecondDensityPhaseValue_im_ofReal_eq_sine]
  field_simp

/-- The source-selected de Branges imaginary channel has positive linear asymptotic mass. -/
theorem tendsto_thetaCuspTailSecondDensityDeBrangesE_im_div_atTop_dropMass :
    Tendsto (fun t : ℝ =>
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im / t)
      atTop (𝓝 thetaCuspTailThirdDerivativeDropMass) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hfactor : Tendsto (fun t : ℝ => 1 + 1 / (4 * t ^ (2 : ℕ)))
      atTop (𝓝 1) := by
    have hsquare := hinv.pow 2
    have hc : Tendsto (fun _ : ℝ => (1 / 4 : ℝ)) atTop (𝓝 (1 / 4)) :=
      tendsto_const_nhds
    have hquarter :
        Tendsto (fun t : ℝ => (1 / 4 : ℝ) * (t⁻¹) ^ (2 : ℕ)) atTop (𝓝 0) := by
      simpa using hc.mul hsquare
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_assoc,
      mul_comm, mul_left_comm, one_mul, add_zero] using hone.add hquarter
  have hprod := hfactor.mul tendsto_thetaCuspTailSecondDensity_sine_scaled_atTop_dropMass
  have hprod' : Tendsto (fun t : ℝ =>
      (1 + 1 / (4 * t ^ (2 : ℕ))) *
        (t * (∫ x : ℝ in Ioi 0,
          thetaCuspTailSecondDensity x * Real.sin (t * x))))
      atTop (𝓝 thetaCuspTailThirdDerivativeDropMass) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  exact (completedDensityNoGo_E_im_over_t_eq ht).symm

private theorem completedDensityNoGo_tendsto_mul_XiC_re_atTop_zero :
    Tendsto (fun t : ℝ => t * (XiC (t : ℂ)).re) atTop (𝓝 0) := by
  let S : 𝓢(ℝ, ℂ) := 𝓕 xiThetaSchwartzSource
  obtain ⟨C, hC, hdec⟩ := S.decay 2 0
  apply squeeze_zero_norm' (a := fun t : ℝ => C / t)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hdec' : t ^ (2 : ℕ) * ‖XiC (t : ℂ)‖ ≤ C := by
      have := hdec t
      simpa only [S, norm_iteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (le_trans zero_le_one ht),
        fourier_xiThetaSchwartzSource] using this
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_trans zero_le_one ht)]
    apply (le_div_iff₀ htpos).2
    calc
      t * |(XiC (t : ℂ)).re| * t = t ^ (2 : ℕ) * |(XiC (t : ℂ)).re| := by ring
      _ ≤ t ^ (2 : ℕ) * ‖XiC (t : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (sq_nonneg t)
      _ ≤ C := hdec'
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul C)

private theorem completedDensityNoGo_E_re_div_im_eq
    {t : ℝ} (ht : 0 < t) :
    (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re /
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im =
      (2 * (t * (XiC (t : ℂ)).re)) /
        ((thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im / t) := by
  rw [completedDensityNoGo_E_re_ofReal]
  have him : (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ≠ 0 :=
    (thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht).ne'
  field_simp

/-- The real-axis source-selected phase ratio asymptotically orthogonalizes to zero. -/
theorem tendsto_thetaCuspTailSecondDensityDeBrangesE_re_div_im_atTop_zero :
    Tendsto (fun t : ℝ =>
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re /
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im)
      atTop (𝓝 0) := by
  have hnum : Tendsto (fun t : ℝ => 2 * (t * (XiC (t : ℂ)).re))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul completedDensityNoGo_tendsto_mul_XiC_re_atTop_zero)
  have hmass : thetaCuspTailThirdDerivativeDropMass ≠ 0 :=
    thetaCuspTailThirdDerivativeDropMass_pos.ne'
  have hquot := hnum.div
    tendsto_thetaCuspTailSecondDensityDeBrangesE_im_div_atTop_dropMass hmass
  have hquot' : Tendsto (fun t : ℝ =>
      (2 * (t * (XiC (t : ℂ)).re)) /
        ((thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im / t))
      atTop (𝓝 0) := by
    simpa only [Pi.div_def, zero_div] using hquot
  apply hquot'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (completedDensityNoGo_E_re_div_im_eq ht).symm

private theorem completedDensityNoGo_exists_pos_E_re_div_im :
    ∃ t : ℝ, 0 < t ∧
      0 < (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re /
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im := by
  have hzero : 0 < (XiC (0 : ℂ)).re := by
    change 0 < (XiC ((0 : ℝ) : ℂ)).re
    rw [XiC_ofReal]
    simpa using Xi_zero_pos
  have hcont : ContinuousAt (fun t : ℝ => (XiC (t : ℂ)).re) 0 :=
    (Complex.continuous_re.comp
      (XiC_analytic.continuous.comp RCLike.continuous_ofReal)).continuousAt
  have hmem : {t : ℝ | 0 < (XiC (t : ℂ)).re} ∈ 𝓝 0 :=
    hcont (Ioi_mem_nhds hzero)
  rcases Metric.mem_nhds_iff.mp hmem with ⟨ε, hε, hball⟩
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    change dist t (0 : ℝ) < ε
    rw [Real.dist_eq]
    dsimp [t]
    rw [sub_zero, abs_of_pos ht]
    exact half_lt_self hε
  have hXi : 0 < (XiC (t : ℂ)).re := hball htball
  have hre : 0 < (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re := by
    rw [completedDensityNoGo_E_re_ofReal]
    positivity
  have him : 0 < (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im :=
    thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht
  exact ⟨t, ht, div_pos hre him⟩

private theorem completedDensityNoGo_hasDerivAt_E_re_div_im
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ =>
        (thetaCuspTailSecondDensityDeBrangesE (s : ℂ)).re /
          (thetaCuspTailSecondDensityDeBrangesE (s : ℂ)).im)
      ((-4 * ((2 * (t : ℂ) *
              thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
            ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
              thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)) *
          starRingEnd ℂ
            (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im) /
        (4 * (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ^ (2 : ℕ))) t := by
  let E' : ℂ :=
    2 * (t : ℂ) * thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
      ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
        thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)
  have hE : HasDerivAt
      (fun s : ℝ => thetaCuspTailSecondDensityDeBrangesE (s : ℂ)) E' t := by
    simpa [E'] using (completedDensityNoGo_hasDerivAt_E (z := (t : ℂ)) (by simp)).comp_ofReal
  have hre : HasDerivAt
      (fun s : ℝ => (thetaCuspTailSecondDensityDeBrangesE (s : ℂ)).re)
      E'.re t := by
    simpa using (hasDerivAt_const t Complex.reCLM).clm_apply hE
  have him : HasDerivAt
      (fun s : ℝ => (thetaCuspTailSecondDensityDeBrangesE (s : ℂ)).im)
      E'.im t := by
    simpa using (hasDerivAt_const t Complex.imCLM).clm_apply hE
  have himne : (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ≠ 0 :=
    (thetaCuspTailSecondDensityDeBrangesE_im_ofReal_pos ht).ne'
  have hratio := hre.div him himne
  exact hratio.congr_deriv (by
    have hE'eq : ((2 * (t : ℂ) * thetaCuspTailSecondDensityPhaseValue (t : ℂ) * 4 +
        ((t : ℂ) ^ (2 : ℕ) * 4 + 1) * thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)) / 4 : ℂ) =
        E' := by
      dsimp only [E']
      ring
    clear_value E'
    simp only [mul_im, Complex.conj_re, Complex.conj_im]
    field_simp
    rw [hE'eq]
    ring)

private theorem completedDensityNoGo_monotoneOn_E_re_div_im_of_gap_pos
    (hgap : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      0 < thetaCuspTailSecondDensityDeBrangesGap z) :
    MonotoneOn
      (fun t : ℝ =>
        (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re /
          (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im)
      (Ioi 0) := by
  let J : ℝ → ℝ := fun t =>
    ((-4 * ((2 * (t : ℂ) *
              thetaCuspTailSecondDensityPhaseValue (t : ℂ) +
            ((t : ℂ) ^ (2 : ℕ) + 1 / 4) *
              thetaCuspTailSecondDensityPhaseDerivative (t : ℂ)) *
          starRingEnd ℂ
            (thetaCuspTailSecondDensityDeBrangesE (t : ℂ))).im) /
      (4 * (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ^ (2 : ℕ)))
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ioi (0 : ℝ)) (f' := J) ?_ ?_ ?_
  · intro t ht
    exact (completedDensityNoGo_hasDerivAt_E_re_div_im ht).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro t ht
    exact (completedDensityNoGo_hasDerivAt_E_re_div_im ht).hasDerivWithinAt
  · rw [interior_Ioi]
    intro t ht
    dsimp [J]
    exact div_nonneg (completedDensityNoGo_boundary_current_nonneg_of_gap_pos hgap t)
      (mul_nonneg (by norm_num) (sq_nonneg _))

/-- The completed-density source-selected de Branges gap cannot be strictly positive on the
open critical half-strip. Its boundary current would force a positive real-axis phase ratio to
be nondecreasing, while theta-source mass and Schwartz decay force that ratio to tend to zero. -/
theorem not_forall_thetaCuspTailSecondDensityDeBrangesGap_pos :
    ¬ ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      0 < thetaCuspTailSecondDensityDeBrangesGap z := by
  intro hgap
  have hmono := completedDensityNoGo_monotoneOn_E_re_div_im_of_gap_pos hgap
  obtain ⟨t, ht, hratio⟩ := completedDensityNoGo_exists_pos_E_re_div_im
  have hevent : ∀ᶠ s : ℝ in atTop,
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re /
          (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ≤
        (thetaCuspTailSecondDensityDeBrangesE (s : ℂ)).re /
          (thetaCuspTailSecondDensityDeBrangesE (s : ℂ)).im := by
    filter_upwards [eventually_ge_atTop t] with s hts
    exact hmono ht (lt_of_lt_of_le ht hts) hts
  have hle :
      (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).re /
          (thetaCuspTailSecondDensityDeBrangesE (t : ℂ)).im ≤ 0 :=
    ge_of_tendsto
      tendsto_thetaCuspTailSecondDensityDeBrangesE_re_div_im_atTop_zero hevent
  exact (not_lt_of_ge hle) hratio

end


end RHTower
