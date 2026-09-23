import GaloisForLFunctions.RHTower.SuzukiScrewDistributionalAtoms
import GaloisForLFunctions.RHTower.SuzukiFinitePartTranslationBridge
import GaloisForLFunctions.RHTower.SuzukiPrimeHankelCarrier
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Suzuki equation (2.4)

This module proves Suzuki's literal singular logarithmic integration-by-parts identity on the
source-locked smooth aperture core. The proof removes the Cauchy singularity with the continuous
divided slope, identifies its finite part with the already-derived translation-difference energy,
computes the autocorrelation Hessian by convolution differentiation and whole-line integration by
parts, and finally shears back to the published double interval integral.
-/

open MeasureTheory Set intervalIntegral
open scoped Topology Convolution

namespace GaloisForLFunctions.RHTower

noncomputable def suzukiCoreAutocorrelation {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) : ℝ → ℝ :=
  screwCrossCorr u u

private theorem core_square_integrable' {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Integrable (fun x : ℝ => u x ^ (2 : ℕ)) := by
  have hsupp : Function.support (fun x : ℝ => u x ^ (2 : ℕ)) ⊆
      Icc (-u.supportRadius) u.supportRadius := by
    intro x hx
    exact u.support_subset (fun hzero => hx (by simp [hzero]))
  exact (u.continuous.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)

private theorem core_cross_integrable' {a : ℝ} (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    Integrable (fun x : ℝ => u x * u (x + h)) := by
  have hsupp : HasCompactSupport (fun x : ℝ => u x * u (x + h)) :=
    u.hasCompactSupport.mul_right
  exact (u.continuous.mul (u.continuous.comp (continuous_id.add continuous_const)))
    |>.integrable_of_hasCompactSupport hsupp

theorem suzukiCoreAutocorrelation_zero {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    suzukiCoreAutocorrelation u 0 = ∫ x : ℝ, u x ^ (2 : ℕ) := by
  unfold suzukiCoreAutocorrelation screwCrossCorr
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [zero_add]
  ring

theorem suzukiCoreAutocorrelation_neg {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    suzukiCoreAutocorrelation u (-h) = suzukiCoreAutocorrelation u h := by
  unfold suzukiCoreAutocorrelation screwCrossCorr
  have hs := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => u x * u (x - h)) h
  calc
    (∫ y : ℝ, u y * u (-h + y)) = ∫ y : ℝ, u y * u (y - h) := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      change u y * u (-h + y) = u y * u (y - h)
      congr 1
      ring
    _ = ∫ y : ℝ, u (y + h) * u y := by
      symm
      simpa only [add_sub_cancel_right] using hs
    _ = ∫ y : ℝ, u y * u (h + y) := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      change u (y + h) * u y = u y * u (h + y)
      rw [add_comm y h, mul_comm]

theorem suzukiRealTranslationDifferenceEnergy_eq_autocorrelation
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    suzukiRealTranslationDifferenceEnergy u h =
      2 * (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h) := by
  have hu2 := core_square_integrable' u
  have hushift : Integrable (fun x : ℝ => u (x + h) ^ (2 : ℕ)) := hu2.comp_add_right h
  have hcross := core_cross_integrable' u h
  have hshift : (∫ x : ℝ, u (x + h) ^ (2 : ℕ)) = ∫ x : ℝ, u x ^ (2 : ℕ) := by
    simpa using integral_add_right_eq_self (μ := volume) (fun x : ℝ => u x ^ (2 : ℕ)) h
  have hexpand :
      (∫ x : ℝ, (u x - u (x + h)) ^ (2 : ℕ)) =
        (∫ x : ℝ, u x ^ (2 : ℕ)) + (∫ x : ℝ, u (x + h) ^ (2 : ℕ)) -
          2 * ∫ x : ℝ, u x * u (x + h) := by
    calc
      (∫ x : ℝ, (u x - u (x + h)) ^ (2 : ℕ)) =
          ∫ x : ℝ, (u x ^ (2 : ℕ) + u (x + h) ^ (2 : ℕ)) - 2 * (u x * u (x + h)) := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            ring
      _ = (∫ x : ℝ, u x ^ (2 : ℕ) + u (x + h) ^ (2 : ℕ)) -
          ∫ x : ℝ, 2 * (u x * u (x + h)) :=
        integral_sub (hu2.add hushift) (hcross.const_mul 2)
      _ = (∫ x : ℝ, u x ^ (2 : ℕ)) + (∫ x : ℝ, u (x + h) ^ (2 : ℕ)) -
          2 * ∫ x : ℝ, u x * u (x + h) := by
        rw [MeasureTheory.integral_add hu2 hushift,
          MeasureTheory.integral_const_mul]
  rw [suzukiRealTranslationDifferenceEnergy, hexpand, hshift,
    suzukiCoreAutocorrelation_zero]
  unfold suzukiCoreAutocorrelation screwCrossCorr
  have hcrossComm : (∫ x : ℝ, u x * u (x + h)) =
      ∫ x : ℝ, u x * u (h + x) := by
    apply MeasureTheory.integral_congr_ae
    exact ae_of_all _ fun x => by
      change u x * u (x + h) = u x * u (h + x)
      rw [add_comm x h]
  rw [hcrossComm]
  ring

private theorem intervalIntegral_congr_Ioo' {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ t ∈ Ioo a b, f t = g t) : (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  refine intervalIntegral.integral_congr_ae ?_
  have h1 : ({b}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton b)
  filter_upwards [h1] with t ht hmem
  rw [Set.uIoc_of_le hab] at hmem
  exact h t ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using ht)⟩

theorem centeredCauchyFinitePart_suzukiCoreAutocorrelation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    centeredCauchyFinitePart (2 * A.1) (suzukiCoreAutocorrelation u) =
      -2 * suzukiFinitePartEnergy A.1 u := by
  let R : ℝ := 2 * A.1
  let c : ℝ → ℝ := suzukiCoreAutocorrelation u
  let D : ℝ → ℝ := suzukiRealTranslationDifferenceEnergy u
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hrightPoint : ∀ h ∈ Ioo 0 R,
      dslope c 0 h = -(1 / 2 : ℝ) * (D h / h) := by
    intro h hh
    have hh0 : h ≠ 0 := hh.1.ne'
    rw [dslope_of_ne c hh0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    dsimp only [c, D]
    rw [suzukiRealTranslationDifferenceEnergy_eq_autocorrelation]
    ring
  have hleftPoint : ∀ h ∈ Ioo 0 R,
      dslope c 0 (-h) = (1 / 2 : ℝ) * (D h / h) := by
    intro h hh
    have hh0 : h ≠ 0 := hh.1.ne'
    rw [dslope_of_ne c (neg_ne_zero.mpr hh0)]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    dsimp only [c, D]
    rw [suzukiCoreAutocorrelation_neg,
      suzukiRealTranslationDifferenceEnergy_eq_autocorrelation]
    field_simp
    ring
  have hright :
      (∫ h in 0..R, dslope c 0 h) =
        -(1 / 2 : ℝ) * ∫ h in 0..R, D h / h := by
    rw [intervalIntegral_congr_Ioo' hR.le hrightPoint,
      ← intervalIntegral.integral_const_mul]
  have hleft :
      (∫ h in (-R)..0, dslope c 0 h) =
        (1 / 2 : ℝ) * ∫ h in 0..R, D h / h := by
    have hneg := intervalIntegral.integral_comp_neg
      (f := fun h => dslope c 0 h) (a := (0 : ℝ)) (b := R)
    simp only [neg_zero] at hneg
    rw [← hneg]
    rw [intervalIntegral_congr_Ioo' hR.le hleftPoint,
      ← intervalIntegral.integral_const_mul]
  have hc0 : c 0 = ∫ x : ℝ, u x ^ (2 : ℕ) := by
    exact suzukiCoreAutocorrelation_zero u
  have henergy := suzukiFinitePartEnergy_eq_translationDifference A u
  dsimp only [R, c, D] at hright hleft hc0 ⊢
  unfold centeredCauchyFinitePart
  rw [hright, hleft, hc0]
  linarith

theorem realConvolution_negReflect_eq_screwCrossCorr
    (u v : ℝ → ℝ) (t : ℝ) :
    (negReflect u ⋆[ContinuousLinearMap.mul ℝ ℝ] v) t = screwCrossCorr u v t := by
  calc
    (negReflect u ⋆[ContinuousLinearMap.mul ℝ ℝ] v) t =
        screwConvolve (negReflect u) v t := rfl
    _ = screwCrossCorr (negReflect (negReflect u)) v t :=
      (screwCrossCorr_negReflect (negReflect u) v t).symm
    _ = screwCrossCorr u v t := by
      unfold screwCrossCorr negReflect
      simp only [neg_neg]

theorem hasDerivAt_suzukiCoreAutocorrelation
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) (t : ℝ) :
    HasDerivAt (suzukiCoreAutocorrelation u)
      (screwCrossCorr u (deriv u) t) t := by
  have hnegLoc : LocallyIntegrable (negReflect (u : ℝ → ℝ)) volume :=
    (u.continuous.comp continuous_neg).locallyIntegrable
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℝ) := u.smooth.of_le (by simp)
  have hconv := u.hasCompactSupport.hasDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hnegLoc hu1 t
  rw [realConvolution_negReflect_eq_screwCrossCorr] at hconv
  have hfun : (negReflect (u : ℝ → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ] (u : ℝ → ℝ)) =
      suzukiCoreAutocorrelation u := by
    funext x
    exact realConvolution_negReflect_eq_screwCrossCorr u u x
  rw [hfun] at hconv
  exact hconv

theorem hasDerivAt_suzukiCoreAutocorrelation_derivative
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) (t : ℝ) :
    HasDerivAt (fun s => screwCrossCorr u (deriv u) s)
      (screwCrossCorr u (deriv (deriv u)) t) t := by
  have hnegLoc : LocallyIntegrable (negReflect (u : ℝ → ℝ)) volume :=
    (u.continuous.comp continuous_neg).locallyIntegrable
  have hduCompact : HasCompactSupport (deriv (u : ℝ → ℝ)) := u.hasCompactSupport.deriv
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℝ) := u.smooth.of_le (by
    show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hdu1 : ContDiff ℝ 1 (deriv (u : ℝ → ℝ)) := by
    exact hu2.deriv'
  have hconv := hduCompact.hasDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hnegLoc hdu1 t
  rw [realConvolution_negReflect_eq_screwCrossCorr] at hconv
  have hfun :
      (negReflect (u : ℝ → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ] deriv (u : ℝ → ℝ)) =
        fun s => screwCrossCorr u (deriv u) s := by
    funext x
    exact realConvolution_negReflect_eq_screwCrossCorr u (deriv u) x
  rw [hfun] at hconv
  exact hconv

theorem suzukiCoreAutocorrelation_secondDerivative_eq_neg_derivativeCorrelation
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) (t : ℝ) :
    screwCrossCorr u (deriv (deriv u)) t =
      -screwCrossCorr (deriv u) (deriv u) t := by
  have huD : ∀ x, HasDerivAt (u : ℝ → ℝ) (deriv u x) x := fun x =>
    (u.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℝ) := u.smooth.of_le (by
    show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hduD : ∀ x, HasDerivAt (deriv (u : ℝ → ℝ)) (deriv (deriv u) x) x := fun x =>
    (hu2.differentiable_deriv_two x).hasDerivAt
  let v : ℝ → ℝ := fun y => deriv u (t + y)
  let v' : ℝ → ℝ := fun y => deriv (deriv u) (t + y)
  have hvD : ∀ y, HasDerivAt v (v' y) y := by
    intro y
    dsimp only [v, v']
    simpa only [Function.comp_def, zero_add, one_mul, mul_one] using
      (hduD (t + y)).comp y ((hasDerivAt_const y t).add (hasDerivAt_id y))
  have hduCont : Continuous (deriv (u : ℝ → ℝ)) :=
    u.smooth.continuous_deriv (by simp)
  have hdu1 : ContDiff ℝ 1 (deriv (u : ℝ → ℝ)) := by
    exact hu2.deriv'
  have hdduCont : Continuous (deriv (deriv (u : ℝ → ℝ))) :=
    hdu1.continuous_deriv_one
  have huCompact := u.hasCompactSupport
  have hduCompact : HasCompactSupport (deriv (u : ℝ → ℝ)) := huCompact.deriv
  have huv' : Integrable ((u : ℝ → ℝ) * v') := by
    exact (u.continuous.mul (hdduCont.comp (continuous_const.add continuous_id)))
      |>.integrable_of_hasCompactSupport huCompact.mul_right
  have hduv : Integrable (deriv (u : ℝ → ℝ) * v) := by
    exact (hduCont.mul (hduCont.comp (continuous_const.add continuous_id)))
      |>.integrable_of_hasCompactSupport hduCompact.mul_right
  have huv : Integrable ((u : ℝ → ℝ) * v) := by
    exact (u.continuous.mul (hduCont.comp (continuous_const.add continuous_id)))
      |>.integrable_of_hasCompactSupport huCompact.mul_right
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := (u : ℝ → ℝ)) (u' := deriv u) (v := v) (v' := v')
    (fun x _ => huD x) (fun x _ => hvD x) huv' hduv huv
  unfold screwCrossCorr
  change (∫ y : ℝ, u y * deriv (deriv u) (t + y)) =
    -(∫ y : ℝ, deriv u y * deriv u (t + y))
  simpa only [Pi.mul_apply, v, v'] using hibp

theorem core_tsupport_subset_radius {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    tsupport (u : ℝ → ℝ) ⊆ Icc (-u.supportRadius) u.supportRadius :=
  closure_minimal u.support_subset isClosed_Icc

theorem core_deriv_support_subset_radius {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Function.support (deriv (u : ℝ → ℝ)) ⊆ Icc (-u.supportRadius) u.supportRadius :=
  support_deriv_subset.trans (core_tsupport_subset_radius u)

theorem core_secondDeriv_support_subset_radius {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) :
    Function.support (deriv (deriv (u : ℝ → ℝ))) ⊆
      Icc (-u.supportRadius) u.supportRadius :=
  support_deriv_subset.trans (tsupport_deriv_subset.trans (core_tsupport_subset_radius u))

theorem screwCrossCorr_eq_zero_of_support_radius_pos
    {r t : ℝ} {f g : ℝ → ℝ}
    (hf : Function.support f ⊆ Icc (-r) r)
    (hg : Function.support g ⊆ Icc (-r) r)
    (hrt : 2 * r < t) :
    screwCrossCorr f g t = 0 := by
  unfold screwCrossCorr
  rw [show (fun y : ℝ => f y * g (t + y)) = 0 by
    funext y
    by_cases hfy : f y = 0
    · simp [hfy]
    have hyr := hf hfy
    have hgy : g (t + y) = 0 := by
      by_contra hne
      have htr := hg hne
      linarith [hyr.1, htr.2]
    simp [hgy]]
  change (∫ _y : ℝ, (0 : ℝ)) = 0
  exact MeasureTheory.integral_zero ℝ ℝ

theorem screwCrossCorr_eq_zero_of_support_radius_neg
    {r t : ℝ} {f g : ℝ → ℝ}
    (hf : Function.support f ⊆ Icc (-r) r)
    (hg : Function.support g ⊆ Icc (-r) r)
    (htr : t < -(2 * r)) :
    screwCrossCorr f g t = 0 := by
  unfold screwCrossCorr
  rw [show (fun y : ℝ => f y * g (t + y)) = 0 by
    funext y
    by_cases hfy : f y = 0
    · simp [hfy]
    have hyr := hf hfy
    have hgy : g (t + y) = 0 := by
      by_contra hne
      have htr' := hg hne
      linarith [hyr.2, htr'.1]
    simp [hgy]]
  change (∫ _y : ℝ, (0 : ℝ)) = 0
  exact MeasureTheory.integral_zero ℝ ℝ

theorem continuous_suzukiCoreAutocorrelation_secondDerivative
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Continuous (fun t => screwCrossCorr u (deriv (deriv u)) t) := by
  have hnegLoc : LocallyIntegrable (negReflect (u : ℝ → ℝ)) volume :=
    (u.continuous.comp continuous_neg).locallyIntegrable
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℝ) := u.smooth.of_le (by
    show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hdu1 : ContDiff ℝ 1 (deriv (u : ℝ → ℝ)) := by
    exact hu2.deriv'
  have hdduCont : Continuous (deriv (deriv (u : ℝ → ℝ))) :=
    hdu1.continuous_deriv_one
  have hdduCompact : HasCompactSupport (deriv (deriv (u : ℝ → ℝ))) :=
    u.hasCompactSupport.deriv.deriv
  have hconv := hdduCompact.continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hnegLoc hdduCont
  have hfun :
      (negReflect (u : ℝ → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        deriv (deriv (u : ℝ → ℝ))) =
        fun t => screwCrossCorr u (deriv (deriv u)) t := by
    funext t
    exact realConvolution_negReflect_eq_screwCrossCorr u (deriv (deriv u)) t
  rw [hfun] at hconv
  exact hconv

/-- Suzuki's published equation (2.4), in its one-variable autocorrelation form. -/
theorem suzuki_equation_two_four_correlation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ t in (-(2 * A.1))..(2 * A.1),
      |t| * Real.log |t| * screwCrossCorr (deriv u) (deriv u) t) =
      2 * suzukiFinitePartEnergy A.1 u - 2 * ∫ x : ℝ, u x ^ (2 : ℕ) := by
  let R : ℝ := 2 * A.1
  let c : ℝ → ℝ := suzukiCoreAutocorrelation u
  let c' : ℝ → ℝ := fun t => screwCrossCorr u (deriv u) t
  let c'' : ℝ → ℝ := fun t => screwCrossCorr u (deriv (deriv u)) t
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hcD : ∀ t, HasDerivAt c (c' t) t := by
    intro t
    exact hasDerivAt_suzukiCoreAutocorrelation u t
  have hc'D : ∀ t, HasDerivAt c' (c'' t) t := by
    intro t
    exact hasDerivAt_suzukiCoreAutocorrelation_derivative u t
  have hc''Cont : Continuous c'' :=
    continuous_suzukiCoreAutocorrelation_secondDerivative u
  have hsep : 2 * u.supportRadius < R := by
    dsimp only [R]
    linarith [u.supportRadius_lt_aperture]
  have hcR : c R = 0 := by
    exact screwCrossCorr_eq_zero_of_support_radius_pos u.support_subset u.support_subset hsep
  have hcnR : c (-R) = 0 := by
    exact screwCrossCorr_eq_zero_of_support_radius_neg u.support_subset u.support_subset (by
      linarith [hsep])
  have hc'R : c' R = 0 := by
    exact screwCrossCorr_eq_zero_of_support_radius_pos u.support_subset
      (core_deriv_support_subset_radius u) hsep
  have hc'nR : c' (-R) = 0 := by
    exact screwCrossCorr_eq_zero_of_support_radius_neg u.support_subset
      (core_deriv_support_subset_radius u) (by linarith [hsep])
  have hsing := integral_abs_mul_log_mul_secondDeriv hR c c' c''
    hcD hc'D hc''Cont hcR hcnR hc'R hc'nR
  have hfp := centeredCauchyFinitePart_suzukiCoreAutocorrelation A u
  have hc0 := suzukiCoreAutocorrelation_zero u
  have hcorr : (∫ t in (-R)..R,
      |t| * Real.log |t| * screwCrossCorr (deriv u) (deriv u) t) =
      -(∫ t in (-R)..R, |t| * Real.log |t| * c'' t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [c'']
    rw [suzukiCoreAutocorrelation_secondDerivative_eq_neg_derivativeCorrelation]
    ring
  dsimp only [R, c] at hsing hfp hc0 ⊢
  rw [hcorr]
  linarith

private theorem integrable_uncurry_suzukiLogDiffForm
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Integrable (Function.uncurry
      (diffFormIntegrand (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u)))
      (volume.prod volume) := by
  let r := u.supportRadius
  have hduSupp := core_deriv_support_subset_radius u
  have hsupp : Function.support (Function.uncurry
      (diffFormIntegrand (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u))) ⊆
      Icc (-r) r ×ˢ Icc (-r) r := by
    intro p hp
    have hy : deriv u p.2 ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffFormIntegrand]
      rw [hz]
      ring
    have hx : deriv u p.1 ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffFormIntegrand]
      rw [hz]
      ring
    exact ⟨hduSupp hx, hduSupp hy⟩
  have hcont : Continuous (Function.uncurry
      (diffFormIntegrand (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u))) := by
    have hduCont : Continuous (deriv (u : ℝ → ℝ)) :=
      u.smooth.continuous_deriv (by simp)
    change Continuous (fun p : ℝ × ℝ =>
      |p.1 - p.2| * Real.log |p.1 - p.2| * deriv u p.2 * deriv u p.1)
    fun_prop
  rw [← Measure.volume_eq_prod]
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsupp)

private theorem integrable_uncurry_suzukiLogDiffShear
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Integrable (Function.uncurry
      (diffShearIntegrand (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u)))
      (volume.prod volume) := by
  let r := u.supportRadius
  have hduSupp := core_deriv_support_subset_radius u
  have hsupp : Function.support (Function.uncurry
      (diffShearIntegrand (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u))) ⊆
      Icc (-r) r ×ˢ Icc (-(2 * r)) (2 * r) := by
    intro p hp
    have hy : deriv u p.1 ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffShearIntegrand]
      rw [hz]
      ring
    have hty : deriv u (p.2 + p.1) ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffShearIntegrand]
      rw [hz]
      ring
    have hyr := hduSupp hy
    have htyr := hduSupp hty
    exact ⟨hyr, by constructor <;> linarith [hyr.1, hyr.2, htyr.1, htyr.2]⟩
  have hcont : Continuous (Function.uncurry
      (diffShearIntegrand (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u))) := by
    have hduCont : Continuous (deriv (u : ℝ → ℝ)) :=
      u.smooth.continuous_deriv (by simp)
    change Continuous (fun p : ℝ × ℝ =>
      |p.2| * Real.log |p.2| * deriv u p.1 * deriv u (p.2 + p.1))
    fun_prop
  rw [← Measure.volume_eq_prod]
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsupp)

private theorem suzukiLogDerivativeCorrelation_interval_eq_integral
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ t in (-(2 * A.1))..(2 * A.1),
      |t| * Real.log |t| * screwCrossCorr (deriv u) (deriv u) t) =
      ∫ t : ℝ, |t| * Real.log |t| * screwCrossCorr (deriv u) (deriv u) t := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hcorr : screwCrossCorr (deriv u) (deriv u) t ≠ 0 := by
    intro hz
    exact ht (by simp [hz])
  have hsep : 2 * u.supportRadius < 2 * A.1 := by
    linarith [u.supportRadius_lt_aperture]
  have hduSupp := core_deriv_support_subset_radius u
  constructor
  · by_contra hneg
    have hz := screwCrossCorr_eq_zero_of_support_radius_neg hduSupp hduSupp
      (show t < -(2 * u.supportRadius) by linarith [hneg, hsep])
    exact hcorr hz
  · by_contra hpos
    have hz := screwCrossCorr_eq_zero_of_support_radius_pos hduSupp hduSupp
      (show 2 * u.supportRadius < t by linarith [hpos, hsep])
    exact hcorr hz

private theorem suzukiLogDerivativeDoubleInterval_eq_diffBilinForm
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
      |x - y| * Real.log |x - y| * deriv u y * deriv u x) =
      diffBilinForm (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u) := by
  have hduSuppRadius := core_deriv_support_subset_radius u
  have hduSuppA : Function.support (deriv (u : ℝ → ℝ)) ⊆ Ioc (-A.1) A.1 := by
    intro x hx
    have hxr := hduSuppRadius hx
    constructor <;> linarith [hxr.1, hxr.2, u.supportRadius_lt_aperture]
  have hinner (x : ℝ) :
      (∫ y in (-A.1)..A.1,
        |x - y| * Real.log |x - y| * deriv u y * deriv u x) =
        ∫ y : ℝ, |x - y| * Real.log |x - y| * deriv u y * deriv u x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro y hy
    have hdy : deriv u y ≠ 0 := by
      intro hz
      exact hy (by simp [hz])
    exact hduSuppA hdy
  rw [intervalIntegral.integral_congr (fun x _ => hinner x)]
  have houter :
      (∫ x in (-A.1)..A.1,
        ∫ y : ℝ, |x - y| * Real.log |x - y| * deriv u y * deriv u x) =
        ∫ x : ℝ, ∫ y : ℝ,
          |x - y| * Real.log |x - y| * deriv u y * deriv u x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hdx : deriv u x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact hduSuppA hdx
  rw [houter]
  rw [diffBilinForm_eq_integral_uncurry, Measure.volume_eq_prod ℝ ℝ]
  exact integral_integral (integrable_uncurry_suzukiLogDiffForm u)

/-- Suzuki's literal published equation (2.4) on the source-locked smooth aperture core. -/
theorem suzuki_equation_two_four
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
      |x - y| * Real.log |x - y| * deriv u y * deriv u x) =
      2 * suzukiFinitePartEnergy A.1 u - 2 * ∫ x : ℝ, u x ^ (2 : ℕ) := by
  rw [suzukiLogDerivativeDoubleInterval_eq_diffBilinForm A u,
    diffBilinForm_eq_correlation_pairing
      (fun t : ℝ => |t| * Real.log |t|) (deriv u) (deriv u)
      (integrable_uncurry_suzukiLogDiffForm u)
      (integrable_uncurry_suzukiLogDiffShear u),
    ← suzukiLogDerivativeCorrelation_interval_eq_integral A u,
    suzuki_equation_two_four_correlation A u]

end GaloisForLFunctions.RHTower
