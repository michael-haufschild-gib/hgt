import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail
import GaloisForLFunctions.CompletedArithmeticForms.WignerSpectralBand

/-!
# Integrated Fourier tails of the first theta atom

The radial Schläfli formula retains the signed argument derivative.
Integration by parts identifies its weighted tail with the complete
signed Bessel combination, including the endpoint contribution.
-/

open Complex Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

/-- Argument derivative of the radial imaginary-order Schläfli value. -/
def besselRadialValueDeriv (τ u : ℝ) : ℝ :=
  2 * (besselArgDeriv (((2 * τ : ℝ) : ℂ) * I) (2 * u)).re

/-- The radial carrier has its literal argument derivative. -/
theorem hasDerivAt_besselRadialValue {u : ℝ} (hu : 0 < u) (τ : ℝ) :
    HasDerivAt (besselRadialValue τ) (besselRadialValueDeriv τ u) u := by
  have hk := (hasDerivAt_modifiedBesselKOrder_arg (by linarith : 0 < 2 * u)
    (((2 * τ : ℝ) : ℂ) * I)).scomp u ((hasDerivAt_id u).const_mul 2)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hk
  apply hr.congr_deriv
  change ((2 * 1 : ℝ) • besselArgDeriv (((2 * τ : ℝ) : ℂ) * I) (2 * u)).re = _
  simp only [besselRadialValueDeriv, Complex.smul_re, smul_eq_mul, mul_one]

/-- Adjacent orders give an absolutely integrable expression for the argument derivative. -/
theorem besselRadialValueDeriv_eq {u : ℝ} (hu : 0 < u) (τ : ℝ) :
    besselRadialValueDeriv τ u =
      -((modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I + 1)).re +
        (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I - 1)).re) := by
  have hd := (d4BM_hasDerivAt_modifiedBesselKOrder_argument
    (by linarith : 0 < 2 * u) (((2 * τ : ℝ) : ℂ) * I)).unique
      (hasDerivAt_modifiedBesselKOrder_arg (by linarith : 0 < 2 * u)
        (((2 * τ : ℝ) : ℂ) * I))
  change -(1 / 2 : ℂ) * (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I + 1) +
    modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I - 1)) =
    besselArgDeriv (((2 * τ : ℝ) : ℂ) * I) (2 * u) at hd
  unfold besselRadialValueDeriv
  rw [← hd]
  simp only [Complex.mul_re, Complex.neg_re, Complex.div_re, Complex.one_re,
    Complex.re_ofNat, Complex.one_im, Complex.im_ofNat, Complex.normSq_ofNat,
    Complex.add_re, Complex.add_im, Complex.neg_im, Complex.div_im]
  ring

/-- Every fixed complex order has absolutely convergent power tails. -/
theorem integrableOn_rpow_smul_besselOrder {q p : ℝ} (hq : 1 ≤ q)
    (hp : -1 < p) (ν : ℂ) :
    IntegrableOn (fun u : ℝ => (u ^ p) • modifiedBesselKOrder (2 * u) ν) (Ioi q) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-2 * u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow hp (show (1 : ℝ) ≤ 1 from le_rfl)
        (show (0 : ℝ) < 2 by norm_num))
  have he := (hg.mono_set (show Ioi q ⊆ Ioi (0 : ℝ) from
    fun u hu => lt_of_lt_of_le zero_lt_one (hq.trans hu.le))).const_mul
      (Real.exp 1 * besselOrderUnitMass ν)
  have hc : ContinuousOn (fun u : ℝ => (u ^ p) • modifiedBesselKOrder (2 * u) ν)
      (Ioi q) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (hq.trans hu.le)
    have hk := (hasDerivAt_modifiedBesselKOrder_arg (by linarith : 0 < 2 * u) ν).continuousAt.comp' (f := fun v : ℝ => 2 * v) (x := u) (by fun_prop)
    exact ((Real.continuousAt_rpow_const u p (Or.inl hu0.ne')).smul hk).continuousWithinAt
  refine he.mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := zero_le_one.trans (hq.trans hu.le)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0 p)]
  calc
    _ ≤ u ^ p * (Real.exp (1 - 2 * u) * besselOrderUnitMass ν) :=
      mul_le_mul_of_nonneg_left
        (norm_modifiedBesselKOrder_le_exp (by have hu1 := hq.trans hu.le; linarith : 1 ≤ 2 * u) ν)
        (Real.rpow_nonneg hu0 p)
    _ = _ := by rw [show 1 - 2 * u = 1 + (-2 * u) by ring, Real.exp_add]; ring

theorem integrableOn_rpow_mul_besselRadialValueDeriv {q p : ℝ} (hq : 1 ≤ q)
    (hp : -1 < p) (τ : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ p * besselRadialValueDeriv τ u) (Ioi q) := by
  have hplus := (integrableOn_rpow_smul_besselOrder hq hp
    ((((2 * τ : ℝ) : ℂ) * I) + 1)).re
  have hminus := (integrableOn_rpow_smul_besselOrder hq hp
    ((((2 * τ : ℝ) : ℂ) * I) - 1)).re
  have hi : IntegrableOn (fun u : ℝ =>
      -((u ^ p • modifiedBesselKOrder (2 * u) ((((2 * τ : ℝ) : ℂ) * I) + 1)).re +
        (u ^ p • modifiedBesselKOrder (2 * u) ((((2 * τ : ℝ) : ℂ) * I) - 1)).re))
      (Ioi q) := (hplus.add hminus).neg
  refine hi.congr_fun ?_ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [besselRadialValueDeriv_eq (lt_of_lt_of_le zero_lt_one (hq.trans hu.le)) τ]
  simp only [Complex.smul_re, smul_eq_mul]
  ring

theorem tendsto_rpow_mul_besselRadialValue_zero (p τ : ℝ) :
    Tendsto (fun u : ℝ => u ^ p * besselRadialValue τ u) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => besselPowerTailCost p τ * Real.exp (-u))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot |>.const_mul (besselPowerTailCost p τ)
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  exact norm_besselPowerIntegrand_le hu p τ

/-- Integration by parts retains the endpoint of the signed argument derivative. -/
theorem integral_rpow_mul_besselRadialValueDeriv {q p : ℝ} (hq : 1 < q)
    (hp : 0 < p) (τ : ℝ) :
    (∫ u in Ioi q, u ^ p * besselRadialValueDeriv τ u) =
      -(q ^ p * besselRadialValue τ q) - p * besselPowerTail (p - 1) τ q := by
  have hi := integrableOn_besselPowerIntegrand hq.le (p - 1) τ
  have hj := integrableOn_rpow_mul_besselRadialValueDeriv hq.le (by linarith : -1 < p) τ
  have hd (u : ℝ) (hu : u ∈ Ici q) :
      HasDerivAt (fun v : ℝ => v ^ p * besselRadialValue τ v)
        (p * (u ^ (p - 1) * besselRadialValue τ u) +
          u ^ p * besselRadialValueDeriv τ u) u := by
    have hu0 : 0 < u := zero_lt_one.trans (hq.trans_le hu)
    have h := (Real.hasDerivAt_rpow_const (Or.inl hu0.ne') :
      HasDerivAt (fun v : ℝ => v ^ p) (p * u ^ (p - 1)) u).mul
        (hasDerivAt_besselRadialValue hu0 τ)
    apply h.congr_deriv
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd ((hi.const_mul p).add hj)
    (tendsto_rpow_mul_besselRadialValue_zero p τ)
  rw [integral_add (hi.const_mul p) hj, integral_const_mul] at h
  change p * besselPowerTail (p - 1) τ q + _ = _ at h
  linarith

/-- Exact real-power expansion of the complete radial Fourier source. -/
theorem rpow_mul_thetaCuspWignerRadialTransform_re {u : ℝ} (hu : 0 < u) (τ : ℝ) :
    u ^ (-(1 / 2 : ℝ)) * (thetaCuspWignerRadialTransform (2 * u) (2 * τ)).re =
      16 * (u ^ (7 / 2 : ℝ) * besselRadialValue τ u) +
      36 * (u ^ (3 / 2 : ℝ) * besselRadialValue τ u) +
      24 * (u ^ (5 / 2 : ℝ) * besselRadialValueDeriv τ u) := by
  rw [thetaCuspWignerRadialTransform_eq_bessel (by linarith : 0 < 2 * u)]
  have hpow (n : ℕ) : u ^ (-(1 / 2 : ℝ)) * u ^ n = u ^ ((n : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hu]
    congr 1
    ring
  have h2 := hpow 2
  have h3 := hpow 3
  have h4 := hpow 4
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num,
    show (3 : ℝ) - 1 / 2 = 5 / 2 by norm_num,
    show (4 : ℝ) - 1 / 2 = 7 / 2 by norm_num] at h2 h3 h4
  simp only [besselRadialValue, besselRadialValueDeriv,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero]
  linear_combination
    16 * (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re * h4 +
    36 * (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re * h2 +
    48 * (besselArgDeriv (((2 * τ : ℝ) : ℂ) * I) (2 * u)).re * h3

/-- The literal radial Fourier tail has the signed Bessel density with its endpoint intact. -/
theorem integral_rpow_mul_thetaCuspWignerRadialTransform_re {q : ℝ}
    (hq : 1 < q) (τ : ℝ) :
    (∫ u in Ioi q, u ^ (-(1 / 2 : ℝ)) *
      (thetaCuspWignerRadialTransform (2 * u) (2 * τ)).re) =
      4 * besselFirstAtomTailDensity τ q := by
  have h7 := integrableOn_besselPowerIntegrand hq.le (7 / 2) τ
  have h3 := integrableOn_besselPowerIntegrand hq.le (3 / 2) τ
  have hd := integrableOn_rpow_mul_besselRadialValueDeriv hq.le
    (show (-1 : ℝ) < 5 / 2 by norm_num) τ
  have he : (∫ u in Ioi q, u ^ (-(1 / 2 : ℝ)) *
      (thetaCuspWignerRadialTransform (2 * u) (2 * τ)).re) =
      ∫ u in Ioi q, 16 * (u ^ (7 / 2 : ℝ) * besselRadialValue τ u) +
        36 * (u ^ (3 / 2 : ℝ) * besselRadialValue τ u) +
        24 * (u ^ (5 / 2 : ℝ) * besselRadialValueDeriv τ u) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact rpow_mul_thetaCuspWignerRadialTransform_re (zero_lt_one.trans (hq.trans hu)) τ
  have hsum : IntegrableOn (fun u : ℝ => 16 * (u ^ (7 / 2 : ℝ) * besselRadialValue τ u) +
      36 * (u ^ (3 / 2 : ℝ) * besselRadialValue τ u)) (Ioi q) :=
    (h7.const_mul 16).add (h3.const_mul 36)
  rw [he, integral_add hsum (hd.const_mul 24),
    integral_add (h7.const_mul 16) (h3.const_mul 36)]
  simp only [integral_const_mul]
  rw [integral_rpow_mul_besselRadialValueDeriv hq (by norm_num : (0 : ℝ) < 5 / 2)]
  norm_num only [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num]
  change 16 * besselPowerTail (7 / 2) τ q + 36 * besselPowerTail (3 / 2) τ q + _ = _
  unfold besselFirstAtomTailDensity
  ring

/-- Every real frequency has a strictly positive integrated radial Fourier source. -/
theorem integral_rpow_mul_thetaCuspWignerRadialTransform_re_pos {q : ℝ}
    (hq : 1 + Real.sqrt 2 < q) (b : ℝ) :
    0 < ∫ u in Ioi q, u ^ (-(1 / 2 : ℝ)) *
      (thetaCuspWignerRadialTransform (2 * u) b).re := by
  have hq1 : 1 < q := lt_of_le_of_lt (le_add_of_nonneg_right (Real.sqrt_nonneg 2)) hq
  have he : b = 2 * (b / 2) := by ring
  rw [he, integral_rpow_mul_thetaCuspWignerRadialTransform_re hq1]
  exact mul_pos (by norm_num) (besselFirstAtomTailDensity_pos hq _)

end
end GaloisForLFunctions.CompletedArithmeticForms
