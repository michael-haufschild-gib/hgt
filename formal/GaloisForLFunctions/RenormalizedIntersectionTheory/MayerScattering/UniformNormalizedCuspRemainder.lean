import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCuspKreinResidue
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence
import GaloisForLFunctions.HTGeometry.HurwitzZetaStripExpBound
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# Uniform normalized cusp remainders

Real-order comparison removes spectral height from the Eisenstein tail bound.
The exact Cauchy kernel tail reaches the boundary power, and charge normalization
cancels the Gamma factors into a completed zeta value in the Euler region.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerQuadraticCone MayerCauchyMellinSymbol
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem cosh_norm_le_real (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, norm_div, Complex.norm_two, Real.cosh_eq]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (norm_add_le _ _).trans_eq (by rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re])

private theorem bessel_norm_le_real_order {a : ℝ} (ha : 0 < a) (u : ℂ) :
    ‖modifiedBesselKOrder a u‖ ≤ ‖modifiedBesselKOrder a (u.re : ℂ)‖ := by
  have hp (t : ℝ) : ‖besselOrderKernel a u t‖ ≤ realBesselOrderKernel a u.re t := by
    have he : ‖Complex.exp (-(a : ℂ) * Complex.cosh (t : ℂ))‖ =
        Real.exp (-a * Real.cosh t) := by
      rw [Complex.norm_exp, ← Complex.ofReal_cosh]
      congr 1
      simp
    have hc : ‖Complex.cosh (u * (t : ℂ))‖ ≤ Real.cosh (u.re * t) := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        using cosh_norm_le_real (u * (t : ℂ))
    rw [besselOrderKernel, norm_mul, he, realBesselOrderKernel]
    exact mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel a u t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), realBesselOrderKernel a u.re t :=
      setIntegral_mono_on (integrableOn_besselOrderKernel ha u).norm
        (integrableOn_realBesselOrderKernel ha u.re) measurableSet_Ioi (fun t ht => hp t)
    _ = _ := by
      rw [modifiedBesselKOrder_ofReal ha, Complex.norm_real,
        Real.norm_of_nonneg (realModifiedBesselKOrder_pos ha u.re).le]
      rfl

private theorem eisenstein_term_uniform_majorant {u : ℂ} (hu : |u.re| ≤ 1 / 2)
    (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 0 < Y) (N : ℕ) :
    ‖_root_.RHTower.eisensteinTailTerm negative x Y N u‖ ≤
      _root_.RHTower.eisensteinTailMajorant Y 0 N := by
  let q : ℝ := 2 * Real.pi * ((N : ℝ) + 1) * Y
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqY : 2 * Real.pi * Y ≤ q := by
    dsimp only [q]
    have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) N]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hN (show (0 : ℝ) ≤ 2 * Real.pi by positivity)) hY.le
    simpa only [mul_one] using h
  have hcoef : ‖_root_.RHTower.d4BMCompletedEisensteinWhittakerCoefficient u
      ⟨N + 1, by omega⟩‖ ≤ ((N : ℝ) + 1) ^ (4 : ℕ) := by
    apply (_root_.RHTower.d4BM_norm_completedEisensteinWhittakerCoefficient_le u
      ⟨N + 1, by omega⟩).trans
    have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hpow := Real.rpow_le_rpow_of_exponent_le hbase
      (show 3 * |u.re| + 1 ≤ (4 : ℝ) by linarith only [hu])
    have hfour : (((N + 1 : ℕ) : ℝ) ^ (4 : ℝ)) = ((N + 1 : ℕ) : ℝ) ^ (4 : ℕ) :=
      Real.rpow_natCast _ _
    rw [hfour] at hpow
    simpa only [Nat.cast_add, Nat.cast_one] using hpow
  have hure : ‖(u.re : ℂ)‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hn := abs_nonneg u.re
    nlinarith only [hu, hn]
  have hK : ‖modifiedBesselKOrder q u‖ ≤
      Real.exp (-q) * Real.exp (1 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y) := by
    apply (bessel_norm_le_real_order hq u).trans
    apply (_root_.RHTower.d4BM_norm_modifiedBesselKOrder_le ⟨q, hq⟩ (u.re : ℂ)).trans
    have h1 : Real.exp (‖(u.re : ℂ)‖ ^ 2 / (2 * q)) ≤
        Real.exp (1 / (4 * Real.pi * Y)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 1 / (2 * q) := div_le_div_of_nonneg_right hure (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left zero_le_one (by positivity)
          (by linarith only [hqY])
    have h2 : Real.sqrt (2 * Real.pi / q) ≤ Real.sqrt (1 / Y) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ hq hY]
      simpa only [one_mul] using hqY
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le) h2
      (Real.sqrt_nonneg _) (by positivity)
  have he : _root_.RHTower.eisensteinTailTerm negative x Y N u =
      (_root_.RHTower.d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
        _root_.RHTower.d4BMCompletedEisensteinFourierPhase negative N x) * (Real.sqrt Y : ℂ) *
        modifiedBesselKOrder q u := by
    simp only [_root_.RHTower.eisensteinTailTerm, pow_zero, mul_one, q]
  rw [he, norm_mul, norm_mul, norm_mul,
    _root_.RHTower.d4BM_norm_completedEisensteinFourierPhase, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _ ≤ (((N : ℝ) + 1) ^ (4 : ℕ)) * Real.sqrt Y *
        (Real.exp (-q) * Real.exp (1 / (4 * Real.pi * Y)) * Real.sqrt (1 / Y)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)) hK
        (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [_root_.RHTower.eisensteinTailMajorant, norm_zero, zero_add, one_pow]
      rw [show (⌈3 * (1 : ℝ) + 1⌉₊) = 4 by norm_num]
      dsimp only [q]
      have he : -(2 * Real.pi * ((N : ℝ) + 1) * Y) =
          -(2 * Real.pi * Y) * ((N : ℝ) + 1) := by ring
      rw [he]
      ring

private theorem signed_tail_uniform_bound {u : ℂ} (hu : |u.re| ≤ 1 / 2)
    (negative : Bool) (x : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ‖_root_.RHTower.d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y‖ ≤
      Real.exp (1 / (2 * Real.pi)) * Real.exp (-(2 * Real.pi * Y)) *
        _root_.RHTower.tailSeriesSum 0 := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hs := _root_.RHTower.summable_eisensteinTailTerm negative x hY0 u
  rw [_root_.RHTower.signedSqrtWhittakerTail_eq_tsum_term]
  calc
    _ ≤ ∑' N : ℕ, ‖_root_.RHTower.eisensteinTailTerm negative x Y N u‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' N : ℕ, (Real.exp (1 / (2 * Real.pi)) * Real.exp (-(2 * Real.pi * Y))) *
        _root_.RHTower.tailSeriesTerm 0 N := by
      apply Summable.tsum_le_tsum _ hs.norm ((_root_.RHTower.summable_tailSeriesTerm 0).mul_left _)
      intro N
      apply (eisenstein_term_uniform_majorant hu negative x hY0 N).trans
      simpa only [norm_zero, zero_add, one_pow] using
        _root_.RHTower.eisensteinTailMajorant_le_exp hY 0 N
    _ = _ := by rw [tsum_mul_left]; rfl

/-- The actual completed Eisenstein cusp tail has one exponential majorant
throughout the vertical order strip `|Re u|≤1/2`. -/
theorem mayerCuspTail_uniform_bound {u : ℂ} (hu : |u.re| ≤ 1 / 2)
    (x : ℝ) {Y : ℝ} (hY : 1 / 2 ≤ Y) :
    ‖_root_.RHTower.d4BMCompletedEisensteinCuspTailPart .scalar u x Y‖ ≤
      _root_.RHTower.tailConst 0 * Real.exp (-(2 * Real.pi * Y)) := by
  rw [_root_.RHTower.cuspTailPart_scalar_eq, norm_mul]
  rw [Complex.norm_two]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  have h1 := signed_tail_uniform_bound hu false x hY
  have h2 := signed_tail_uniform_bound hu true x hY
  apply (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  simp only [_root_.RHTower.tailConst, norm_zero, zero_add, one_pow]
  ring

#print axioms mayerCuspTail_uniform_bound

private theorem positive_convolution_comm (f g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    _root_.RHTower.positiveMellinConvolution f g a =
      _root_.RHTower.positiveMellinConvolution g f a := by
  let H : ℝ → ℂ := fun t => g t * f (a / t)
  have hinv : mellin (fun t => H (a * t⁻¹)) 0 = mellin H 0 := by
    rw [mellin_comp_inv (fun t => H (a * t)) (0 : ℂ), neg_zero,
      mellin_comp_mul_left H 0 ha, neg_zero, Complex.cpow_zero, one_smul]
  calc
    _ = mellin (fun t => H (a * t⁻¹)) 0 := by
      rw [_root_.RHTower.positiveMellinConvolution, mellin]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have hdiv : a / (a * t⁻¹) = t := by field_simp [ha.ne', ht0.ne']
      dsimp only [H]
      rw [hdiv]
      simp only [zero_sub, Complex.cpow_neg_one, smul_eq_mul, div_eq_mul_inv]
      ring
    _ = mellin H 0 := hinv
    _ = _ := by
      rw [mellin, _root_.RHTower.positiveMellinConvolution]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [H]
      simp only [zero_sub, Complex.cpow_neg_one, smul_eq_mul, div_eq_mul_inv]
      ring

private theorem field_charge_product {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im) :
    Gammaℝ w * averagingFactor w * (2 * riemannZeta (w - 1) / (w - 1)) * w =
      _root_.RHTower.reflectedCompletedLambda (w - 1) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl _ hw
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
    exact him.ne' hi
  have hh : (w - 1) / 2 ≠ 0 := div_ne_zero hw1 (by norm_num)
  have hrec : Gamma ((w + 1) / 2) = ((w - 1) / 2) * Gamma ((w - 1) / 2) := by
    rw [show (w + 1) / 2 = (w - 1) / 2 + 1 by ring, Gamma_add_one _ hh]
  have hp : (Real.pi : ℂ) ^ ((1 - w) / 2) = (Real.pi : ℂ) ^ (-(w - 1) / 2) := by
    congr 1
    ring
  rw [gammaR_mul_averagingFactor hw, hrec, hp,
    _root_.RHTower.reflectedCompletedLambda, Gammaℝ_def]
  field_simp [hw0, hw1]

/-- The completed functional equation moves the normalization into the Euler region. -/
private theorem field_charge_product_reflected (s : upperMayerResonances) :
    Gammaℝ (2 * s.1) * averagingFactor (2 * s.1) * mayerCuspCharge s * (2 * s.1) =
      Gammaℝ (2 - 2 * s.1) * riemannZeta (2 - 2 * s.1) := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hi1 : (2 * s.1 - 1).im ≠ 0 := by simpa using him.ne'
  have hi2 : (2 - 2 * s.1).im ≠ 0 := by simpa using (neg_ne_zero.mpr him.ne')
  have hn1 : 2 * s.1 - 1 ≠ 0 := by intro h; apply hi1; rw [h, Complex.zero_im]
  have hn2 : 2 - 2 * s.1 ≠ 0 := by intro h; apply hi2; rw [h, Complex.zero_im]
  rw [mayerCuspCharge, field_charge_product hw him]
  change _root_.RHTower.reflectedCompletedLambda (2 * s.1 - 1) =
    _root_.RHTower.reflectedCompletedLambda (2 - 2 * s.1)
  rw [_root_.RHTower.reflectedCompletedLambda_eq_completed hn1
      (_root_.RHTower.Gammaℝ_ne_zero_of_im_ne_zero hi1),
    _root_.RHTower.reflectedCompletedLambda_eq_completed hn2
      (_root_.RHTower.Gammaℝ_ne_zero_of_im_ne_zero hi2)]
  simpa only [show 1 - (2 * s.1 - 1) = 2 - 2 * s.1 by ring] using
    (completedRiemannZeta_one_sub (2 * s.1 - 1)).symm

private def cuspNormalizedFieldFactor (s : upperMayerResonances) : ℂ :=
  (2 * s.1) / (Gammaℝ (2 - 2 * s.1) * riemannZeta (2 - 2 * s.1))

private theorem cusp_charge_inverse_normalization (s : upperMayerResonances) :
    (Gammaℝ (2 * s.1) * averagingFactor (2 * s.1) * mayerCuspCharge s)⁻¹ =
      cuspNormalizedFieldFactor s := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hw0 : 2 * s.1 ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl _ hw
  have hG := _root_.RHTower.Gammaℝ_ne_zero_of_im_ne_zero him.ne'
  have hA := MayerEpsteinEndpointBounds.averagingFactor_ne_zero_halfPlane hw
  have hB := mayerCuspCharge_ne_zero s
  have hs0 : s.1 ≠ 0 := by
    intro h
    have hs := s.2.2.1
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  rw [cuspNormalizedFieldFactor, ← field_charge_product_reflected]
  field_simp [hG, hA, hB, hw0, hs0]

private theorem cusp_scattering_normalization (s : upperMayerResonances) :
    scatteringCoefficient (2 * s.1) / (averagingFactor (2 * s.1) * mayerCuspCharge s) =
      2 * s.1 := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hG := _root_.RHTower.Gammaℝ_ne_zero_of_im_ne_zero him.ne'
  have hA := MayerEpsteinEndpointBounds.averagingFactor_ne_zero_halfPlane hw
  have hB := mayerCuspCharge_ne_zero s
  have hp : _root_.RHTower.reflectedCompletedLambda (2 * s.1 - 1) =
      Gammaℝ (2 * s.1) * averagingFactor (2 * s.1) * mayerCuspCharge s * (2 * s.1) := by
    simpa only [mayerCuspCharge] using (field_charge_product hw him).symm
  rw [scatteringCoefficient, hp]
  field_simp [hG, hA, hB]

private def cuspFieldRemainder (s : upperMayerResonances) (a : ℝ) : ℂ :=
  (fieldCore (2 * s.1) a + scatteringCoefficient (2 * s.1) * (a : ℂ) ^ (-1 : ℂ)) /
    (averagingFactor (2 * s.1) * mayerCuspCharge s)

private theorem cusp_field_norm_factor (s : upperMayerResonances) :
    1 / (‖Gammaℝ (2 * s.1)‖ * ‖averagingFactor (2 * s.1) * mayerCuspCharge s‖) =
      ‖cuspNormalizedFieldFactor s‖ := by
  simpa only [one_div, norm_inv, norm_mul, mul_assoc] using
    congrArg norm (cusp_charge_inverse_normalization s)

private def cuspFieldSmallBound (s : upperMayerResonances) : ℝ :=
  ‖cuspNormalizedFieldFactor s‖ *
    (2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re)) + ‖2 * s.1‖

private theorem cuspFieldSmallBound_nonneg (s : upperMayerResonances) :
    0 ≤ cuspFieldSmallBound s := by
  have hs : 0 < 2 * s.1.re := by linarith only [s.2.2.1]
  have hg : 0 < 1 - 2 * s.1.re := by linarith only [s.2.2.2.1]
  unfold cuspFieldSmallBound
  positivity

private theorem cusp_field_small_bound (s : upperMayerResonances) {a : ℝ} (ha : 0 < a) :
    ‖cuspFieldRemainder s a‖ ≤ cuspFieldSmallBound s / a := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have hw1 : (2 * s.1).re < 1 := by simp; linarith only [s.2.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hz := (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  have hf := fieldCore_resonant_endpoint_bound hw hw1 him hz ha
  rw [show (2 * s.1).re = 2 * s.1.re by simp] at hf
  have he : cuspFieldRemainder s a =
      fieldCore (2 * s.1) a / (averagingFactor (2 * s.1) * mayerCuspCharge s) +
        (scatteringCoefficient (2 * s.1) / (averagingFactor (2 * s.1) * mayerCuspCharge s)) *
          (a : ℂ) ^ (-1 : ℂ) := by
    unfold cuspFieldRemainder
    ring
  have hp : ‖(2 * s.1) * (a : ℂ) ^ (-1 : ℂ)‖ = ‖2 * s.1‖ * a⁻¹ := by
    rw [norm_mul, Complex.cpow_neg_one, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [he, cusp_scattering_normalization]
  calc
    _ ≤ ‖fieldCore (2 * s.1) a / (averagingFactor (2 * s.1) * mayerCuspCharge s)‖ +
        ‖(2 * s.1) * (a : ℂ) ^ (-1 : ℂ)‖ := norm_add_le _ _
    _ ≤ ((2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re)) /
        (‖Gammaℝ (2 * s.1)‖ * a)) / ‖averagingFactor (2 * s.1) * mayerCuspCharge s‖ +
        ‖2 * s.1‖ * a⁻¹ := by
      rw [hp, norm_div]
      exact add_le_add (div_le_div_of_nonneg_right hf (norm_nonneg _)) le_rfl
    _ = _ := by
      rw [cuspFieldSmallBound, ← cusp_field_norm_factor]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem cusp_exp_inverse_square {a : ℝ} (ha : 0 < a) :
    Real.exp (-(2 * Real.pi * a)) ≤ (Real.pi ^ 2)⁻¹ * a ^ (-2 : ℝ) := by
  have hp : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hbase : Real.pi * a ≤ Real.exp (Real.pi * a) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hi : Real.exp (-(Real.pi * a)) ≤ (Real.pi * a)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hp hbase
  calc
    _ = Real.exp (-(Real.pi * a)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    _ ≤ ((Real.pi * a)⁻¹) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hi 2
    _ = _ := by rw [Real.rpow_neg ha.le, Real.rpow_two]; field_simp

private theorem cusp_field_large_bound (s : upperMayerResonances) {a : ℝ} (ha : 1 ≤ a) :
    ‖cuspFieldRemainder s a‖ ≤
      (‖cuspNormalizedFieldFactor s‖ * (_root_.RHTower.tailConst 0 / Real.pi ^ 2)) *
        a ^ (-s.1.re - 2) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hz := (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  have hu : |((2 * s.1 - 1) / 2).re| ≤ 1 / 2 := by
    have he : ((2 * s.1 - 1) / 2).re = s.1.re - 1 / 2 := by simp; ring
    rw [he]
    exact abs_le.mpr ⟨by linarith only [s.2.2.1], by linarith only [s.2.2.2.1]⟩
  have ht := mayerCuspTail_uniform_bound hu 0 (Y := a) (by linarith only [ha])
  rw [cuspFieldRemainder, fieldCore_eq_tail hw him ha0, hz, zero_mul, sub_zero, sub_add_cancel,
    normalizedTail, norm_div, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha0,
    show (-(2 * s.1) / 2).re = -s.1.re by simp; ring]
  calc
    _ ≤ (a ^ (-s.1.re) / ‖Gammaℝ (2 * s.1)‖) *
        (_root_.RHTower.tailConst 0 * Real.exp (-(2 * Real.pi * a))) /
          ‖averagingFactor (2 * s.1) * mayerCuspCharge s‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) (norm_nonneg _)
    _ = ‖cuspNormalizedFieldFactor s‖ * _root_.RHTower.tailConst 0 *
        a ^ (-s.1.re) * Real.exp (-(2 * Real.pi * a)) := by
      rw [← cusp_field_norm_factor]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ‖cuspNormalizedFieldFactor s‖ * _root_.RHTower.tailConst 0 *
        a ^ (-s.1.re) * ((Real.pi ^ 2)⁻¹ * a ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (cusp_exp_inverse_square ha0)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (_root_.RHTower.tailConst_nonneg _))
          (Real.rpow_pos_of_pos ha0 _).le)
    _ = _ := by
      rw [show -s.1.re - 2 = -s.1.re + (-2) by ring, Real.rpow_add ha0]
      ring

private theorem measurable_cuspFieldRemainder (s : upperMayerResonances) :
    Measurable (cuspFieldRemainder s) := by
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hw0 : 2 * s.1 ≠ 0 := by intro h; rw [h, Complex.zero_im] at him; exact lt_irrefl _ him
  have hw2 : 2 * s.1 ≠ 2 := by intro h; rw [h] at him; norm_num at him
  have he := MayerEpsteinHeightMeasurability.measurable_epsteinField hw0 hw2
  unfold cuspFieldRemainder fieldCore scatteringPowers
  fun_prop

private def cuspFieldDensity (s : upperMayerResonances) (a : ℝ) : ℝ :=
  a ^ (2 * s.1.re) * ‖cuspFieldRemainder s a‖

/-- The weighted field mass is finite: the small-axis power is `2 Re s−1`,
and the large-axis power is `Re s−2`. -/
private theorem cusp_field_mass_bound (s : upperMayerResonances) :
    IntegrableOn (cuspFieldDensity s) (Ioi 0) ∧
      (∫ a in Ioi (0 : ℝ), cuspFieldDensity s a) ≤
        cuspFieldSmallBound s / (2 * s.1.re) +
          2 * (‖cuspNormalizedFieldFactor s‖ * (_root_.RHTower.tailConst 0 / Real.pi ^ 2)) := by
  have hσ : 0 < 2 * s.1.re := by linarith only [s.2.2.1]
  have hr : -1 < 2 * s.1.re - 1 := by linarith only [hσ]
  have hq : s.1.re - 2 < -1 := by linarith only [s.2.2.2.1]
  have hg : 0 < 1 - s.1.re := by linarith only [s.2.2.2.1]
  let D : ℝ := ‖cuspNormalizedFieldFactor s‖ * (_root_.RHTower.tailConst 0 / Real.pi ^ 2)
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _)
    (div_nonneg (_root_.RHTower.tailConst_nonneg _) (sq_nonneg _))
  have hm : Measurable (cuspFieldDensity s) := by
    have hf := measurable_cuspFieldRemainder s
    unfold cuspFieldDensity
    fun_prop
  have hnn (a : ℝ) (ha : 0 ≤ a) : 0 ≤ cuspFieldDensity s a :=
    mul_nonneg (Real.rpow_nonneg ha _) (norm_nonneg _)
  have hsmall (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1) :
      cuspFieldDensity s a ≤ cuspFieldSmallBound s * a ^ (2 * s.1.re - 1) := by
    have ha0 : 0 < a := ha.1
    calc
      _ ≤ a ^ (2 * s.1.re) * (cuspFieldSmallBound s / a) :=
        mul_le_mul_of_nonneg_left (cusp_field_small_bound s ha0) (Real.rpow_pos_of_pos ha0 _).le
      _ = _ := by rw [Real.rpow_sub ha0, Real.rpow_one]; ring
  have hlarge (a : ℝ) (ha : a ∈ Ioi (1 : ℝ)) :
      cuspFieldDensity s a ≤ D * a ^ (s.1.re - 2) := by
    have ha0 : 0 < a := zero_lt_one.trans ha
    calc
      _ ≤ a ^ (2 * s.1.re) * (D * a ^ (-s.1.re - 2)) :=
        mul_le_mul_of_nonneg_left (cusp_field_large_bound s ha.le) (Real.rpow_pos_of_pos ha0 _).le
      _ = D * (a ^ (2 * s.1.re) * a ^ (-s.1.re - 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add ha0]
        congr 2
        ring
  have hpSmall : IntegrableOn (fun a : ℝ => a ^ (2 * s.1.re - 1)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  have hpLarge := integrableOn_Ioi_rpow_of_lt hq zero_lt_one
  have hiSmall : IntegrableOn (cuspFieldDensity s) (Ioc 0 1) := by
    apply (hpSmall.const_mul (cuspFieldSmallBound s)).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    rw [Real.norm_of_nonneg (hnn a ha.1.le)]
    exact hsmall a ha
  have hiLarge : IntegrableOn (cuspFieldDensity s) (Ioi 1) := by
    apply (hpLarge.const_mul D).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [Real.norm_of_nonneg (hnn a (zero_lt_one.trans ha).le)]
    exact hlarge a ha
  have hi : IntegrableOn (cuspFieldDensity s) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hiSmall.union hiLarge
  refine ⟨hi, ?_⟩
  have hvalSmall : (∫ a in Ioc (0 : ℝ) 1, a ^ (2 * s.1.re - 1)) = 1 / (2 * s.1.re) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr),
      show 2 * s.1.re - 1 + 1 = 2 * s.1.re by ring,
      Real.one_rpow, Real.zero_rpow hσ.ne', sub_zero]
  have hvalLarge : (∫ a in Ioi (1 : ℝ), a ^ (s.1.re - 2)) = 1 / (1 - s.1.re) := by
    rw [integral_Ioi_rpow_of_lt hq zero_lt_one, Real.one_rpow,
      show s.1.re - 2 + 1 = -(1 - s.1.re) by ring]
    simp only [div_neg, neg_div, neg_neg]
  have hbSmall : (∫ a in Ioc (0 : ℝ) 1, cuspFieldDensity s a) ≤
      cuspFieldSmallBound s / (2 * s.1.re) := by
    calc
      _ ≤ ∫ a in Ioc (0 : ℝ) 1, cuspFieldSmallBound s * a ^ (2 * s.1.re - 1) :=
        setIntegral_mono_on hiSmall (hpSmall.const_mul _) measurableSet_Ioc hsmall
      _ = _ := by rw [integral_const_mul, hvalSmall]; ring
  have hbLarge : (∫ a in Ioi (1 : ℝ), cuspFieldDensity s a) ≤ 2 * D := by
    have hrp : 1 / (1 - s.1.re) ≤ 2 := (div_le_iff₀ hg).mpr (by linarith only [s.2.2.2.1])
    calc
      _ ≤ ∫ a in Ioi (1 : ℝ), D * a ^ (s.1.re - 2) :=
        setIntegral_mono_on hiLarge (hpLarge.const_mul _) measurableSet_Ioi hlarge
      _ = D * (1 / (1 - s.1.re)) := by rw [integral_const_mul, hvalLarge]
      _ ≤ D * 2 := mul_le_mul_of_nonneg_left hrp hD
      _ = _ := mul_comm _ _
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hiSmall hiLarge
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  rw [hsplit]
  exact add_le_add hbSmall hbLarge

private def cuspFieldMass (s : upperMayerResonances) : ℝ :=
  ∫ a in Ioi (0 : ℝ), cuspFieldDensity s a

/-- Commuting the multiplicative convolution exposes the full boundary exponent. -/
private theorem cusp_normalized_outgoing_bound (s : upperMayerResonances)
    {a : ℝ} (ha : 0 < a) :
    ‖(mayerPeriodCore s.1 a + mayerCuspCharge s * (a : ℂ) ^ (-1 : ℂ)) /
      mayerCuspCharge s‖ ≤ cuspFieldMass s * a ^ (-1 - 2 * s.1.re) := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  let raw : ℝ → ℂ := fun u => fieldCore (2 * s.1) u +
    scatteringCoefficient (2 * s.1) * (u : ℂ) ^ (-1 : ℂ)
  have hc := cauchyKernel_core_integrable hw him ha
  have hp := power_integrable hw (u := 1) (by norm_num)
    (by simp; linarith only [s.2.2.1]) ha
  have he : _root_.RHTower.positiveMellinConvolution (cauchyKernel (2 * s.1)) raw a =
      mayerPeriodCore s.1 a + mayerCuspCharge s * (a : ℂ) ^ (-1 : ℂ) := by
    unfold _root_.RHTower.positiveMellinConvolution
    have hf (t : ℝ) : cauchyKernel (2 * s.1) t * raw (a / t) / (t : ℂ) =
        cauchyKernel (2 * s.1) t * fieldCore (2 * s.1) (a / t) / (t : ℂ) +
          scatteringCoefficient (2 * s.1) *
            (cauchyKernel (2 * s.1) t * ((a / t : ℝ) : ℂ) ^ (-1 : ℂ) / (t : ℂ)) := by
      dsimp only [raw]
      ring
    simp_rw [hf]
    rw [integral_add hc (hp.const_mul _), integral_const_mul]
    change mayerPeriodCore s.1 a + scatteringCoefficient (2 * s.1) *
      _root_.RHTower.positiveMellinConvolution (cauchyKernel (2 * s.1))
        (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) a = _
    rw [power_convolution hw (u := 1) (by norm_num) (by simp; linarith only [s.2.2.1]) ha,
      mul_left_comm (scatteringCoefficient (2 * s.1)), scatteringCoefficient_mul_symbol_one hw him]
    dsimp only [mayerCuspCharge]
    ring
  let J : ℝ → ℂ := fun u => cuspFieldRemainder s u * ((a / u : ℝ) : ℂ) *
    cauchyWeight (2 * s.1) (a / u) / (u : ℂ)
  have hrep : (mayerPeriodCore s.1 a + mayerCuspCharge s * (a : ℂ) ^ (-1 : ℂ)) /
      mayerCuspCharge s = ∫ u in Ioi (0 : ℝ), J u := by
    rw [← he, positive_convolution_comm _ _ ha, _root_.RHTower.positiveMellinConvolution]
    change (∫ u in Ioi (0 : ℝ), raw u * cauchyKernel (2 * s.1) (a / u) / (u : ℂ)) *
      (mayerCuspCharge s)⁻¹ = _
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only [J, raw, cuspFieldRemainder, cauchyKernel]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hb (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      ‖J u‖ ≤ a ^ (-1 - 2 * s.1.re) * cuspFieldDensity s u := by
    have hu0 : 0 < u := hu
    have hq : 0 < a / u := div_pos ha hu0
    have hwgt := MayerEpsteinEndpointBounds.norm_cauchyWeight_le_power hw.le hq
    rw [show (2 * s.1).re = 2 * s.1.re by simp] at hwgt
    have hpw : (a / u) * (a / u) ^ (-(2 * s.1.re) - 2) =
        (a / u) ^ (-1 - 2 * s.1.re) := by
      rw [show -1 - 2 * s.1.re = 1 + (-(2 * s.1.re) - 2) by ring,
        Real.rpow_add hq, Real.rpow_one]
    have hratio : (a / u) ^ (-1 - 2 * s.1.re) / u =
        a ^ (-1 - 2 * s.1.re) * u ^ (2 * s.1.re) := by
      rw [Real.div_rpow ha.le hu0.le,
        show -1 - 2 * s.1.re = -(1 + 2 * s.1.re) by ring,
        Real.rpow_neg hu0.le, div_inv_eq_mul]
      rw [show 1 + 2 * s.1.re = 2 * s.1.re + 1 by ring, Real.rpow_add hu0, Real.rpow_one]
      field_simp
    dsimp only [J]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    calc
      _ ≤ (‖cuspFieldRemainder s u‖ * (a / u) *
          (a / u) ^ (-(2 * s.1.re) - 2)) / u :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hwgt (mul_nonneg (norm_nonneg _) hq.le)) hu0.le
      _ = ‖cuspFieldRemainder s u‖ * ((a / u) ^ (-1 - 2 * s.1.re) / u) := by
        rw [← hpw]
        ring
      _ = _ := by rw [hratio]; dsimp only [cuspFieldDensity]; ring
  have hm : Measurable J := by
    have hf := measurable_cuspFieldRemainder s
    dsimp only [J, cauchyWeight]
    fun_prop
  have hM := (cusp_field_mass_bound s).1
  have hi : IntegrableOn J (Ioi 0) := by
    apply (hM.const_mul (a ^ (-1 - 2 * s.1.re))).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hb u hu
  rw [hrep]
  calc
    _ ≤ ∫ u in Ioi (0 : ℝ), ‖J u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), a ^ (-1 - 2 * s.1.re) * cuspFieldDensity s u :=
      setIntegral_mono_on hi.norm (hM.const_mul _) measurableSet_Ioi hb
    _ = _ := by rw [integral_const_mul]; exact mul_comm _ _

private theorem cusp_normalized_lower_bound (s : upperMayerResonances)
    {a : ℝ} (ha : 0 < a) :
    ‖mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1)‖ ≤ cuspFieldMass s * a := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hcore := lewisModularInversion_mayerPeriodCore s.2.2.1 s.2.1 ha
  rw [lewisModularInversion] at hcore
  have hp : (a : ℂ) ^ (-(2 * s.1)) * (((1 / a : ℝ) : ℂ) ^ (-1 : ℂ)) =
      (a : ℂ) ^ (1 - 2 * s.1) := by
    rw [Complex.cpow_neg_one, Complex.ofReal_div, Complex.ofReal_one, one_div, inv_inv]
    calc
      _ = (a : ℂ) ^ (-(2 * s.1)) * (a : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (a : ℂ) ^ (-(2 * s.1) + 1) := (Complex.cpow_add _ _ haC).symm
      _ = _ := by congr 1; ring
  have he : mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1) =
      -(a : ℂ) ^ (-(2 * s.1)) *
        ((mayerPeriodCore s.1 (1 / a) + mayerCuspCharge s *
          (((1 / a : ℝ) : ℂ) ^ (-1 : ℂ))) / mayerCuspCharge s) := by
    rw [mayerCuspNormalizedCore, ← hp]
    rw [one_div]
    field_simp [mayerCuspCharge_ne_zero s]
    simp only [one_div]
    linear_combination hcore
  have hr : (1 / a) ^ (-1 - 2 * s.1.re) = a ^ (1 + 2 * s.1.re) := by
    rw [one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.neg_re, show (2 * s.1).re = 2 * s.1.re by simp]
  calc
    _ ≤ a ^ (-(2 * s.1.re)) * (cuspFieldMass s * (1 / a) ^ (-1 - 2 * s.1.re)) :=
      mul_le_mul_of_nonneg_left (cusp_normalized_outgoing_bound s (one_div_pos.mpr ha))
        (Real.rpow_pos_of_pos ha _).le
    _ = cuspFieldMass s * (a ^ (-(2 * s.1.re)) * a ^ (1 + 2 * s.1.re)) := by rw [hr]; ring
    _ = _ := by
      rw [← Real.rpow_add ha, show -(2 * s.1.re) + (1 + 2 * s.1.re) = 1 by ring, Real.rpow_one]

private theorem cusp_right_gap_bound (s : upperMayerResonances) :
    1 / (1 - 2 * s.1.re) ≤ 116 * s.1.im := by
  have h := (upperMayerResonance_reciprocal_bound (reflectUpperResonance s)).2
  rw [reflectUpperResonance_coe, riemannMayerReflect_re, riemannMayerReflect_im,
    show 2 * (1 / 2 - s.1.re) = 1 - 2 * s.1.re by ring] at h
  exact h

private theorem cusp_parameter_norm_bound (s : upperMayerResonances) :
    ‖2 * s.1‖ ≤ 2 * (1 + s.1.im) := by
  have hs : ‖s.1‖ ≤ s.1.re + s.1.im := by
    calc
      _ = ‖(s.1.re : ℂ) + (s.1.im : ℂ) * I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(s.1.re : ℂ)‖ + ‖(s.1.im : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_of_nonneg s.2.2.1.le, Real.norm_of_nonneg s.2.1.le]
  rw [norm_mul, Complex.norm_ofNat]
  linarith only [hs, s.2.2.2.1]

/-- Gamma decay and both reciprocal strip gaps give a uniform spectral majorant. -/
private theorem cusp_field_factor_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances,
      ‖cuspNormalizedFieldFactor s‖ ≤
        C * (1 + s.1.im) ^ 2 * Real.exp (Real.pi * s.1.im) := by
  obtain ⟨C, hC, hG⟩ := HTGeometry.exists_bound_norm_div_Gammaℝ
    (f := fun _ => 1) (σ₀ := 1) (σ₁ := 2) (B := 1)
    (by norm_num) (by norm_num) (by intros; simp)
  refine ⟨234 * C, by positivity, fun s => ?_⟩
  have hs0 := s.2.2.1
  have hs1 := s.2.2.2.1
  have hy := (upperMayerResonance_reciprocal_bound s).1
  have hre : (2 - 2 * s.1).re = 2 - 2 * s.1.re := by simp
  have him : |(2 - 2 * s.1).im| = 2 * s.1.im := by
    rw [show (2 - 2 * s.1).im = -(2 * s.1.im) by simp, abs_neg,
      abs_of_pos (show 0 < 2 * s.1.im by linarith only [s.2.1])]
  have hg := hG (2 - 2 * s.1) (by rw [hre]; linarith only [hs1])
    (by rw [hre]; linarith only [hs0]) (by rw [him]; linarith only [hy])
  rw [one_div, him, show Real.pi * (2 * s.1.im) / 2 = Real.pi * s.1.im by ring] at hg
  have hz := _root_.RHTower.norm_inv_riemannZeta_le_of_le_re
    (show 1 < 2 - 2 * s.1.re by linarith only [hs1]) (s := 2 - 2 * s.1) (by rw [hre])
  rw [show 2 - 2 * s.1.re - 1 = 1 - 2 * s.1.re by ring] at hz
  have hz' : ‖(riemannZeta (2 - 2 * s.1))⁻¹‖ ≤ 117 * (1 + s.1.im) :=
    hz.trans (by linarith only [cusp_right_gap_bound s, s.2.1])
  rw [cuspNormalizedFieldFactor, div_eq_mul_inv, mul_inv_rev, norm_mul,
    norm_mul (riemannZeta (2 - 2 * s.1))⁻¹ (Gammaℝ (2 - 2 * s.1))⁻¹]
  calc
    _ ≤ (2 * (1 + s.1.im)) *
        ((117 * (1 + s.1.im)) * (C * Real.exp (Real.pi * s.1.im))) :=
      mul_le_mul (cusp_parameter_norm_bound s)
        (mul_le_mul hz' hg (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

private theorem cusp_field_mass_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances,
      cuspFieldMass s ≤ C * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im) := by
  obtain ⟨L, hL, hF⟩ := cusp_field_factor_growth
  let D : ℝ := _root_.RHTower.tailConst 0 / Real.pi ^ 2
  have hD : 0 ≤ D := div_nonneg (_root_.RHTower.tailConst_nonneg _) (sq_nonneg _)
  refine ⟨L * (26912 + 2 * D) + 232, by positivity, fun s => ?_⟩
  let R : ℝ := 1 + s.1.im
  let E : ℝ := Real.exp (Real.pi * s.1.im)
  have hR : 1 ≤ R := by dsimp only [R]; linarith only [s.2.1]
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg Real.pi_pos.le s.2.1.le)
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hσ : 0 < 2 * s.1.re := by linarith only [s.2.2.1]
  have hg : 0 < 1 - 2 * s.1.re := by linarith only [s.2.2.2.1]
  have hl : 1 / (2 * s.1.re) ≤ 116 * R :=
    (upperMayerResonance_reciprocal_bound s).2.trans (by dsimp only [R]; linarith)
  have hr : 1 / (1 - 2 * s.1.re) ≤ 116 * R :=
    (cusp_right_gap_bound s).trans (by dsimp only [R]; linarith)
  have hπ : 2 / (Real.pi * (2 * s.1.re)) ≤ 1 / (2 * s.1.re) := by
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos hσ) hσ).mpr
    nlinarith only [Real.pi_gt_three, hσ]
  have hK : cuspFieldSmallBound s ≤
      (232 * ‖cuspNormalizedFieldFactor s‖ + 2) * R := by
    unfold cuspFieldSmallBound
    calc
      _ ≤ ‖cuspNormalizedFieldFactor s‖ * (116 * R + 116 * R) + 2 * R :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add (hπ.trans hl) hr) (norm_nonneg _))
          (cusp_parameter_norm_bound s)
      _ = _ := by ring
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR24 : R ^ 2 ≤ R ^ 4 := by
    calc
      _ = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hR2 (sq_nonneg _)
      _ = _ := by ring
  have hmass : cuspFieldMass s ≤
      ‖cuspNormalizedFieldFactor s‖ * (26912 * R ^ 2 + 2 * D) + 232 * R ^ 2 := by
    calc
      _ ≤ cuspFieldSmallBound s / (2 * s.1.re) +
          2 * (‖cuspNormalizedFieldFactor s‖ * D) := (cusp_field_mass_bound s).2
      _ ≤ ((232 * ‖cuspNormalizedFieldFactor s‖ + 2) * R) * (116 * R) +
          2 * (‖cuspNormalizedFieldFactor s‖ * D) := by
        apply add_le_add _ le_rfl
        rw [div_eq_mul_inv, ← one_div]
        exact mul_le_mul hK hl (by positivity) (by positivity)
      _ = _ := by ring
  have hbr : 26912 * R ^ 2 + 2 * D ≤ (26912 + 2 * D) * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ 2 * D by positivity)
    nlinarith only [h]
  have hrest : 232 * R ^ 2 ≤ 232 * R ^ 4 * E := by
    calc
      _ ≤ 232 * R ^ 4 := mul_le_mul_of_nonneg_left hR24 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hE
  calc
    _ ≤ ‖cuspNormalizedFieldFactor s‖ * (26912 * R ^ 2 + 2 * D) + 232 * R ^ 2 := hmass
    _ ≤ (L * R ^ 2 * E) * ((26912 + 2 * D) * R ^ 2) + 232 * R ^ 4 * E :=
      add_le_add (mul_le_mul (hF s) hbr (by positivity) (by positivity)) hrest
    _ = _ := by dsimp only [R, E]; ring

/-- Charge-normalized actual cores have an exact linear cusp remainder,
with a uniform polynomial-exponential spectral bound. -/
theorem mayerCuspNormalizedCore_uniform_remainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ a > 0,
      ‖mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1)‖ ≤
        (C * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im)) * a := by
  obtain ⟨C, hC, hbound⟩ := cusp_field_mass_growth
  exact ⟨C, hC, fun s a ha => (cusp_normalized_lower_bound s ha).trans
    (mul_le_mul_of_nonneg_right (hbound s) ha.le)⟩

#print axioms mayerCuspNormalizedCore_uniform_remainder_bound

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
