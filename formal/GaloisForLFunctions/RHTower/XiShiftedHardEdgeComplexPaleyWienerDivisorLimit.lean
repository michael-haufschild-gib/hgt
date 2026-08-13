import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexPaleyWienerAliasExchange
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexCayleyGeometry
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearRayIntegral
import GaloisForLFunctions.RHTower.PrimeArchCenteredAnalyticTailVacuumCone
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Central Xi-divisor limit for complex hard-edge Paley--Wiener packets

Alias exchange and central Cayley convergence require different domination mechanisms.  The former
is handled by reciprocal-square summability.  For the central packet, the normalized resolvent is
uniformly bounded while complex Cayley geometry retains `min(height, mass)` in the Fourier phase.
This module develops that second mechanism.
-/

open scoped BigOperators SchwartzMap FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open MeasureTheory
open Filter

/-- Integral form of the complex positive Fourier extension.  This exposes its dependence on the
complex frequency without routing through a frequency-dependent Schwartz tilt. -/
theorem routeUComplexPositiveFourierExtension_eq_integral
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (z : ℂ) :
    routeUComplexPositiveFourierExtension n f z =
      ∫ t : ℝ,
        Complex.exp (Complex.I * z * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t := by
  rw [routeUComplexPositiveFourierExtension, routeUPositiveFourierExtension,
    SchwartzMap.fourier_coe, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with t
  rw [routeUComplexTilt_apply, routeU_complex_exp_decomposition]
  simp only [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul]
  rw [← mul_assoc]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Sequential continuity of the complex Fourier extension on the closed unit strip, proved by
dominated convergence against the compact amplitude rather than by a formal power series. -/
theorem tendsto_routeUComplexPositiveFourierExtension_of_tendsto
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (z : ℕ → ℂ) (z₀ : ℂ)
    (hz : Tendsto z atTop (nhds z₀)) (hstrip : ∀ k, |(z k).im| ≤ 1) :
    Tendsto (fun k => routeUComplexPositiveFourierExtension n f (z k))
      atTop (nhds (routeUComplexPositiveFourierExtension n f z₀)) := by
  have hmeas : ∀ k, AEStronglyMeasurable (fun t : ℝ =>
      Complex.exp (Complex.I * z k * (t : ℂ)) *
        SchwartzMap.compactSupportApproximation n f t) := by
    intro k
    exact (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (Complex.I * z k * (t : ℂ)) *
        SchwartzMap.compactSupportApproximation n f t).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ t : ℝ ∂volume,
      ‖Complex.exp (Complex.I * z k * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t‖ ≤
        routeUComplexTiltDerivMajorant n f 0 t := by
    intro k
    filter_upwards with t
    have hexp : ‖Complex.exp (Complex.I * z k * (t : ℂ))‖ ≤ Real.exp |t| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (Complex.I * z k * (t : ℂ)).re = -((z k).im * t) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre]
      calc
        -((z k).im * t) ≤ |(z k).im * t| := neg_le_abs _
        _ = |(z k).im| * |t| := abs_mul _ _
        _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right (hstrip k) (abs_nonneg t)
        _ = |t| := one_mul _
    rw [norm_mul]
    calc
      ‖Complex.exp (Complex.I * z k * (t : ℂ))‖ *
          ‖SchwartzMap.compactSupportApproximation n f t‖ ≤
        Real.exp |t| * ‖SchwartzMap.compactSupportApproximation n f t‖ := by gcongr
      _ = routeUComplexTiltDerivMajorant n f 0 t := by
        simp [routeUComplexTiltDerivMajorant]
  have hlim : ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun k =>
        Complex.exp (Complex.I * z k * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t) atTop
        (nhds (Complex.exp (Complex.I * z₀ * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t)) := by
    filter_upwards with t
    have hcont : Continuous (fun w : ℂ =>
        Complex.exp (Complex.I * w * (t : ℂ)) *
          SchwartzMap.compactSupportApproximation n f t) := by
      fun_prop
    exact hcont.continuousAt.tendsto.comp hz
  have hdct := tendsto_integral_of_dominated_convergence
    (routeUComplexTiltDerivMajorant n f 0) hmeas
    (integrable_routeUComplexTiltDerivMajorant n f 0) hbound hlim
  simpa only [routeUComplexPositiveFourierExtension_eq_integral] using hdct

/-- Exact complement identity for the mass-normalized shifted resolvent. -/
theorem routeUXiHardEdgeResolventWeight_eq_one_sub
    (r : ℝ) (q : XiZeroCopy) :
    routeUXiHardEdgeResolventWeight r q =
      1 - xiSquaredNode q *
        xiShiftedReciprocalSquare (routeUHardEdgeMass r ^ 2) q := by
  rw [routeUXiHardEdgeResolventWeight,
    xiShiftedReciprocalSquare_eq_inv (sq_nonneg (routeUHardEdgeMass r))]
  have hden : (((routeUHardEdgeMass r ^ 2 : ℝ) : ℂ) + xiSquaredNode q) ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero (sq_nonneg (routeUHardEdgeMass r)) q
  field_simp [hden]
  ring

/-- The mass-normalized shifted Xi resolvent tends to one along the natural hard-edge ray. -/
theorem tendsto_routeUXiHardEdgeResolventWeight_natCast_one (q : XiZeroCopy) :
    Tendsto (fun k : ℕ => routeUXiHardEdgeResolventWeight (k : ℝ) q)
      atTop (nhds 1) := by
  have hmass : Tendsto (fun k : ℕ => routeUHardEdgeMass (k : ℝ)) atTop atTop := by
    simpa [routeUHardEdgeMass, abs_of_nonneg, add_comm] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hmassSq : Tendsto (fun k : ℕ => routeUHardEdgeMass (k : ℝ) ^ 2)
      atTop atTop := by
    exact (tendsto_pow_atTop (n := 2) (by norm_num)).comp hmass
  have hshift : Tendsto
      (fun k : ℕ => xiShiftedReciprocalSquare
        (routeUHardEdgeMass (k : ℝ) ^ 2) q) atTop (nhds 0) :=
    (tendsto_xiShiftedReciprocalSquare_atTop_zero q).comp hmassSq
  have hlim : Tendsto
      (fun k : ℕ => (1 : ℂ) - xiSquaredNode q *
        xiShiftedReciprocalSquare (routeUHardEdgeMass (k : ℝ) ^ 2) q)
      atTop (nhds ((1 : ℂ) - xiSquaredNode q * 0)) :=
    (tendsto_const_nhds (x := (1 : ℂ))).sub
      ((tendsto_const_nhds (x := xiSquaredNode q)).mul hshift)
  convert hlim using 1
  · funext k
    exact routeUXiHardEdgeResolventWeight_eq_one_sub (k : ℝ) q
  · simp

/-- The mass-normalized shifted Xi resolvent is uniformly bounded throughout the divisor. -/
theorem norm_routeUXiHardEdgeResolventWeight_le_eightyFive_div_eightyFour
    (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiHardEdgeResolventWeight r q‖ ≤ (85 / 84 : ℝ) := by
  let a : ℝ := routeUHardEdgeMass r
  let y : ℝ := a ^ 2
  let z : ℂ := xiZeroCopyReciprocalSquare q
  have hy : 0 ≤ y := sq_nonneg a
  have hzre : 0 < z.re := by
    simpa only [z] using xiZeroCopyReciprocalSquare_re_pos q
  have hznorm : ‖z‖ ≤ (85 / 84 : ℝ) * z.re := by
    simpa only [z] using
      norm_xiZeroCopyReciprocalSquare_le_eightyFive_div_eightyFour_mul_re q
  have hdenRe : (1 + (y : ℂ) * z).re = 1 + y * z.re := by
    simp [Complex.mul_re]
  have hdenNorm : 1 + y * z.re ≤ ‖1 + (y : ℂ) * z‖ := by
    rw [← hdenRe]
    exact Complex.re_le_norm _
  have hdenOne : 1 ≤ ‖1 + (y : ℂ) * z‖ := by
    simpa only [z, y] using
      one_le_norm_one_add_mul_xiZeroCopyReciprocalSquare hy q
  have hdenPos : 0 < ‖1 + (y : ℂ) * z‖ := zero_lt_one.trans_le hdenOne
  rw [routeUXiHardEdgeResolventWeight, xiShiftedReciprocalSquare,
    norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hy]
  change y * (‖z‖ / ‖1 + (y : ℂ) * z‖) ≤ (85 / 84 : ℝ)
  rw [show y * (‖z‖ / ‖1 + (y : ℂ) * z‖) =
      (y * ‖z‖) / ‖1 + (y : ℂ) * z‖ by ring]
  apply (div_le_iff₀ hdenPos).2
  calc
    y * ‖z‖ ≤ y * ((85 / 84 : ℝ) * z.re) := by gcongr
    _ ≤ (85 / 84 : ℝ) * (1 + y * z.re) := by
      nlinarith [mul_nonneg hy hzre.le]
    _ ≤ (85 / 84 : ℝ) * ‖1 + (y : ℂ) * z‖ := by gcongr

/-- Reciprocal-square norm in the spectral coordinate. -/
theorem norm_xiZeroCopyReciprocalSquare_eq_inv_norm_sq (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ = 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv]
  ring

/-- Xi strip geometry and the unconditional height gap make real spectral height strong enough to
dominate the full spectral norm. -/
theorem norm_xiSpectralPoint_sq_le_abs_re_pow_four (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ ^ 2 ≤ |(xiSpectralPoint q).re| ^ 4 := by
  have hreSq : 2 < (xiSpectralPoint q).re ^ 2 := by
    have h := xiZeroCopy_two_lt_im_sq q
    simpa [xiSpectralPoint, Complex.mul_re] using h
  have hsupport := xi_divisor_support_re_mem_open_unit q.1
  have him : (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := by
    rw [xiSpectralPoint]
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_im,
      Complex.I_re, Complex.I_im]
  have himAbs : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [him, abs_lt]
    constructor <;> linarith
  have himSq : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
    nlinarith [sq_abs (xiSpectralPoint q).im, abs_nonneg (xiSpectralPoint q).im]
  have hrePos : 0 < (xiSpectralPoint q).re ^ 2 := by positivity
  have hgrowth :
      0 < ((xiSpectralPoint q).re ^ 2 - 2) * (xiSpectralPoint q).re ^ 2 :=
    mul_pos (sub_pos.mpr hreSq) hrePos
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_abs (xiSpectralPoint q).re]

/-- Uniform Fourier-decay constant used by the central divisor majorant. -/
def routeUXiComplexHardEdgeCentralDecayConstant
    (n : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  routeUComplexTiltUniformDecay n f 1 * (8 * Real.pi) ^ 2

theorem routeUXiComplexHardEdgeCentralDecayConstant_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    0 ≤ routeUXiComplexHardEdgeCentralDecayConstant n f := by
  rw [routeUXiComplexHardEdgeCentralDecayConstant]
  exact mul_nonneg (routeUComplexTiltUniformDecay_nonneg n f 1) (sq_nonneg _)

/-- Global central-packet decay in the smaller of Xi height and hard-edge mass. -/
theorem norm_routeUXiComplexHardEdgeCentral_le_min_height_mass_sq
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤
      routeUXiComplexHardEdgeCentralDecayConstant n f /
        min |(xiSpectralPoint q).re| (routeUHardEdgeMass r) ^ 2 := by
  let m : ℝ := min |(xiSpectralPoint q).re| (routeUHardEdgeMass r)
  let x : ℝ := -(routeUComplexHardEdgePhase r (xiSpectralPoint q)).re /
    (2 * Real.pi)
  let C : ℝ := routeUComplexTiltUniformDecay n f 1
  have hreSq : 2 < (xiSpectralPoint q).re ^ 2 := by
    have h := xiZeroCopy_two_lt_im_sq q
    simpa [xiSpectralPoint, Complex.mul_re] using h
  have hreAbs : 0 < |(xiSpectralPoint q).re| := by
    rw [abs_pos]
    nlinarith
  have hmass : 0 < routeUHardEdgeMass r := routeUHardEdgeMass_pos r
  have hm : 0 < m := lt_min hreAbs hmass
  have hphase :=
    min_abs_xiSpectralPoint_re_mass_div_four_le_abs_phase_re r q
  have hxabs : |x| =
      |(routeUComplexHardEdgePhase r (xiSpectralPoint q)).re| /
        (2 * Real.pi) := by
    dsimp only [x]
    rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos Real.pi_pos)]
  have hlower : m / (8 * Real.pi) ≤ |x| := by
    rw [hxabs]
    dsimp only [m] at hphase ⊢
    calc
      min |(xiSpectralPoint q).re| (routeUHardEdgeMass r) / (8 * Real.pi) =
          (min |(xiSpectralPoint q).re| (routeUHardEdgeMass r) / 4) /
            (2 * Real.pi) := by ring
      _ ≤ |(routeUComplexHardEdgePhase r (xiSpectralPoint q)).re| /
            (2 * Real.pi) :=
        (div_le_div_iff_of_pos_right (mul_pos two_pos Real.pi_pos)).2 hphase
  have hkgLower : m / (8 * Real.pi) ≤ kgFreq x :=
    hlower.trans (abs_le_kgFreq_real x)
  have hdecay :
      kgFreq x ^ 2 * ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤ C := by
    simpa only [routeUXiComplexHardEdgeCentral, x, C] using
      routeUComplexPositiveFourierExtension_uniform_decay n f
        (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one r q).le 1
  have hC : 0 ≤ C := routeUComplexTiltUniformDecay_nonneg n f 1
  have hnorm :
      ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤ C / kgFreq x ^ 2 := by
    apply (le_div_iff₀ (pow_pos (kgFreq_pos x) 2)).2
    simpa only [mul_comm] using hdecay
  calc
    ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤ C / kgFreq x ^ 2 := hnorm
    _ ≤ C / (m / (8 * Real.pi)) ^ 2 := by
      exact div_le_div_of_nonneg_left hC (pow_pos (by positivity) 2)
        (pow_le_pow_left₀ (by positivity) hkgLower 2)
    _ = routeUXiComplexHardEdgeCentralDecayConstant n f / m ^ 2 := by
      rw [routeUXiComplexHardEdgeCentralDecayConstant]
      change C / (m / (8 * Real.pi)) ^ 2 = C * (8 * Real.pi) ^ 2 / m ^ 2
      field_simp [hm.ne', Real.pi_ne_zero]

/-- Central mass-normalized Xi-divisor packet. -/
def routeUXiComplexHardEdgeCentralDivisorTerm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) : ℂ :=
  routeUXiHardEdgeResolventWeight r q *
    routeUXiComplexHardEdgeCentral n f r q ^ 2

/-- Divisor-independent coefficient in the central reciprocal-square majorant. -/
def routeUXiComplexHardEdgeCentralDivisorMajorantConstant
    (n : ℕ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  (85 / 84 : ℝ) * routeUXiComplexHardEdgeCentralDecayConstant n f ^ 2

theorem routeUXiComplexHardEdgeCentralDivisorMajorantConstant_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    0 ≤ routeUXiComplexHardEdgeCentralDivisorMajorantConstant n f := by
  rw [routeUXiComplexHardEdgeCentralDivisorMajorantConstant]
  positivity

/-- **Global Xi central-packet majorant.**  Low zeros use the uniform normalized-resolvent bound
and height decay; high zeros use reciprocal-square resolvent decay and mass decay.  Both regimes
land on the same summable Xi reciprocal-square atom. -/
theorem norm_routeUXiComplexHardEdgeCentralDivisorTerm_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    ‖routeUXiComplexHardEdgeCentralDivisorTerm n f r q‖ ≤
      routeUXiComplexHardEdgeCentralDivisorMajorantConstant n f *
        ‖xiZeroCopyReciprocalSquare q‖ := by
  let a : ℝ := routeUHardEdgeMass r
  let h : ℝ := |(xiSpectralPoint q).re|
  let A : ℝ := routeUXiComplexHardEdgeCentralDecayConstant n f
  let c : ℝ := (85 / 84 : ℝ)
  have ha : 1 ≤ a := by simp [a, routeUHardEdgeMass]
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hA : 0 ≤ A := by
    simpa only [A] using routeUXiComplexHardEdgeCentralDecayConstant_nonneg n f
  have hc : 1 ≤ c := by norm_num [c]
  have hreSq : 2 < (xiSpectralPoint q).re ^ 2 := by
    have hz := xiZeroCopy_two_lt_im_sq q
    simpa [xiSpectralPoint, Complex.mul_re] using hz
  have hh : 0 < h := by
    dsimp only [h]
    rw [abs_pos]
    nlinarith
  have hnormPos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by
    have hz : xiSpectralPoint q ≠ 0 := by
      intro hz
      rw [hz] at hreSq
      norm_num at hreSq
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hnormSq : ‖xiSpectralPoint q‖ ^ 2 ≤ h ^ 4 := by
    simpa only [h] using norm_xiSpectralPoint_sq_le_abs_re_pow_four q
  rw [routeUXiComplexHardEdgeCentralDivisorTerm, norm_mul, norm_pow]
  rcases le_total h a with hlow | hhigh
  · have hcentral : ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤ A / h ^ 2 := by
      simpa only [A, h, a, min_eq_left hlow] using
        norm_routeUXiComplexHardEdgeCentral_le_min_height_mass_sq n f r q
    have hinv : 1 / h ^ 4 ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
      rw [norm_xiZeroCopyReciprocalSquare_eq_inv_norm_sq]
      exact (div_le_div_iff₀ (pow_pos hh 4) hnormPos).2 (by simpa using hnormSq)
    calc
      ‖routeUXiHardEdgeResolventWeight r q‖ *
          ‖routeUXiComplexHardEdgeCentral n f r q‖ ^ 2 ≤
        c * (A / h ^ 2) ^ 2 := by
          exact mul_le_mul
            (by simpa only [c] using
              norm_routeUXiHardEdgeResolventWeight_le_eightyFive_div_eightyFour r q)
            (pow_le_pow_left₀ (norm_nonneg _) hcentral 2)
            (by positivity) (by positivity)
      _ = c * A ^ 2 * (1 / h ^ 4) := by ring
      _ ≤ c * A ^ 2 * ‖xiZeroCopyReciprocalSquare q‖ := by gcongr
      _ = routeUXiComplexHardEdgeCentralDivisorMajorantConstant n f *
          ‖xiZeroCopyReciprocalSquare q‖ := by
        rw [routeUXiComplexHardEdgeCentralDivisorMajorantConstant]
  · have hcentral : ‖routeUXiComplexHardEdgeCentral n f r q‖ ≤ A / a ^ 2 := by
      simpa only [A, h, a, min_eq_right hhigh] using
        norm_routeUXiComplexHardEdgeCentral_le_min_height_mass_sq n f r q
    have hweight := norm_routeUXiHardEdgeResolventWeight_le r q
    have haSq : 1 ≤ a ^ 2 := one_le_pow₀ ha
    calc
      ‖routeUXiHardEdgeResolventWeight r q‖ *
          ‖routeUXiComplexHardEdgeCentral n f r q‖ ^ 2 ≤
        (a ^ 2 * ‖xiZeroCopyReciprocalSquare q‖) * (A / a ^ 2) ^ 2 := by
          exact mul_le_mul
            (by simpa only [a] using hweight)
            (pow_le_pow_left₀ (norm_nonneg _) hcentral 2)
            (by positivity) (by positivity)
      _ = (A ^ 2 / a ^ 2) * ‖xiZeroCopyReciprocalSquare q‖ := by
        field_simp [hapos.ne']
      _ ≤ A ^ 2 * ‖xiZeroCopyReciprocalSquare q‖ := by
        gcongr
        exact div_le_self (sq_nonneg A) haSq
      _ ≤ (c * A ^ 2) * ‖xiZeroCopyReciprocalSquare q‖ := by
        gcongr
        exact le_mul_of_one_le_left (sq_nonneg A) hc
      _ = routeUXiComplexHardEdgeCentralDivisorMajorantConstant n f *
          ‖xiZeroCopyReciprocalSquare q‖ := by
        rw [routeUXiComplexHardEdgeCentralDivisorMajorantConstant]

theorem summable_routeUXiComplexHardEdgeCentralDivisorTerm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    Summable (routeUXiComplexHardEdgeCentralDivisorTerm n f r) := by
  apply Summable.of_norm_bounded
    ((summable_xiZeroCopyReciprocalSquare_pow 0).norm.mul_left
      (routeUXiComplexHardEdgeCentralDivisorMajorantConstant n f))
  intro q
  simpa using norm_routeUXiComplexHardEdgeCentralDivisorTerm_le n f r q

/-- Each central Fourier value recovers its unshifted complex spectral value along the hard edge. -/
theorem tendsto_routeUXiComplexHardEdgeCentral_natCast
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : XiZeroCopy) :
    Tendsto (fun k : ℕ => routeUXiComplexHardEdgeCentral n f (k : ℝ) q)
      atTop (nhds (routeUComplexPositiveFourierExtension n f (xiSpectralPoint q))) := by
  apply tendsto_routeUComplexPositiveFourierExtension_of_tendsto
    n f (fun k : ℕ => routeUComplexHardEdgePhase (k : ℝ) (xiSpectralPoint q))
      (xiSpectralPoint q)
  · exact tendsto_routeUComplexHardEdgePhase_natCast (xiSpectralPoint q)
  · intro k
    exact (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one (k : ℝ) q).le

/-- Pointwise convergence of each mass-normalized central Xi-divisor packet. -/
theorem tendsto_routeUXiComplexHardEdgeCentralDivisorTerm_natCast
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : XiZeroCopy) :
    Tendsto (fun k : ℕ =>
        routeUXiComplexHardEdgeCentralDivisorTerm n f (k : ℝ) q)
      atTop
      (nhds (routeUComplexPositiveFourierExtension n f (xiSpectralPoint q) ^ 2)) := by
  have hweight := tendsto_routeUXiHardEdgeResolventWeight_natCast_one q
  have hcentral := tendsto_routeUXiComplexHardEdgeCentral_natCast n f q
  have hlim := hweight.mul (hcentral.pow 2)
  simpa only [routeUXiComplexHardEdgeCentralDivisorTerm, one_mul] using hlim

/-- **Central complex HEPW divisor limit.**  The hard-edge limit passes through the complete
multiplicity-labelled Xi divisor with no zero-density premise. -/
theorem tendsto_tsum_routeUXiComplexHardEdgeCentralDivisorTerm_natCast
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℕ => ∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeCentralDivisorTerm n f (k : ℝ) q)
      atTop
      (nhds (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n f (xiSpectralPoint q) ^ 2)) := by
  apply tendsto_tsum_of_dominated_convergence
    ((summable_xiZeroCopyReciprocalSquare_pow 0).norm.mul_left
      (routeUXiComplexHardEdgeCentralDivisorMajorantConstant n f))
  · exact tendsto_routeUXiComplexHardEdgeCentralDivisorTerm_natCast n f
  · exact Filter.Eventually.of_forall fun k q => by
      simpa using
        norm_routeUXiComplexHardEdgeCentralDivisorTerm_le n f (k : ℝ) q

/-- Full mass-normalized squared lattice sample at one Xi divisor point. -/
def routeUXiComplexHardEdgeSampleDivisorTerm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) : ℂ :=
  routeUXiHardEdgeResolventWeight r q *
    routeUXiComplexHardEdgeSample n f r q ^ 2

theorem routeUXiComplexHardEdgeSampleDivisorTerm_eq_central_add_error
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) :
    routeUXiComplexHardEdgeSampleDivisorTerm n f r q =
      routeUXiComplexHardEdgeCentralDivisorTerm n f r q +
        routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q := by
  rw [routeUXiComplexHardEdgeSampleDivisorTerm,
    routeUXiComplexHardEdgeCentralDivisorTerm,
    routeUXiComplexHardEdgeAliasSquareErrorTerm]
  ring

theorem summable_routeUXiComplexHardEdgeSampleDivisorTerm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    Summable (routeUXiComplexHardEdgeSampleDivisorTerm n f r) := by
  have hsum := (summable_routeUXiComplexHardEdgeCentralDivisorTerm n f r).add
    (summable_routeUXiComplexHardEdgeAliasSquareErrorTerm n f r)
  exact hsum.congr fun q =>
    (routeUXiComplexHardEdgeSampleDivisorTerm_eq_central_add_error n f r q).symm

theorem tsum_routeUXiComplexHardEdgeSampleDivisorTerm_eq_central_add_error
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) :
    (∑' q : XiZeroCopy, routeUXiComplexHardEdgeSampleDivisorTerm n f r q) =
      (∑' q : XiZeroCopy, routeUXiComplexHardEdgeCentralDivisorTerm n f r q) +
        ∑' q : XiZeroCopy,
          routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q := by
  calc
    (∑' q : XiZeroCopy, routeUXiComplexHardEdgeSampleDivisorTerm n f r q) =
        ∑' q : XiZeroCopy,
          (routeUXiComplexHardEdgeCentralDivisorTerm n f r q +
            routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q) := by
      apply tsum_congr
      exact routeUXiComplexHardEdgeSampleDivisorTerm_eq_central_add_error n f r
    _ = (∑' q : XiZeroCopy, routeUXiComplexHardEdgeCentralDivisorTerm n f r q) +
        ∑' q : XiZeroCopy,
          routeUXiComplexHardEdgeAliasSquareErrorTerm n f r q := by
      exact (summable_routeUXiComplexHardEdgeCentralDivisorTerm n f r).tsum_add
        (summable_routeUXiComplexHardEdgeAliasSquareErrorTerm n f r)

/-- **Full complex HEPW divisor limit.**  Exact lattice samples, not central surrogates, converge
after mass-normalized summation over the complete Xi divisor. -/
theorem tendsto_tsum_routeUXiComplexHardEdgeSampleDivisorTerm_natCast
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun k : ℕ => ∑' q : XiZeroCopy,
        routeUXiComplexHardEdgeSampleDivisorTerm n f (k : ℝ) q)
      atTop
      (nhds (∑' q : XiZeroCopy,
        routeUComplexPositiveFourierExtension n f (xiSpectralPoint q) ^ 2)) := by
  have hcentral :=
    tendsto_tsum_routeUXiComplexHardEdgeCentralDivisorTerm_natCast n f
  have halias :=
    tendsto_tsum_routeUXiComplexHardEdgeAliasSquareErrorTerm_natCast_zero n f
  have hsum := hcentral.add halias
  convert hsum using 1
  · funext k
    exact tsum_routeUXiComplexHardEdgeSampleDivisorTerm_eq_central_add_error
      n f (k : ℝ)
  · simp

end RHTower
