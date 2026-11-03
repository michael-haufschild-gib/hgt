import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerKreinLaxPhillipsRealization
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerThetaCore
import GaloisForLFunctions.HTGeometry.ThetaSumPeriodParseval

/-!
# Spectral bounds for the actual Mayer period cores

Gaussian sum comparison and theta reciprocity bound the renormalized ray at both
endpoints. Weighted Cauchy–Schwarz bounds the actual theta correlation. Its Cauchy
transform has a uniformly bounded central moment after normalization; the Gamma
recurrence cancels one normalization factor exactly.

The resulting explicit bound controls the actual core throughout the upper strip.
On resonances, the zeta zero-free region and a fixed Gamma strip give polynomial
height growth times `exp (π Im s / 2)`, retaining the cusp decay `a^(−Re s)`.
-/

set_option autoImplicit false

noncomputable section
open Complex Set MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerThetaRay MayerThetaProduct MayerThetaCore

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem thetaSum_split {t : ℝ} (ht : 0 < t) :
    thetaSum t = 1 + 2 * ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
  let f : ℤ → ℝ := fun n => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)
  have hf : Summable f := summable_thetaSum ht
  have hp : Summable (fun n : ℕ => f (n : ℤ)) :=
    hf.comp_injective (fun m n h => by omega)
  have hn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun m n h => by omega)
  have hhead := (hp.sum_add_tsum_nat_add 1).symm
  have he (n : ℕ) : f (-((n : ℤ) + 1)) =
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
    dsimp [f]
    push_cast
    congr 1
    ring
  have he' (n : ℕ) : f ((n + 1 : ℕ) : ℤ) =
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) := by
    dsimp [f]
    push_cast
    congr 1
    ring
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one hp hn, hhead]
  simp only [Finset.sum_range_one, he, he']
  have hz : f 0 = 1 := by simp [f]
  rw [Nat.cast_zero, hz]
  ring

private theorem thetaSum_le_gaussian_integral {t : ℝ} (ht : 0 < t) :
    thetaSum t ≤ 1 + (Real.sqrt t)⁻¹ := by
  rw [thetaSum_split ht]
  have h := GaloisForLFunctions.HTGeometry.tsum_exp_neg_sq_succ_le ht
  have he : 2 * (1 / (2 * Real.sqrt t)) = (Real.sqrt t)⁻¹ := by ring
  linarith

private theorem thetaRay_real {t : ℝ} (ht : 0 < t) :
    thetaRay t = (((thetaSum t - 1 - (Real.sqrt t)⁻¹) / 2 : ℝ) : ℂ) := by
  rw [thetaRay]
  have hp : (t : ℂ) ^ (-1 / 2 : ℂ) = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) := by
    rw [show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring, Complex.cpow_neg,
      Real.sqrt_eq_rpow, Complex.ofReal_inv, Complex.ofReal_cpow ht.le]
    norm_num
  rw [hp]
  push_cast
  rfl

/-- Gaussian sum comparison and reciprocity give bounds at both endpoints. -/
theorem thetaRay_norm_le {t : ℝ} (ht : 0 < t) :
    ‖thetaRay t‖ ≤ min (1 / 2 : ℝ) ((Real.sqrt t)⁻¹ / 2) := by
  have hb (u : ℝ) (hu : 0 < u) : ‖thetaRay u‖ ≤ (Real.sqrt u)⁻¹ / 2 := by
    rw [thetaRay_real hu, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [thetaSum_le_gaussian_integral hu])]
    linarith [one_le_thetaSum hu]
  refine le_min ?_ (hb t ht)
  have hi := hb (1 / t) (one_div_pos.mpr ht)
  rw [thetaRay_inv ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos ht _).le,
    ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, inv_inv] at hi
  nlinarith only [hi, Real.sqrt_pos.mpr ht]

private theorem thetaRay_measurable : Measurable thetaRay := by
  have ht : Measurable thetaSum := by
    unfold thetaSum
    apply Measurable.tsum
    intro n
    fun_prop
  unfold thetaRay
  fun_prop

private theorem thetaRay_square_integrable {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IntegrableOn (fun t : ℝ => t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) (Ioi 0) := by
  have hu : 0 < ((r : ℂ) / 2).re := by simp; linarith
  have hu1 : ((r : ℂ) / 2).re < 1 / 2 := by simp; linarith
  have hm := (thetaRay_hasMellin hu hu1).1.norm
  have hL : IntegrableOn (fun t : ℝ => t ^ (r / 2 - 1) * ‖thetaRay t‖) (Ioi 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun hm (fun t ht => ?_) measurableSet_Ioi
    change ‖(t : ℂ) ^ ((r : ℂ) / 2 - 1) • thetaRay t‖ = _
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    congr 2
    simp
  have hmeas : Measurable (fun t : ℝ => t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) := by
    have := thetaRay_measurable
    fun_prop
  apply (hL.const_mul (1 / 2 : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hb := (thetaRay_norm_le ht0).trans (min_le_left _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖thetaRay t‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖thetaRay t‖ := by
    nlinarith only [norm_nonneg (thetaRay t), hb]
  calc
    _ ≤ t ^ (r / 2 - 1) * ((1 / 2 : ℝ) * ‖thetaRay t‖) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos ht0 _).le
    _ = _ := by ring

/-- An explicit Mellin square bound for the volume-subtracted Gaussian ray. -/
theorem thetaRay_square_mellin_bound {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ t in Ioi (0 : ℝ), t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) ≤
      1 / (2 * r) + 1 / (2 * (2 - r)) := by
  have hi := thetaRay_square_integrable hr hr1
  have hlo : -1 < r / 2 - 1 := by linarith
  have hhi : r / 2 - 2 < -1 := by linarith
  have hp0 : IntegrableOn (fun t : ℝ => t ^ (r / 2 - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' hlo).1
  have hp1 := integrableOn_Ioi_rpow_of_lt hhi (show (0 : ℝ) < 1 by norm_num)
  have hsmall : (∫ t in Ioc (0 : ℝ) 1, t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∫ t in Ioc (0 : ℝ) 1, t ^ (r / 2 - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hi.mono_set Ioc_subset_Ioi_self) (hp0.const_mul _)
      measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have hb := (thetaRay_norm_le ht0).trans (min_le_left _ _)
    have hs : ‖thetaRay t‖ ^ 2 ≤ (1 / 4 : ℝ) := by
      nlinarith only [hb, norm_nonneg (thetaRay t)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos ht0 _).le
  have hlarge : (∫ t in Ioi (1 : ℝ), t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∫ t in Ioi (1 : ℝ), t ^ (r / 2 - 2) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hi.mono_set (Ioi_subset_Ioi zero_le_one)) (hp1.const_mul _)
      measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hb := (thetaRay_norm_le ht0).trans (min_le_right _ _)
    have hs : ‖thetaRay t‖ ^ 2 ≤ (1 / 4 : ℝ) * t⁻¹ := by
      calc
        _ ≤ ((Real.sqrt t)⁻¹ / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = _ := by rw [div_pow, inv_pow, Real.sq_sqrt ht0.le]; ring
    calc
      _ ≤ t ^ (r / 2 - 1) * ((1 / 4 : ℝ) * t⁻¹) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos ht0 _).le
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_neg_one, ← Real.rpow_add ht0]
        congr 2
        ring
  have hsplit : (∫ t in Ioi (0 : ℝ), t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) =
      (∫ t in Ioc (0 : ℝ) 1, t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2) +
        ∫ t in Ioi (1 : ℝ), t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2 := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hv0 : (∫ t in Ioc (0 : ℝ) 1, t ^ (r / 2 - 1)) = 2 / r := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl hlo), Real.one_rpow,
      Real.zero_rpow (by linarith : r / 2 - 1 + 1 ≠ 0)]
    field_simp [ne_of_gt hr]
    ring
  have hv1 : (∫ t in Ioi (1 : ℝ), t ^ (r / 2 - 2)) = 2 / (2 - r) := by
    rw [integral_Ioi_rpow_of_lt hhi zero_lt_one, Real.one_rpow]
    rw [show r / 2 - 2 + 1 = -(2 - r) / 2 by ring]
    field_simp [show 2 - r ≠ 0 by linarith]
  rw [hsplit]
  calc
    _ ≤ (1 / 4 : ℝ) * (∫ t in Ioc (0 : ℝ) 1, t ^ (r / 2 - 1)) +
        (1 / 4 : ℝ) * (∫ t in Ioi (1 : ℝ), t ^ (r / 2 - 2)) := add_le_add hsmall hlarge
    _ = _ := by
      rw [hv0, hv1]
      field_simp [ne_of_gt hr, show 2 - r ≠ 0 by linarith]
      ring

private theorem thetaRay_scaled_square {r a : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (r / 2 - 1) * ‖thetaRay (a ^ 2 * t)‖ ^ 2) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t ^ (r / 2 - 1) * ‖thetaRay (a ^ 2 * t)‖ ^ 2) =
        a ^ (-r) * ∫ t in Ioi (0 : ℝ), t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2 := by
  let p : ℝ := r / 2 - 1
  let F : ℝ → ℝ := fun t => t ^ p * ‖thetaRay t‖ ^ 2
  have hi : IntegrableOn F (Ioi 0) := thetaRay_square_integrable hr hr1
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have he (t : ℝ) (ht : 0 < t) :
      t ^ p * ‖thetaRay (a ^ 2 * t)‖ ^ 2 =
        (a ^ 2) ^ (-p) * F (a ^ 2 * t) := by
    dsimp [F]
    rw [Real.mul_rpow ha2.le ht.le]
    rw [show (a ^ 2) ^ (-p) * ((a ^ 2) ^ p * t ^ p * ‖thetaRay (a ^ 2 * t)‖ ^ 2) =
      ((a ^ 2) ^ (-p) * (a ^ 2) ^ p) * (t ^ p * ‖thetaRay (a ^ 2 * t)‖ ^ 2) by ring,
      ← Real.rpow_add ha2, neg_add_cancel, Real.rpow_zero, one_mul]
  have hcomp : IntegrableOn (fun t => F (a ^ 2 * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff F 0 ha2).mpr
    simpa only [mul_zero] using hi
  constructor
  · exact MeasureTheory.IntegrableOn.congr_fun (hcomp.const_mul ((a ^ 2) ^ (-p)))
      (fun t ht => (he t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
      integral_comp_mul_left_Ioi F 0 ha2, mul_zero, smul_eq_mul]
    have hpow : (a ^ 2) ^ (-p) * (a ^ 2)⁻¹ = a ^ (-r) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ha2,
        ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
      congr 1
      dsimp [p]
      ring
    rw [← mul_assoc, hpow]

/-- The Gaussian correlation gives a spectral bound with only a reciprocal Gamma factor.
The decay suffices for upper Haar square energy throughout the open strip. -/
theorem fieldCore_spectral_decay_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) {a : ℝ} (ha : 0 < a) :
    ‖MayerScatteringCore.fieldCore w a‖ ≤
      ((1 / w.re + 1 / (2 - w.re)) / ‖Gammaℝ w‖) * a ^ (-w.re / 2) := by
  let r : ℝ := w.re
  let q : ℝ := a ^ (-r / 2)
  let F : ℝ → ℝ := fun t => t ^ (r / 2 - 1) * ‖thetaRay t‖ ^ 2
  let G : ℝ → ℝ := fun t => t ^ (r / 2 - 1) * ‖thetaRay (a ^ 2 * t)‖ ^ 2
  have hq : 0 < q := Real.rpow_pos_of_pos ha _
  have hF : IntegrableOn F (Ioi 0) := thetaRay_square_integrable hw hw1
  obtain ⟨hG, hscale⟩ := thetaRay_scaled_square hw hw1 ha
  have hscale' : (∫ t in Ioi (0 : ℝ), G t) = a ^ (-r) * ∫ t in Ioi (0 : ℝ), F t := hscale
  have hqq : a ^ (-r) = q ^ 2 := by
    dsimp [q]
    rw [← Real.rpow_natCast (a ^ (-r / 2)) 2, ← Real.rpow_mul ha.le]
    congr 1
    norm_num
  have hpoint (t : ℝ) (ht : 0 < t) :
      ‖(t : ℂ) ^ (w / 2 - 1) * thetaRay t * thetaRay (a ^ 2 * t)‖ ≤
        (q / 2) * F t + (1 / (2 * q)) * G t := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    have hre : (w / 2 - 1).re = r / 2 - 1 := by simp [r]
    rw [hre]
    have htwo : 0 < 2 * q := by positivity
    have hxy : ‖thetaRay t‖ * ‖thetaRay (a ^ 2 * t)‖ ≤
        (q / 2) * ‖thetaRay t‖ ^ 2 + (1 / (2 * q)) * ‖thetaRay (a ^ 2 * t)‖ ^ 2 := by
      calc
        _ ≤ (q ^ 2 * ‖thetaRay t‖ ^ 2 + ‖thetaRay (a ^ 2 * t)‖ ^ 2) / (2 * q) :=
          (le_div_iff₀ htwo).mpr (by
            nlinarith only [sq_nonneg (q * ‖thetaRay t‖ - ‖thetaRay (a ^ 2 * t)‖)])
        _ = _ := by field_simp
    calc
      _ ≤ t ^ (r / 2 - 1) *
          ((q / 2) * ‖thetaRay t‖ ^ 2 + (1 / (2 * q)) * ‖thetaRay (a ^ 2 * t)‖ ^ 2) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hxy (Real.rpow_pos_of_pos ht _).le
      _ = _ := by dsimp [F, G]; ring
  have hprod := (core_theta_hasMellin hw (by linarith) him ha).1.norm
  have hprod' : IntegrableOn
      (fun t : ℝ => ‖(t : ℂ) ^ (w / 2 - 1) * thetaRay t * thetaRay (a ^ 2 * t)‖) (Ioi 0) := by
    simpa only [IntegrableOn, thetaProduct, smul_eq_mul, mul_assoc] using hprod
  have hnorm : ‖∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (w / 2 - 1) * thetaRay t * thetaRay (a ^ 2 * t)‖ ≤
        q * ∫ t in Ioi (0 : ℝ), F t := by
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ),
          ‖(t : ℂ) ^ (w / 2 - 1) * thetaRay t * thetaRay (a ^ 2 * t)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (0 : ℝ), (q / 2) * F t + (1 / (2 * q)) * G t :=
        setIntegral_mono_on hprod' ((hF.const_mul _).add (hG.const_mul _))
          measurableSet_Ioi hpoint
      _ = _ := by
        rw [integral_add (hF.const_mul _) (hG.const_mul _), integral_const_mul, integral_const_mul]
        rw [hscale', hqq]
        field_simp [ne_of_gt hq]
        ring
  rw [core_theta_integral hw (by linarith) him ha, norm_mul, norm_div, Complex.norm_ofNat]
  calc
    _ ≤ (2 / ‖Gammaℝ w‖) * (q * ∫ t in Ioi (0 : ℝ), F t) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ (2 / ‖Gammaℝ w‖) * (q * (1 / (2 * r) + 1 / (2 * (2 - r)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (thetaRay_square_mellin_bound hw hw1) hq.le) (by positivity)
    _ = _ := by
      dsimp [r, q]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The field and Cauchy normalizations cancel one Gamma factor exactly. -/
theorem gammaR_mul_averagingFactor {w : ℂ} (hw : 0 < w.re) :
    Gammaℝ w * MayerQuadraticCone.averagingFactor w =
      (Real.pi : ℂ) ^ ((1 - w) / 2) * Gamma ((w + 1) / 2) / w := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hw2 : w / 2 ≠ 0 := div_ne_zero hw0 (by norm_num)
  have hg : Gamma (w / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : (Real.pi : ℂ) ^ (-w / 2) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) =
      (Real.pi : ℂ) ^ ((1 - w) / 2) := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  rw [Gammaℝ_def, MayerQuadraticCone.averagingFactor,
    MayerScatteringNormalization.archimedeanFactor,
    show (w + 2) / 2 - 1 / 2 = (w + 1) / 2 by ring,
    show (w + 2) / 2 = w / 2 + 1 by ring,
    Gamma_add_one _ hw2]
  calc
    _ = ((Real.pi : ℂ) ^ (-w / 2) * (Real.pi : ℂ) ^ (1 / 2 : ℂ)) *
        Gamma ((w + 1) / 2) / w := by field_simp [hg, hw0]
    _ = _ := by rw [hp]

private theorem cauchy_central_mass_integrable {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => ‖MayerQuadraticCone.cauchyKernel w t‖ *
      t ^ (w.re / 2) / t) (Ioi 0) := by
  have hu : -1 < ((w.re / 2 : ℝ) : ℂ).re := by simp; linarith
  have hu1 : ((w.re / 2 : ℝ) : ℂ).re < w.re + 1 := by simp; linarith
  have h := (MayerCauchyMellinSymbol.cauchyKernel_hasMellin hw hu hu1).1.norm
  refine MeasureTheory.IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  change ‖(t : ℂ) ^ (((w.re / 2 : ℝ) : ℂ) - 1) • MayerQuadraticCone.cauchyKernel w t‖ = _
  rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [Real.rpow_sub ht, Real.rpow_one]
  ring

private theorem cauchy_central_mass_integrand {w : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖MayerQuadraticCone.cauchyKernel w t‖ * t ^ (w.re / 2) / t =
      ‖MayerQuadraticCone.averagingFactor w‖⁻¹ *
        (t ^ (w.re / 2) * (1 + t ^ 2) ^ (-(w.re + 2) / 2)) := by
  rw [MayerQuadraticCone.cauchyKernel, MayerQuadraticCone.cauchyWeight,
    norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have hre : (-((w + 2) / 2)).re = -(w.re + 2) / 2 := by simp; ring
  rw [hre]
  field_simp

/-- The absolute central Cauchy moment is uniform after removing its explicit normalization. -/
theorem cauchy_central_mass_le {w : ℂ} (hw : 0 < w.re) :
    (∫ t in Ioi (0 : ℝ), ‖MayerQuadraticCone.cauchyKernel w t‖ *
      t ^ (w.re / 2) / t) ≤ 2 / ‖MayerQuadraticCone.averagingFactor w‖ := by
  let B : ℝ := ‖MayerQuadraticCone.averagingFactor w‖⁻¹
  let f : ℝ → ℝ := fun t => ‖MayerQuadraticCone.cauchyKernel w t‖ * t ^ (w.re / 2) / t
  have hi : IntegrableOn f (Ioi 0) := cauchy_central_mass_integrable hw
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : f t ≤ B := by
    rw [show f t = B * (t ^ (w.re / 2) * (1 + t ^ 2) ^ (-(w.re + 2) / 2)) from
      cauchy_central_mass_integrand ht.1]
    have h1 := Real.rpow_le_one ht.1.le ht.2 (by linarith : 0 ≤ w.re / 2)
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos
      (by nlinarith only [sq_nonneg t] : 1 ≤ 1 + t ^ 2)
      (by linarith : -(w.re + 2) / 2 ≤ 0)
    have hprod : t ^ (w.re / 2) * (1 + t ^ 2) ^ (-(w.re + 2) / 2) ≤ 1 := by
      nlinarith only [h1, h2, Real.rpow_nonneg ht.1.le (w.re / 2),
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + t ^ 2) (-(w.re + 2) / 2)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hB
  have hl (t : ℝ) (ht : 1 < t) : f t ≤ B * t ^ (-2 : ℝ) := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [show f t = B * (t ^ (w.re / 2) * (1 + t ^ 2) ^ (-(w.re + 2) / 2)) from
      cauchy_central_mass_integrand ht0]
    apply mul_le_mul_of_nonneg_left _ hB
    have hpow : (1 + t ^ 2) ^ (-(w.re + 2) / 2) ≤ (t ^ 2) ^ (-(w.re + 2) / 2) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos ht0) (by linarith)
        (by linarith)
    calc
      _ ≤ t ^ (w.re / 2) * (t ^ 2) ^ (-(w.re + 2) / 2) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_pos_of_pos ht0 _).le
      _ = t ^ (-w.re / 2 - 2) := by
        rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
        congr 1
        norm_num
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)
  have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one
  have hsmall : (∫ t in Ioc (0 : ℝ) 1, f t) ≤ B := by
    calc
      _ ≤ ∫ _t in Ioc (0 : ℝ) 1, B := setIntegral_mono_on
        (hi.mono_set Ioc_subset_Ioi_self) (integrableOn_const (by simp)) measurableSet_Ioc hs
      _ = _ := by simp
  have hlarge : (∫ t in Ioi (1 : ℝ), f t) ≤ B := by
    calc
      _ ≤ ∫ t in Ioi (1 : ℝ), B * t ^ (-2 : ℝ) := setIntegral_mono_on
        (hi.mono_set (Ioi_subset_Ioi zero_le_one)) (hp.const_mul B) measurableSet_Ioi hl
      _ = _ := by rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  change (∫ t in Ioi (0 : ℝ), f t) ≤ _
  rw [hsplit]
  have hb : B + B = 2 / ‖MayerQuadraticCone.averagingFactor w‖ := by dsimp [B]; ring
  exact (add_le_add hsmall hlarge).trans_eq hb

/-- The Cauchy transform preserves the theta correlation bound with an explicit spectral factor. -/
theorem cauchyCore_spectral_decay_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) {a : ℝ} (ha : 0 < a) :
    ‖_root_.RHTower.positiveMellinConvolution (MayerQuadraticCone.cauchyKernel w)
        (MayerScatteringCore.fieldCore w) a‖ ≤
      (2 * (1 / w.re + 1 / (2 - w.re)) /
        (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖)) * a ^ (-w.re / 2) := by
  let D : ℝ := (1 / w.re + 1 / (2 - w.re)) / ‖Gammaℝ w‖
  have hD : 0 ≤ D := by
    have hden : 0 < 2 - w.re := by linarith
    dsimp [D]
    positivity
  have hmass := cauchy_central_mass_integrable hw
  have hcore := MayerScatteringCore.cauchyKernel_core_integrable hw him ha
  have hp (t : ℝ) (ht : 0 < t) :
      (a / t) ^ (-w.re / 2) = a ^ (-w.re / 2) * t ^ (w.re / 2) := by
    rw [Real.div_rpow ha.le ht.le, show -w.re / 2 = -(w.re / 2) by ring,
      Real.rpow_neg ht.le, div_inv_eq_mul]
  have hpoint (t : ℝ) (ht : 0 < t) :
      ‖MayerQuadraticCone.cauchyKernel w t * MayerScatteringCore.fieldCore w (a / t) / (t : ℂ)‖ ≤
        (D * a ^ (-w.re / 2)) *
          (‖MayerQuadraticCone.cauchyKernel w t‖ * t ^ (w.re / 2) / t) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    have hf := fieldCore_spectral_decay_bound hw hw1 him (div_pos ha ht)
    rw [hp t ht] at hf
    calc
      _ ≤ (‖MayerQuadraticCone.cauchyKernel w t‖ *
          (D * (a ^ (-w.re / 2) * t ^ (w.re / 2)))) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (norm_nonneg _)) ht.le
      _ = _ := by ring
  change ‖∫ t in Ioi (0 : ℝ),
    MayerQuadraticCone.cauchyKernel w t * MayerScatteringCore.fieldCore w (a / t) / (t : ℂ)‖ ≤ _
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖MayerQuadraticCone.cauchyKernel w t * MayerScatteringCore.fieldCore w (a / t) / (t : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), (D * a ^ (-w.re / 2)) *
        (‖MayerQuadraticCone.cauchyKernel w t‖ * t ^ (w.re / 2) / t) :=
      setIntegral_mono_on hcore.norm (hmass.const_mul _) measurableSet_Ioi hpoint
    _ = (D * a ^ (-w.re / 2)) * ∫ t in Ioi (0 : ℝ),
        ‖MayerQuadraticCone.cauchyKernel w t‖ * t ^ (w.re / 2) / t := by rw [integral_const_mul]
    _ ≤ (D * a ^ (-w.re / 2)) * (2 / ‖MayerQuadraticCone.averagingFactor w‖) :=
      mul_le_mul_of_nonneg_left (cauchy_central_mass_le hw) (by positivity)
    _ = _ := by dsimp [D]; ring

private theorem inv_gammaR_averaging_norm {w : ℂ} (hw : 0 < w.re) :
    1 / (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖) =
      ‖w‖ * Real.pi ^ ((w.re - 1) / 2) / ‖Gamma ((w + 1) / 2)‖ := by
  have h := congrArg norm (gammaR_mul_averagingFactor hw)
  rw [norm_mul, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at h
  have hre : ((1 - w) / 2).re = (1 - w.re) / 2 := by simp
  rw [hre] at h
  rw [h]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  rw [← Real.rpow_neg Real.pi_pos.le, show -((1 - w.re) * (2 : ℝ)⁻¹) = (w.re - 1) * (2 : ℝ)⁻¹ by ring]
  ring

/-- Only one reciprocal Gamma factor remains in the actual period-core bound. -/
theorem cauchyCore_gamma_bound {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) {a : ℝ} (ha : 0 < a) :
    ‖_root_.RHTower.positiveMellinConvolution (MayerQuadraticCone.cauchyKernel w)
        (MayerScatteringCore.fieldCore w) a‖ ≤
      (2 * (1 / w.re + 1 / (2 - w.re)) * ‖w‖ * Real.pi ^ ((w.re - 1) / 2) /
        ‖Gamma ((w + 1) / 2)‖) * a ^ (-w.re / 2) := by
  have h := cauchyCore_spectral_decay_bound hw hw1 him ha
  have he : 2 * (1 / w.re + 1 / (2 - w.re)) /
      (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖) =
      2 * (1 / w.re + 1 / (2 - w.re)) * ‖w‖ * Real.pi ^ ((w.re - 1) / 2) /
        ‖Gamma ((w + 1) / 2)‖ := by
    calc
      _ = (2 * (1 / w.re + 1 / (2 - w.re))) *
          (1 / (‖Gammaℝ w‖ * ‖MayerQuadraticCone.averagingFactor w‖)) := by ring
      _ = _ := by rw [inv_gammaR_averaging_norm hw]; ring
  simpa only [he] using h

/-- An explicit spectral bound for the actual PM core throughout the upper open strip. -/
theorem mayerPeriodCore_spectral_bound {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1 / 2)
    (him : 0 < s.im) {a : ℝ} (ha : 0 < a) :
    ‖mayerPeriodCore s a‖ ≤
      (2 * (1 / (2 * s.re) + 1 / (2 - 2 * s.re)) * ‖2 * s‖ *
        Real.pi ^ ((2 * s.re - 1) / 2) / ‖Gamma (s + 1 / 2)‖) * a ^ (-s.re) := by
  have hw : 0 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s).re < 1 := by simp; linarith
  have hwi : 0 < (2 * s).im := by simp; linarith
  have h := cauchyCore_gamma_bound hw hw1 hwi ha
  change ‖mayerPeriodCore s a‖ ≤ _ at h
  rw [show (2 * s).re = 2 * s.re by simp,
    show (2 * s + 1) / 2 = s + 1 / 2 by ring,
    show -(2 * s.re) / 2 = -s.re by ring] at h
  exact h

/-- The zero-free region controls the left strip edge at every upper resonance. -/
theorem upperMayerResonance_reciprocal_bound (s : upperMayerResonances) :
    2 ≤ s.1.im ∧ 1 / (2 * s.1.re) ≤ 116 * s.1.im := by
  have h0 : 0 < (2 * s.1).re := by simp; linarith [s.2.2.1]
  have h1 : (2 * s.1).re < 1 := by simp; linarith [s.2.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith [s.2.1]
  have hz : riemannZeta (2 * s.1) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  have hfour := _root_.RHTower.four_le_abs_im_of_zeta_zero h0 h1 hz
  have hedge := _root_.RHTower.one_div_le_re_of_zeta_zero h0 h1 hz
  rw [abs_of_pos him] at hfour hedge
  have hre : (2 * s.1).re = 2 * s.1.re := by simp
  have him' : (2 * s.1).im = 2 * s.1.im := by simp
  rw [him'] at hfour
  rw [hre, him'] at hedge
  have hy : 2 ≤ s.1.im := by linarith
  have hlog : 0 < Real.log (2 * s.1.im) := Real.log_pos (by linarith)
  have hm := (div_le_iff₀ hlog).mp hedge
  have hrec : 1 / (2 * s.1.re) ≤ 58 * Real.log (2 * s.1.im) := by
    apply (div_le_iff₀ (by linarith [s.2.2.1] : 0 < 2 * s.1.re)).mpr
    nlinarith only [hm]
  refine ⟨hy, hrec.trans ?_⟩
  have hlogle := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 * s.1.im)
  linarith

/-- The actual resonant cores have uniform exponential growth in height and decaying cusp tails. -/
theorem upperMayerCore_growth_bound :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ a > 0,
      ‖mayerPeriodCore s.1 a‖ ≤
        (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) * a ^ (-s.1.re) := by
  obtain ⟨C, N, hC, hgamma⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_inv_Gamma_strip (1 / 2) 1
  refine ⟨468 * C, N + 2, by positivity, fun s a ha => ?_⟩
  obtain ⟨hy, hedge⟩ := upperMayerResonance_reciprocal_bound s
  have hx : 0 < s.1.re := s.2.2.1
  have hx1 : s.1.re < 1 / 2 := s.2.2.2.1
  have hy0 : 0 < s.1.im := s.2.1
  have hden : 0 < 2 - 2 * s.1.re := by linarith
  have hS : 1 / (2 * s.1.re) + 1 / (2 - 2 * s.1.re) ≤ 117 * (1 + s.1.im) := by
    have hsecond : 1 / (2 - 2 * s.1.re) ≤ 1 := (div_le_one hden).mpr (by linarith)
    linarith
  have hnorm : ‖2 * s.1‖ ≤ 2 * (1 + s.1.im) := by
    have hs : ‖s.1‖ ≤ s.1.re + s.1.im := by
      calc
        _ = ‖(s.1.re : ℂ) + (s.1.im : ℂ) * I‖ := by rw [Complex.re_add_im]
        _ ≤ ‖(s.1.re : ℂ)‖ + ‖(s.1.im : ℂ) * I‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Complex.norm_I, mul_one, Real.norm_of_nonneg hx.le, Real.norm_of_nonneg hy0.le]
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have hpi : Real.pi ^ ((2 * s.1.re - 1) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hgim : (s.1 + 1 / 2).im = s.1.im := by simp
  have hG := hgamma (s.1 + 1 / 2) (by simp; linarith) (by simp; linarith)
    (by simpa only [hgim, abs_of_pos hy0] using (show 1 ≤ s.1.im by linarith))
  rw [hgim, abs_of_pos hy0, norm_inv] at hG
  have hG' : ‖Gamma (s.1 + 1 / 2)‖⁻¹ ≤
      C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2) :=
    hG.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le (by linarith) N) hC)
      (Real.exp_pos _).le)
  have hm : 2 * (1 / (2 * s.1.re) + 1 / (2 - 2 * s.1.re)) * ‖2 * s.1‖ *
      Real.pi ^ ((2 * s.1.re - 1) / 2) / ‖Gamma (s.1 + 1 / 2)‖ ≤
        (468 * C) * (1 + s.1.im) ^ (N + 2) * Real.exp (Real.pi * s.1.im / 2) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (2 * (117 * (1 + s.1.im))) * (2 * (1 + s.1.im)) * 1 *
          (C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num)) hnorm
              (norm_nonneg _) (by positivity)
          · exact hpi
          · exact Real.rpow_nonneg Real.pi_pos.le _
          · positivity
        · exact hG'
        · positivity
        · positivity
      _ = _ := by rw [pow_add, pow_two]; ring
  exact (mayerPeriodCore_spectral_bound hx hx1 hy0 ha).trans
    (mul_le_mul_of_nonneg_right hm (Real.rpow_pos_of_pos ha _).le)

#print axioms mayerPeriodCore_spectral_bound
#print axioms upperMayerCore_growth_bound

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
