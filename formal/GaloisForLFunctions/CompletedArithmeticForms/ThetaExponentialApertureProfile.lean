import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomExponentialProfile
import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureWeight

/-!
# Exponential profiles with the exact theta aperture

Power raising retains the product-scale exponential while paying the entire
center integral. At aperture one quarter, the diagonal summability exponent
is strictly greater than one.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open RHTower
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The positive polynomial kernel of the averaged radial tail. -/
def exponentialProfileKernel (c u : ℝ) : ℝ :=
  u ^ (3 / 2 : ℝ) * ((2 * u - 3) ^ 2 + 12 * (1 - c) * u) * Real.exp (-2 * c * u)

theorem integrableOn_exponentialProfileKernel {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) : IntegrableOn (exponentialProfileKernel c) (Ioi q) := by
  have h7 := (integrableOn_exponentialPowerIntegrand
    (by norm_num : (-1 : ℝ) < 7 / 2) (by positivity : 0 < 2 * c) hq.le).const_mul (4 : ℝ)
  have h5 := (integrableOn_exponentialPowerIntegrand
    (by norm_num : (-1 : ℝ) < 5 / 2) (by positivity : 0 < 2 * c) hq.le).const_mul (12 * c)
  have h3 := (integrableOn_exponentialPowerIntegrand
    (by norm_num : (-1 : ℝ) < 3 / 2) (by positivity : 0 < 2 * c) hq.le).const_mul (9 : ℝ)
  apply ((h7.sub h5).add h3).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change 4 * (u ^ (7 / 2 : ℝ) * Real.exp (-(2 * c) * u)) -
    (12 * c) * (u ^ (5 / 2 : ℝ) * Real.exp (-(2 * c) * u)) +
    9 * (u ^ (3 / 2 : ℝ) * Real.exp (-(2 * c) * u)) = exponentialProfileKernel c u
  rw [exponentialProfileKernel, exponentialProfile_rpow_polynomial_identity (hq.trans hu)]
  simp only [neg_mul, mul_assoc]
  ring

theorem exponentialProfileKernel_nonneg {c u : ℝ} (hc1 : c ≤ 1) (hu : 0 ≤ u) :
    0 ≤ exponentialProfileKernel c u := by
  unfold exponentialProfileKernel
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hu _)
    (add_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hc1)) hu))) (Real.exp_pos _).le

private theorem exponentialProfileKernel_ge_power {c u : ℝ}
    (hc1 : c ≤ 1) (hu : 3 ≤ u) :
    u ^ (7 / 2 : ℝ) * Real.exp (-2 * c * u) ≤ exponentialProfileKernel c u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hsq : u ^ 2 ≤ (2 * u - 3) ^ 2 :=
    pow_le_pow_left₀ hu0.le (by linarith only [hu]) 2
  have hcorr : 0 ≤ 12 * (1 - c) * u :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hc1)) hu0.le
  have hpow : u ^ (7 / 2 : ℝ) = u ^ (3 / 2 : ℝ) * u ^ (2 : ℕ) := by
    calc
      _ = u ^ ((3 / 2 : ℝ) + 2) := by norm_num
      _ = u ^ (3 / 2 : ℝ) * u ^ (2 : ℝ) := Real.rpow_add hu0 _ _
      _ = _ := by rw [Real.rpow_two]
  rw [hpow, exponentialProfileKernel]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hsq.trans (le_add_of_nonneg_right hcorr))
      (Real.rpow_nonneg hu0.le _)) (Real.exp_pos _).le

/-- The radial square pays an entire positive power tail beyond any larger cutoff at least three. -/
theorem besselFirstAtomExponentialTail_ge_powerTail {c q y : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hq : 0 < q) (hqy : q ≤ y) (hy3 : 3 ≤ y) :
    exponentialPowerTail (7 / 2) (2 * c) y ≤ besselFirstAtomExponentialTail c q := by
  have hy : 0 < y := hq.trans_le hqy
  rw [besselFirstAtomExponentialTail_eq_polynomial hc hq]
  change exponentialPowerTail (7 / 2) (2 * c) y ≤ ∫ u in Ioi q, exponentialProfileKernel c u
  calc
    _ ≤ ∫ u in Ioi y, exponentialProfileKernel c u := by
      change (∫ u in Ioi y, u ^ (7 / 2 : ℝ) * Real.exp (-(2 * c) * u)) ≤ _
      apply setIntegral_mono_on
        (integrableOn_exponentialPowerIntegrand (by norm_num : (-1 : ℝ) < 7 / 2)
          (by positivity : 0 < 2 * c) hy.le)
        (integrableOn_exponentialProfileKernel hc hy) measurableSet_Ioi
      intro u hu
      simpa only [neg_mul, mul_assoc] using
        exponentialProfileKernel_ge_power hc1 (hy3.trans hu.le)
    _ ≤ _ := setIntegral_mono_set (integrableOn_exponentialProfileKernel hc hq)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact exponentialProfileKernel_nonneg hc1 (hq.trans hu).le)
      (Filter.Eventually.of_forall fun u hu => hqy.trans_lt hu)

/-- Exact scaling supplies a uniform positive radial lower bound throughout a moving cutoff. -/
theorem besselFirstAtomExponentialTail_scaled_lower {N D q : ℝ}
    (hN : 1 ≤ N) (hD : 3 ≤ D) (hq : 0 < q) (hqD : q ≤ N * D) :
    N ^ (9 / 2 : ℝ) * exponentialPowerTail (7 / 2) 2 D ≤
      besselFirstAtomExponentialTail (1 / N) q := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hc1 : 1 / N ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hN
  have hND : 3 ≤ N * D := by
    have h := mul_nonneg (sub_nonneg.mpr hN) hD0
    nlinarith only [h, hD]
  have hb := besselFirstAtomExponentialTail_ge_powerTail
    (by positivity : 0 < 1 / N) hc1 hq hqD hND
  have hs := exponentialPowerTail_scale (7 / 2) 2 hN0 hD0
  norm_num only [show (7 / 2 : ℝ) + 1 = 9 / 2 by norm_num] at hs
  rw [show 2 * (1 / N) = 2 / N by ring, hs] at hb
  exact hb

/-- The Gamma mass controlling the raised radial power. -/
def exponentialApertureGammaMass (c : ℝ) : ℝ :=
  (1 / c) ^ (39 / 8 : ℝ) * Real.Gamma (39 / 8)

private theorem exponentialApertureGammaMass_pos {c : ℝ} (hc : 0 < c) :
    0 < exponentialApertureGammaMass c := by
  unfold exponentialApertureGammaMass
  positivity

/-- The complete aperture integration of the frequency-averaged radial profile. -/
def thetaExponentialApertureProfile (a c x : ℝ) : ℝ :=
  4 * Real.pi * x ^ (-(1 / 2 : ℝ)) *
    ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight a r *
      besselFirstAtomExponentialTail c (x * Real.exp r)

private theorem quarter_aperture_exp_upper {r : ℝ} (hr : 0 ≤ r) :
    thetaCuspCenterTailWeight (1 / 4) r ≤ 4 * Real.exp ((5 / 16 : ℝ) * r) := by
  have hw := thetaCuspCenterTailWeight_le (by norm_num : (0 : ℝ) ≤ 1 / 4) hr
  have hp : 1 + (1 / 4 : ℝ) * r ≤ 4 * Real.exp (r / 16) := by
    linarith only [Real.add_one_le_exp (r / 16)]
  have he : Real.exp (r / 16) * Real.exp ((1 / 4 : ℝ) * r) =
      Real.exp ((5 / 16 : ℝ) * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (1 + (1 / 4 : ℝ) * r) * Real.exp ((1 / 4 : ℝ) * r) := hw
    _ ≤ (4 * Real.exp (r / 16)) * Real.exp ((1 / 4 : ℝ) * r) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, he]

/-- A center-decaying majorant retains the product exponential and the Gamma scale. -/
theorem quarter_aperture_exponentialProfile_pointwise {c x r : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) (hr : 0 ≤ r) :
    thetaCuspCenterTailWeight (1 / 4) r * besselFirstAtomExponentialTail c (x * Real.exp r) ≤
      (16 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) * Real.exp (-c * x)) *
        Real.exp (-(1 / 16 : ℝ) * r) := by
  have hq : 0 < x * Real.exp r := mul_pos hx (Real.exp_pos r)
  have hG0 := besselFirstAtomExponentialTail_nonneg hc hc1 hq
  have hraised := besselFirstAtomExponentialTail_raise_upper hc hq (by norm_num : (0 : ℝ) ≤ 3 / 8)
  norm_num only [show (7 / 2 : ℝ) + 3 / 8 + 1 = 39 / 8 by norm_num] at hraised
  change (x * Real.exp r) ^ (3 / 8 : ℝ) *
      besselFirstAtomExponentialTail c (x * Real.exp r) ≤
      4 * (Real.exp (-c * (x * Real.exp r)) * exponentialApertureGammaMass c) at hraised
  have hbound : besselFirstAtomExponentialTail c (x * Real.exp r) ≤
      (x * Real.exp r) ^ (-(3 / 8 : ℝ)) *
        (4 * (Real.exp (-c * (x * Real.exp r)) * exponentialApertureGammaMass c)) := by
    calc
      _ = (x * Real.exp r) ^ (-(3 / 8 : ℝ)) *
          ((x * Real.exp r) ^ (3 / 8 : ℝ) *
            besselFirstAtomExponentialTail c (x * Real.exp r)) := by
        rw [← mul_assoc, ← Real.rpow_add hq]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hraised (Real.rpow_nonneg hq.le _)
  have hpow : (x * Real.exp r) ^ (-(3 / 8 : ℝ)) =
      x ^ (-(3 / 8 : ℝ)) * Real.exp (-(3 / 8 : ℝ) * r) := by
    rw [Real.mul_rpow hx.le (Real.exp_pos r).le,
      Real.rpow_def_of_pos (Real.exp_pos r), Real.log_exp,
      mul_comm r (-(3 / 8 : ℝ))]
  have hphase : Real.exp ((5 / 16 : ℝ) * r) * Real.exp (-(3 / 8 : ℝ) * r) =
      Real.exp (-(1 / 16 : ℝ) * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hradial : Real.exp (-c * (x * Real.exp r)) ≤ Real.exp (-c * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (le_mul_of_one_le_right hx.le (Real.one_le_exp hr)) (neg_nonpos.mpr hc.le))
  calc
    _ ≤ (4 * Real.exp ((5 / 16 : ℝ) * r)) *
        ((x * Real.exp r) ^ (-(3 / 8 : ℝ)) *
          (4 * (Real.exp (-c * (x * Real.exp r)) * exponentialApertureGammaMass c))) :=
      mul_le_mul (quarter_aperture_exp_upper hr) hbound hG0 (by positivity)
    _ = (16 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) *
        Real.exp (-c * (x * Real.exp r))) * Real.exp (-(1 / 16 : ℝ) * r) := by
      rw [hpow]
      calc
        _ = (16 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) *
          Real.exp (-c * (x * Real.exp r))) *
          (Real.exp ((5 / 16 : ℝ) * r) * Real.exp (-(3 / 8 : ℝ) * r)) := by ring
        _ = _ := by rw [hphase]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hradial (by
        have hH := (exponentialApertureGammaMass_pos hc).le
        positivity)) (Real.exp_pos _).le

/-- The exact quarter-aperture profile is absolutely integrable in its center. -/
theorem integrableOn_quarter_aperture_exponentialProfile {c x : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) :
    IntegrableOn (fun r : ℝ => thetaCuspCenterTailWeight (1 / 4) r *
      besselFirstAtomExponentialTail c (x * Real.exp r)) (Ioi 0) := by
  have hw : Continuous (thetaCuspCenterTailWeight (1 / 4)) := by
    unfold thetaCuspCenterTailWeight
    fun_prop
  have hG := (stronglyMeasurable_besselFirstAtomExponentialTail c).comp_measurable
    (by fun_prop : Measurable (fun r : ℝ => x * Real.exp r))
  apply ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 16 : ℝ) < 0) 0).const_mul
    (16 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) * Real.exp (-c * x))).mono'
    (hw.stronglyMeasurable.mul hG).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change ‖thetaCuspCenterTailWeight (1 / 4) r *
    besselFirstAtomExponentialTail c (x * Real.exp r)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (thetaCuspCenterTailWeight_nonneg (by norm_num) hr.le)
    (besselFirstAtomExponentialTail_nonneg hc hc1 (mul_pos hx (Real.exp_pos r))))]
  exact quarter_aperture_exponentialProfile_pointwise hc hc1 hx hr.le

/-- Power raising controls the complete center integral at its exact Gamma scale. -/
theorem integral_quarter_aperture_exponentialProfile_le {c x : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) :
    (∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight (1 / 4) r *
      besselFirstAtomExponentialTail c (x * Real.exp r)) ≤
      256 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) * Real.exp (-c * x) := by
  have hm := (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 16 : ℝ) < 0) 0).const_mul
    (16 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) * Real.exp (-c * x))
  have h := setIntegral_mono_on (integrableOn_quarter_aperture_exponentialProfile hc hc1 hx)
    hm measurableSet_Ioi (fun r hr => quarter_aperture_exponentialProfile_pointwise hc hc1 hx hr.le)
  have he : (∫ r in Ioi (0 : ℝ), Real.exp (-(1 / 16 : ℝ) * r)) = 16 := by
    have he0 := integral_exp_mul_Ioi (by norm_num : -(1 / 16 : ℝ) < 0) (0 : ℝ)
    norm_num at he0
    simpa only [neg_mul] using he0
  rw [integral_const_mul, he] at h
  exact h.trans_eq (by ring)

/-- The integrated product profile keeps both a summable diagonal power and exponential product decay. -/
theorem thetaExponentialApertureProfile_weighted_upper {c x : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) :
    x ^ (7 / 8 : ℝ) * thetaExponentialApertureProfile (1 / 4) c x ≤
      1024 * Real.pi * exponentialApertureGammaMass c * Real.exp (-c * x) := by
  have hI := integral_quarter_aperture_exponentialProfile_le hc hc1 hx
  have hpow : x ^ (7 / 8 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 8 : ℝ)) = 1 := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    norm_num
  unfold thetaExponentialApertureProfile
  calc
    _ = (x ^ (7 / 8 : ℝ) * (4 * Real.pi * x ^ (-(1 / 2 : ℝ)))) *
        (∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight (1 / 4) r *
          besselFirstAtomExponentialTail c (x * Real.exp r)) := by ring
    _ ≤ (x ^ (7 / 8 : ℝ) * (4 * Real.pi * x ^ (-(1 / 2 : ℝ)))) *
        (256 * exponentialApertureGammaMass c * x ^ (-(3 / 8 : ℝ)) * Real.exp (-c * x)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (x ^ (7 / 8 : ℝ) * x ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 8 : ℝ))) *
        (1024 * Real.pi * exponentialApertureGammaMass c * Real.exp (-c * x)) := by ring
    _ = _ := by rw [hpow, one_mul]

/-- A fixed center interval retains a positive radial mass at every scale. -/
theorem thetaExponentialApertureProfile_weighted_lower {N D x : ℝ}
    (hN : 1 ≤ N) (hD : 3 ≤ D) (hx : 0 < x)
    (hxD : x * Real.exp 2 ≤ N * D) :
    4 * Real.pi * thetaCuspCenterTailWeight (1 / 4) 1 *
        N ^ (9 / 2 : ℝ) * exponentialPowerTail (7 / 2) 2 D ≤
      x ^ (1 / 2 : ℝ) * thetaExponentialApertureProfile (1 / 4) (1 / N) x := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hc : 0 < 1 / N := by positivity
  have hc1 : 1 / N ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hN
  let C : ℝ := thetaCuspCenterTailWeight (1 / 4) 1 *
    N ^ (9 / 2 : ℝ) * exponentialPowerTail (7 / 2) 2 D
  have hT := exponentialPowerTail_nonneg (7 / 2) 2 hD0
  have hw1 := thetaCuspCenterTailWeight_nonneg
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hw1 (Real.rpow_nonneg hN0.le _)) hT
  have hp (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
      C ≤ thetaCuspCenterTailWeight (1 / 4) r *
        besselFirstAtomExponentialTail (1 / N) (x * Real.exp r) := by
    have hr0 : 0 ≤ r := zero_le_one.trans hr.1
    have hqD : x * Real.exp r ≤ N * D :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr.2) hx.le).trans hxD
    have hG := besselFirstAtomExponentialTail_scaled_lower hN hD
      (mul_pos hx (Real.exp_pos r)) hqD
    have hw := thetaCenterTailWeight_mono
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1) hr.1
    calc
      C = thetaCuspCenterTailWeight (1 / 4) 1 *
          (N ^ (9 / 2 : ℝ) * exponentialPowerTail (7 / 2) 2 D) := by dsimp only [C]; ring
      _ ≤ _ := mul_le_mul hw hG (mul_nonneg (Real.rpow_nonneg hN0.le _) hT)
        (thetaCuspCenterTailWeight_nonneg (by norm_num) hr0)
  have hi := integrableOn_quarter_aperture_exponentialProfile hc hc1 hx
  have hseg := hi.mono_set (show Icc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) from
    fun r hr => zero_lt_one.trans_le hr.1)
  have hconst : IntegrableOn (fun _ : ℝ => C) (Icc (1 : ℝ) 2) := by
    apply hseg.mono' stronglyMeasurable_const.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg hC]
    exact hp r hr
  have hsegLower := setIntegral_mono_on hconst hseg measurableSet_Icc hp
  have hconstIntegral : (∫ _r in Icc (1 : ℝ) 2, C) = C := by
    norm_num [setIntegral_const, Measure.real, Real.volume_Icc]
  rw [hconstIntegral] at hsegLower
  have hsegFull : (∫ r in Icc (1 : ℝ) 2, thetaCuspCenterTailWeight (1 / 4) r *
      besselFirstAtomExponentialTail (1 / N) (x * Real.exp r)) ≤
      ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight (1 / 4) r *
        besselFirstAtomExponentialTail (1 / N) (x * Real.exp r) := by
    apply setIntegral_mono_set hi ?_
      (Filter.Eventually.of_forall fun r hr => zero_lt_one.trans_le hr.1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (thetaCuspCenterTailWeight_nonneg (by norm_num) hr.le)
      (besselFirstAtomExponentialTail_nonneg hc hc1 (mul_pos hx (Real.exp_pos r)))
  have hI := hsegLower.trans hsegFull
  have hpow : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hx]
    norm_num
  have he : x ^ (1 / 2 : ℝ) * thetaExponentialApertureProfile (1 / 4) (1 / N) x =
      4 * Real.pi * ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight (1 / 4) r *
        besselFirstAtomExponentialTail (1 / N) (x * Real.exp r) := by
    unfold thetaExponentialApertureProfile
    calc
      _ = (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ))) *
          (4 * Real.pi * ∫ r in Ioi (0 : ℝ), thetaCuspCenterTailWeight (1 / 4) r *
            besselFirstAtomExponentialTail (1 / N) (x * Real.exp r)) := by ring
      _ = _ := by rw [hpow, one_mul]
  rw [he]
  simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left hI
    (show 0 ≤ 4 * Real.pi by positivity)

end GaloisForLFunctions.CompletedArithmeticForms

