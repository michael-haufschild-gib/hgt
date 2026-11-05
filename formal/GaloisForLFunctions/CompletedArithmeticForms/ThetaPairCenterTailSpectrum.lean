import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomFourierTail
import GaloisForLFunctions.RHTower.MellinHardyBridge
import GaloisForLFunctions.RHTower.WeightedLaplaceShift

/-!
# Exact signs of integrated theta-pair spectra

Center integration makes the radial factor strictly positive at every real
frequency. The remaining sign is exactly the logarithmic ratio cosine.
In particular every diagonal pair is positive, while each unequal pair has
negative frequencies.
-/

open Complex Set MeasureTheory
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower
noncomputable section

private theorem integral_expScale_tail {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) (r : ℝ) :
    (∫ s in Ioi r, (a * Real.exp s) * g (a * Real.exp s)) =
      ∫ u in Ioi (a * Real.exp r), g u := by
  rw [integral_Ioi_expScale (mul_pos ha (Real.exp_pos r))]
  have ht := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
    (fun s : ℝ => (a * Real.exp s) * g (a * Real.exp s)) r r
  rw [sub_self] at ht
  rw [← ht]
  apply integral_congr_ae
  filter_upwards with s
  rw [Real.exp_add]
  simp only [smul_eq_mul, mul_assoc, mul_comm (Real.exp s) (Real.exp r)]

private theorem exp_half_radial_coefficient {a : ℝ} (ha : 0 < a) (s : ℝ) :
    a ^ (-(1 / 2 : ℝ)) * (a * Real.exp s) *
      (a * Real.exp s) ^ (-(1 / 2 : ℝ)) = Real.exp (s / 2) := by
  have hp : (a * Real.exp s) * (a * Real.exp s) ^ (-(1 / 2 : ℝ)) =
      (a * Real.exp s) ^ (1 / 2 : ℝ) := by
    calc
      _ = (a * Real.exp s) ^ (1 : ℝ) * (a * Real.exp s) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add (mul_pos ha (Real.exp_pos s))]
        norm_num
  rw [mul_assoc, hp, Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos (mul_pos ha (Real.exp_pos s)),
    ← Real.exp_add, Real.log_mul ha.ne' (Real.exp_pos s).ne', Real.log_exp]
  congr 1
  ring

/-- Exponential center coordinates convert a half-density into its radial power measure. -/
theorem integral_exp_half_mul_radial {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (r : ℝ) :
    (∫ s in Ioi r, Real.exp (s / 2) * f (a * Real.exp s)) =
      a ^ (-(1 / 2 : ℝ)) *
        ∫ u in Ioi (a * Real.exp r), u ^ (-(1 / 2 : ℝ)) * f u := by
  rw [← integral_expScale_tail ha (fun u => u ^ (-(1 / 2 : ℝ)) * f u) r,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [← exp_half_radial_coefficient ha s]
  ring

/-- The literal real Wigner tail of one ordered pair of theta atoms. -/
def thetaPairCenterTailSpectrum (n m : ℕ) (r b : ℝ) : ℝ :=
  ∫ s in Ioi r, (thetaCuspSourcePairWigner n m (s / 2) b).re

/-- The positive radial amplitude of an ordered-pair center tail. -/
def thetaPairCenterTailAmplitude (n m : ℕ) (r b : ℝ) : ℝ :=
  4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) *
    besselFirstAtomTailDensity (b / 2) (Real.pi * n * m * Real.exp r)

private theorem pair_scale_lower {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) : 3 < Real.pi * n * m * Real.exp r := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he := Real.one_le_exp hr
  have hp := Real.pi_gt_three
  have hpn := le_mul_of_one_le_right Real.pi_pos.le hnR
  have hpnm : Real.pi * n ≤ Real.pi * n * m :=
    le_mul_of_one_le_right (by positivity) hmR
  have hlast : Real.pi * n * m ≤ Real.pi * n * m * Real.exp r :=
    le_mul_of_one_le_right (by positivity) he
  exact hp.trans_le (hpn.trans (hpnm.trans hlast))

private theorem pair_scale_threshold {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) : 1 + Real.sqrt 2 < Real.pi * n * m * Real.exp r := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith only [pair_scale_lower hn hm hr, hs]

theorem thetaPairCenterTailAmplitude_pos {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) : 0 < thetaPairCenterTailAmplitude n m r b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  exact mul_pos (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (mul_pos (mul_pos Real.pi_pos hnR) hmR) _))
    (besselFirstAtomTailDensity_pos (pair_scale_threshold hn hm hr) _)

private theorem divisorRatioPhase_re (n m : ℕ) (b : ℝ) :
    (thetaCuspWignerDivisorRatioPhase n m b).re =
      Real.cos (b * (Real.log n - Real.log m)) := by
  simp only [thetaCuspWignerDivisorRatioPhase, Complex.exp_re,
    Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, neg_zero,
    Real.exp_zero, one_mul, Real.cos_neg]

/-- The literal integrated pair spectrum has precisely its ratio cosine as signed factor. -/
theorem thetaPairCenterTailSpectrum_eq {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    thetaPairCenterTailSpectrum n m r b =
      Real.cos (b * (Real.log n - Real.log m)) * thetaPairCenterTailAmplitude n m r b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < Real.pi * n * m := mul_pos (mul_pos Real.pi_pos hnR) hmR
  have hq : 1 < Real.pi * n * m * Real.exp r :=
    lt_trans (by norm_num) (pair_scale_lower hn hm hr)
  have he (s : ℝ) : (thetaCuspSourcePairWigner n m (s / 2) b).re =
      Real.cos (b * (Real.log n - Real.log m)) *
        (Real.exp (s / 2) * (thetaCuspWignerRadialTransform
          (2 * (Real.pi * n * m * Real.exp s)) b).re) := by
    rw [thetaCuspSourcePairWigner_eq_phase_mul_radial hn hm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      thetaCuspWignerRadialTransform_im_zero, divisorRatioPhase_re,
      zero_mul, mul_zero, sub_zero, add_zero]
    have hc : thetaCuspWignerAtomScale n m (s / 2) =
        2 * (Real.pi * n * m * Real.exp s) := by
      unfold thetaCuspWignerAtomScale
      rw [show 2 * (s / 2) = s by ring]
      ring
    rw [hc]
    ring
  unfold thetaPairCenterTailSpectrum
  simp_rw [he]
  rw [integral_const_mul, integral_exp_half_mul_radial ha
    (fun u : ℝ => (thetaCuspWignerRadialTransform (2 * u) b).re) r]
  have htail := integral_rpow_mul_thetaCuspWignerRadialTransform_re hq (b / 2)
  rw [show 2 * (b / 2) = b by ring] at htail
  rw [htail]
  unfold thetaPairCenterTailAmplitude
  ring

/-- No frequency restriction remains in the exact sign test for an integrated atom pair. -/
theorem thetaPairCenterTailSpectrum_nonneg_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    0 ≤ thetaPairCenterTailSpectrum n m r b ↔
      0 ≤ Real.cos (b * (Real.log n - Real.log m)) := by
  rw [thetaPairCenterTailSpectrum_eq hn hm hr,
    mul_nonneg_iff_of_pos_right (thetaPairCenterTailAmplitude_pos hn hm hr b)]

/-- Every diagonal pair has a strictly positive integrated spectrum at every frequency. -/
theorem thetaPairCenterTailSpectrum_diagonal_pos {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) : 0 < thetaPairCenterTailSpectrum n n r b := by
  rw [thetaPairCenterTailSpectrum_eq hn hn hr]
  simpa only [sub_self, mul_zero, Real.cos_zero, one_mul] using
    thetaPairCenterTailAmplitude_pos hn hn hr b

/-- Every ordered pair is strictly positive at zero frequency. -/
theorem thetaPairCenterTailSpectrum_zero_pos {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) : 0 < thetaPairCenterTailSpectrum n m r 0 := by
  rw [thetaPairCenterTailSpectrum_eq hn hm hr]
  simpa only [zero_mul, Real.cos_zero, one_mul] using
    thetaPairCenterTailAmplitude_pos hn hm hr 0

/-- Each unequal pair has a negative frequency at every nonnegative center cutoff. -/
theorem thetaPairCenterTailSpectrum_unequal_neg {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hne : n ≠ m) {r : ℝ} (hr : 0 ≤ r) :
    thetaPairCenterTailSpectrum n m r (Real.pi / (Real.log n - Real.log m)) < 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log n - Real.log m ≠ 0 := by
    intro h
    have he := Real.log_injOn_pos hnR hmR (sub_eq_zero.mp h)
    exact hne (by exact_mod_cast he)
  rw [thetaPairCenterTailSpectrum_eq hn hm hr, div_mul_cancel₀ _ hlog,
    Real.cos_pi, neg_one_mul]
  exact neg_neg_of_pos (thetaPairCenterTailAmplitude_pos hn hm hr _)

/-- Explicit frequency-dependent exponential cost of the signed radial density. -/
def besselFirstAtomTailCost (τ : ℝ) : ℝ :=
  4 * besselPowerTailCost (7 / 2) τ + 6 * besselPowerTailCost (3 / 2) τ +
    6 * besselPowerTailCost (5 / 2) τ

theorem besselFirstAtomTailCost_nonneg (τ : ℝ) : 0 ≤ besselFirstAtomTailCost τ := by
  unfold besselFirstAtomTailCost
  exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (besselPowerTailCost_nonneg _ _))
    (mul_nonneg (by norm_num) (besselPowerTailCost_nonneg _ _)))
      (mul_nonneg (by norm_num) (besselPowerTailCost_nonneg _ _))

/-- The complete signed radial density has an absolute exponential envelope. -/
theorem abs_besselFirstAtomTailDensity_le {q : ℝ} (hq : 1 ≤ q) (τ : ℝ) :
    |besselFirstAtomTailDensity τ q| ≤ besselFirstAtomTailCost τ * Real.exp (-q) := by
  have h7 := abs_besselPowerTail_le hq (7 / 2) τ
  have h3 := abs_besselPowerTail_le hq (3 / 2) τ
  have h5 := norm_besselPowerIntegrand_le hq (5 / 2) τ
  rw [Real.norm_eq_abs] at h5
  calc
    _ ≤ |4 * besselPowerTail (7 / 2) τ q - 6 * besselPowerTail (3 / 2) τ q| +
        |6 * q ^ (5 / 2 : ℝ) * besselRadialValue τ q| := abs_sub _ _
    _ ≤ (|4 * besselPowerTail (7 / 2) τ q| + |6 * besselPowerTail (3 / 2) τ q|) +
        |6 * q ^ (5 / 2 : ℝ) * besselRadialValue τ q| :=
      by
        have h := abs_sub (4 * besselPowerTail (7 / 2) τ q) (6 * besselPowerTail (3 / 2) τ q)
        linarith only [h]
    _ = 4 * |besselPowerTail (7 / 2) τ q| + 6 * |besselPowerTail (3 / 2) τ q| +
        6 * |q ^ (5 / 2 : ℝ) * besselRadialValue τ q| := by
      rw [mul_assoc 6]
      norm_num [abs_mul]
    _ ≤ (4 * besselPowerTailCost (7 / 2) τ + 6 * besselPowerTailCost (3 / 2) τ +
        6 * besselPowerTailCost (5 / 2) τ) * Real.exp (-q) := by
      nlinarith only [h7, h3, h5]
    _ = _ := rfl

/-- An absolute exponential bound for each literal ordered-pair tail. -/
theorem abs_thetaPairCenterTailSpectrum_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    |thetaPairCenterTailSpectrum n m r b| ≤
      4 * besselFirstAtomTailCost (b / 2) *
        Real.exp (-(Real.pi * Real.exp r * n * m)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 1 ≤ Real.pi * n * m := by
    have h1 := le_mul_of_one_le_right Real.pi_pos.le hnR
    have h2 : Real.pi * n ≤ Real.pi * n * m := le_mul_of_one_le_right (by positivity) hmR
    linarith only [Real.pi_gt_three, h1, h2]
  have hp : (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le ha (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    simpa only [Real.rpow_zero] using h
  have hq := pair_scale_threshold hn hm hr
  have hb := abs_besselFirstAtomTailDensity_le
    (show 1 ≤ Real.pi * n * m * Real.exp r by linarith only [pair_scale_lower hn hm hr])
    (b / 2)
  have hpos := besselFirstAtomTailDensity_pos hq (b / 2)
  have hc := thetaPairCenterTailAmplitude_pos hn hm hr b
  rw [thetaPairCenterTailSpectrum_eq hn hm hr, abs_mul, abs_of_pos hc]
  calc
    _ ≤ 1 * thetaPairCenterTailAmplitude n m r b :=
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hc.le
    _ = 4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) *
        |besselFirstAtomTailDensity (b / 2) (Real.pi * n * m * Real.exp r)| := by
      rw [one_mul, abs_of_pos hpos]
      rfl
    _ ≤ 4 * 1 * (besselFirstAtomTailCost (b / 2) *
        Real.exp (-(Real.pi * n * m * Real.exp r))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hb
        (abs_nonneg _) (by norm_num)
    _ = _ := by
      rw [show Real.pi * n * m * Real.exp r = Real.pi * Real.exp r * n * m by ring]
      ring

/-- Imaginary-order Schläfli mass is bounded by the zero-order mass. -/
theorem besselOrderUnitMass_imag_le (τ : ℝ) :
    HTGeometry.besselOrderUnitMass ((τ : ℂ) * I) ≤ HTGeometry.besselOrderUnitMass 0 := by
  unfold HTGeometry.besselOrderUnitMass
  apply setIntegral_mono_on
    (HTGeometry.integrableOn_besselOrderKernel (by norm_num : (0 : ℝ) < 1) _).norm
    (HTGeometry.integrableOn_besselOrderKernel (by norm_num : (0 : ℝ) < 1) _).norm
    measurableSet_Ioi
  intro t _
  rw [HTGeometry.besselOrderKernel_eq_ofReal_mul, HTGeometry.besselOrderKernel_eq_ofReal_mul]
  have he : (τ : ℂ) * I * (t : ℂ) = ((τ * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [he, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  simp only [norm_mul, zero_mul, Complex.cosh_zero, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- Every radial-power cost admits the same bound at all imaginary frequencies. -/
theorem besselPowerTailCost_le_zero (p τ : ℝ) :
    besselPowerTailCost p τ ≤ besselPowerTailCost p 0 := by
  unfold besselPowerTailCost
  simp only [mul_zero, Complex.ofReal_zero, zero_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (besselOrderUnitMass_imag_le (2 * τ)) (Real.exp_pos _).le)
    (by positivity)

/-- The signed tail's absolute cost has a frequency-independent upper bound. -/
theorem besselFirstAtomTailCost_le_zero (τ : ℝ) :
    besselFirstAtomTailCost τ ≤ besselFirstAtomTailCost 0 := by
  unfold besselFirstAtomTailCost
  linarith only [besselPowerTailCost_le_zero (7 / 2) τ,
    besselPowerTailCost_le_zero (3 / 2) τ, besselPowerTailCost_le_zero (5 / 2) τ]

/-- A single exponential envelope controls every frequency of every ordered pair. -/
theorem abs_thetaPairCenterTailSpectrum_uniform_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    |thetaPairCenterTailSpectrum n m r b| ≤
      4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * Real.exp r * n * m)) := by
  exact (abs_thetaPairCenterTailSpectrum_le hn hm hr b).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (besselFirstAtomTailCost_le_zero _) (by norm_num))
      (Real.exp_pos _).le)

end
end GaloisForLFunctions.CompletedArithmeticForms
