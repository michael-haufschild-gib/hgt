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

end
end GaloisForLFunctions.CompletedArithmeticForms
