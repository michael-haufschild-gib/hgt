import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureRemainder
import GaloisForLFunctions.CompletedArithmeticForms.TwoAtomApertureWeight

/-!
# Strict Fourier positivity of the two-atom aperture spectrum

Multiplicative atom scales become translated center cutoffs. Convexity of the
aperture weight pays the ratio-cosine cross term, and the initial center
interval leaves strictly positive mass at every real frequency.
-/

set_option autoImplicit false

open Complex Set MeasureTheory Filter
open RHTower

namespace GaloisForLFunctions.CompletedArithmeticForms

noncomputable section

private theorem aperture_positivePart_shift (a h : ℝ) (F : ℝ → ℝ) (hh : 0 ≤ h) :
    (∫ s in Ioi (0 : ℝ), thetaCuspCenterTailWeight a (max 0 (s - h)) * F s) =
      ∫ s in Ioi h, thetaCuspCenterTailWeight a (s - h) * F s := by
  have he : (fun s : ℝ => thetaCuspCenterTailWeight a (max 0 (s - h)) * F s) =
      (Ioi h).indicator (fun s => thetaCuspCenterTailWeight a (s - h) * F s) := by
    funext s
    by_cases hs : h < s
    · rw [Set.indicator_of_mem (show s ∈ Ioi h from hs), max_eq_right (sub_nonneg.mpr hs.le)]
    · rw [Set.indicator_of_notMem (show s ∉ Ioi h from hs),
        max_eq_left (sub_nonpos.mpr (not_lt.mp hs))]
      simp only [thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero, Real.cosh_zero,
        zero_mul, add_zero]
  rw [he, integral_indicator measurableSet_Ioi]
  change (∫ s, _ ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi h))) = _
  rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hh]

private theorem pair_amplitude_shift {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (r b : ℝ) :
    thetaPairCenterTailAmplitude n m r b =
      Real.exp (-(Real.log ((n : ℝ) * m)) / 2) *
        thetaPairCenterTailAmplitude 1 1 (r + Real.log ((n : ℝ) * m)) b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm : 0 < (n : ℝ) * m := mul_pos hnR hmR
  have harg : Real.pi * Real.exp (r + Real.log ((n : ℝ) * m)) =
      Real.pi * n * m * Real.exp r := by
    rw [Real.exp_add, Real.exp_log hnm]
    ring
  have hcoef : (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-(Real.log ((n : ℝ) * m)) / 2) * Real.pi ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos (mul_pos (mul_pos Real.pi_pos hnR) hmR),
      Real.rpow_def_of_pos Real.pi_pos, ← Real.exp_add,
      show Real.pi * n * m = Real.pi * ((n : ℝ) * m) by ring,
      Real.log_mul Real.pi_pos.ne' hnm.ne']
    congr 1
    ring
  simp only [thetaPairCenterTailAmplitude, Nat.cast_one, mul_one, harg, hcoef]
  ring

/-- Multiplicative atom scale becomes a translated center cutoff. -/
theorem thetaPairApertureSpectrum_eq_shifted {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℝ) :
    thetaPairApertureSpectrum n m a b =
      Real.cos (b * (Real.log n - Real.log m)) * Real.exp (-(Real.log ((n : ℝ) * m)) / 2) *
        ∫ s in Ioi (0 : ℝ), thetaCuspCenterTailWeight a (max 0 (s - Real.log ((n : ℝ) * m))) *
          thetaPairCenterTailSpectrum 1 1 s b := by
  let h := Real.log ((n : ℝ) * m)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : 0 ≤ h := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hnR hmR)
  have hp (r : ℝ) (hr : 0 ≤ r) :
      thetaPairCenterTailSpectrum n m r b =
        Real.cos (b * (Real.log n - Real.log m)) * Real.exp (-h / 2) *
          thetaPairCenterTailSpectrum 1 1 (r + h) b := by
    rw [thetaPairCenterTailSpectrum_eq hn hm hr,
      pair_amplitude_shift hn hm r b,
      thetaPairCenterTailSpectrum_eq (by decide : 0 < 1) (by decide : 0 < 1) (add_nonneg hr hh)]
    simp only [Nat.cast_one, Real.log_one, sub_self, mul_zero, Real.cos_zero, one_mul, h]
    ring
  have ht := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
    (fun s : ℝ => thetaCuspCenterTailWeight a (s - h) * thetaPairCenterTailSpectrum 1 1 s b) h h
  rw [sub_self] at ht
  simp only [add_sub_cancel_right] at ht
  change _ = _ * ∫ s in Ioi (0 : ℝ), thetaCuspCenterTailWeight a (max 0 (s - h)) *
    thetaPairCenterTailSpectrum 1 1 s b
  rw [aperture_positivePart_shift a h _ hh, ← ht, ← integral_const_mul]
  unfold thetaPairApertureSpectrum
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [hp r hr.le]
  ring

private theorem integrable_shifted_aperture {a h : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (hh : 0 ≤ h) (b : ℝ) :
    IntegrableOn (fun s => thetaCuspCenterTailWeight a (max 0 (s - h)) *
      thetaPairCenterTailSpectrum 1 1 s b) (Ioi 0) := by
  have hw : Continuous (fun s : ℝ => thetaCuspCenterTailWeight a (max 0 (s - h))) := by
    unfold thetaCuspCenterTailWeight
    fun_prop
  apply (integrableOn_weight_mul_thetaPairCenterTailSpectrum
    (by decide : 0 < 1) (by decide : 0 < 1) ha0 ha b).mono'
      (hw.stronglyMeasurable.mul (stronglyMeasurable_thetaPairCenterTailSpectrum 1 1 b)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hF := (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs.le b).le
  have hw0 := thetaCuspCenterTailWeight_nonneg ha0 (le_max_left 0 (s - h))
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 hF)]
  exact mul_le_mul_of_nonneg_right
    (thetaCenterTailWeight_mono ha0 (le_max_left _ _) (max_le hs.le (sub_le_self s hh))) hF

/-- An initial center interval supplies strict positivity after the damped midpoint payment. -/
theorem twoAtom_shifted_aperture_pos {a h p c : ℝ} (ha0 : 0 < a)
    (ha : a < 1 / 2) (hh : 0 < h) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : -1 ≤ c) (b : ℝ) :
    0 < ∫ s in Ioi (0 : ℝ),
      thetaCuspCenterTailWeight a s * thetaPairCenterTailSpectrum 1 1 s b +
      (2 * c * p) * (thetaCuspCenterTailWeight a (max 0 (s - h)) * thetaPairCenterTailSpectrum 1 1 s b) +
      p ^ 2 * (thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) * thetaPairCenterTailSpectrum 1 1 s b) := by
  let f : ℝ → ℝ := fun s =>
    thetaCuspCenterTailWeight a s * thetaPairCenterTailSpectrum 1 1 s b +
    (2 * c * p) * (thetaCuspCenterTailWeight a (max 0 (s - h)) * thetaPairCenterTailSpectrum 1 1 s b) +
    p ^ 2 * (thetaCuspCenterTailWeight a (max 0 (s - 2 * h)) * thetaPairCenterTailSpectrum 1 1 s b)
  have hi : IntegrableOn f (Ioi 0) :=
    ((integrableOn_weight_mul_thetaPairCenterTailSpectrum
      (by decide : 0 < 1) (by decide : 0 < 1) ha0.le ha b).add
        ((integrable_shifted_aperture ha0.le ha hh.le b).const_mul (2 * c * p))).add
          ((integrable_shifted_aperture ha0.le ha (by positivity : 0 ≤ 2 * h) b).const_mul (p ^ 2))
  have hnn : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ f s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hF := (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs.le b).le
    have hm := thetaCuspCenterTailWeight_nonneg ha0.le (le_max_left 0 (s - h))
    have hpay := mul_le_mul_of_nonneg_right
      (thetaCenterTailWeight_two_atom_payment ha0.le hh.le hs.le hp hp1) hF
    have hcos := mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (by linarith only [hc] : 0 ≤ c + 1)) hp)
      (mul_nonneg hm hF)
    dsimp only [f]
    nlinarith only [hpay, hcos]
  change 0 < ∫ s in Ioi (0 : ℝ), f s
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hi]
  have hsub : Ioo 0 h ⊆ Function.support f ∩ Ioi (0 : ℝ) := by
    intro s hs
    refine ⟨?_, hs.1⟩
    have hp0 : max 0 (s - h) = 0 := max_eq_left (sub_nonpos.mpr hs.2.le)
    have hp2 : max 0 (s - 2 * h) = 0 := max_eq_left (by linarith only [hs.2, hh])
    have he : f s = thetaCuspCenterTailWeight a s * thetaPairCenterTailSpectrum 1 1 s b := by
      simp only [f, hp0, hp2, thetaCuspCenterTailWeight, mul_zero, Real.sinh_zero,
        Real.cosh_zero, zero_mul, add_zero]
    change f s ≠ 0
    rw [he]
    exact (mul_pos (thetaCuspCenterTailWeight_pos ha0 hs.1)
      (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hs.1.le b)).ne'
  have hvol : 0 < volume (Ioo (0 : ℝ) h) := by
    rw [Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr hh
  exact hvol.trans_le (measure_mono hsub)

/-- The first unequal atom pair is paid by its two diagonal aperture terms at every frequency. -/
theorem twoAtom_apertureSpectrum_pos {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (b : ℝ) :
    0 < thetaPairApertureSpectrum 1 1 a b + thetaPairApertureSpectrum 1 2 a b +
      thetaPairApertureSpectrum 2 1 a b + thetaPairApertureSpectrum 2 2 a b := by
  let h := Real.log 2
  let p := Real.exp (-h / 2)
  let J : ℝ → ℝ := fun d => ∫ s in Ioi (0 : ℝ),
    thetaCuspCenterTailWeight a (max 0 (s - d)) * thetaPairCenterTailSpectrum 1 1 s b
  have hh : 0 < h := Real.log_pos (by norm_num)
  have hp : 0 ≤ p := (Real.exp_pos _).le
  have hp1 : p ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hh])
  have hi0 := integrableOn_weight_mul_thetaPairCenterTailSpectrum
    (by decide : 0 < 1) (by decide : 0 < 1) ha0.le ha b
  have hi1 := integrable_shifted_aperture ha0.le ha hh.le b
  have hi2 := integrable_shifted_aperture ha0.le ha (by positivity : 0 ≤ 2 * h) b
  have hJ0 : J 0 = ∫ s in Ioi (0 : ℝ),
      thetaCuspCenterTailWeight a s * thetaPairCenterTailSpectrum 1 1 s b := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [sub_zero, max_eq_right hs.le]
  have he22 : Real.exp (-(Real.log ((2 : ℝ) * 2)) / 2) = p ^ 2 := by
    rw [Real.log_mul (by norm_num) (by norm_num)]
    dsimp only [p, h]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h11 : thetaPairApertureSpectrum 1 1 a b = J 0 := by
    simpa only [Nat.cast_one, one_mul, Real.log_one, sub_self, mul_zero,
      Real.cos_zero, neg_zero, zero_div, Real.exp_zero, mul_one, one_mul] using
      thetaPairApertureSpectrum_eq_shifted (by decide : 0 < 1) (by decide : 0 < 1) a b
  have h12 : thetaPairApertureSpectrum 1 2 a b = Real.cos (b * h) * p * J h := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, one_mul, Real.log_one, zero_sub,
      mul_neg, Real.cos_neg, h, p, J] using
      thetaPairApertureSpectrum_eq_shifted (by decide : 0 < 1) (by decide : 0 < 2) a b
  have h21 : thetaPairApertureSpectrum 2 1 a b = Real.cos (b * h) * p * J h := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, mul_one, Real.log_one, sub_zero, h, p, J] using
      thetaPairApertureSpectrum_eq_shifted (by decide : 0 < 2) (by decide : 0 < 1) a b
  have h22 : thetaPairApertureSpectrum 2 2 a b = p ^ 2 * J (2 * h) := by
    have ht := thetaPairApertureSpectrum_eq_shifted (by decide : 0 < 2) (by decide : 0 < 2) a b
    simp only [Nat.cast_ofNat] at ht
    rw [he22] at ht
    simpa only [Nat.cast_ofNat, sub_self, mul_zero, Real.cos_zero, one_mul,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      ← two_mul, h, J] using ht
  have hpos := twoAtom_shifted_aperture_pos ha0 ha hh hp hp1 (Real.neg_one_le_cos (b * h)) b
  have he01 := integral_add hi0 (hi1.const_mul (2 * Real.cos (b * h) * p))
  have he012 := integral_add (hi0.add (hi1.const_mul (2 * Real.cos (b * h) * p)))
    (hi2.const_mul (p ^ 2))
  simp only [Pi.add_apply] at he01 he012
  rw [he012, he01, integral_const_mul, integral_const_mul, ← hJ0] at hpos
  rw [h11, h12, h21, h22]
  dsimp only [J] at hpos ⊢
  linarith only [hpos]

#print axioms thetaPairApertureSpectrum_eq_shifted
#print axioms twoAtom_apertureSpectrum_pos

end

end GaloisForLFunctions.CompletedArithmeticForms
