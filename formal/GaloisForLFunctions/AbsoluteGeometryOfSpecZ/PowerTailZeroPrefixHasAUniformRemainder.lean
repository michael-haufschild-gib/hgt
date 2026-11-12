import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta
import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripTraceCanBeIntegrated

/-!
# A uniform power-prefix remainder after division by the zero

The complex-prefix rate grows linearly in the ordinate on a fixed right
strip. Dividing by the shifted zero cancels that growth. Consequently a
finite zero convolution costs its number of zeros, without an extra
ordinate factor.
-/

noncomputable section

open Complex
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry TransHorizonIncidenceMechanics

/-- The finite power-prefix error divided by the shifted zero. -/
def powerTailZeroPrefixRemainder (a : ℝ) (q : XiZeroCopy) (N : ℕ) : ℂ :=
  (cpowPartialSum ((q.1 : ℂ) + (a : ℂ)) N -
    ((N : ℝ) : ℂ) ^ (1 - ((q.1 : ℂ) + (a : ℂ))) /
      (1 - ((q.1 : ℂ) + (a : ℂ))) - riemannZeta ((q.1 : ℂ) + (a : ℂ))) /
    ((q.1 : ℂ) - (a : ℂ))

/-- On the closed strip from one half to one, the prefix rate is bounded
by a constant times the ordinate of the actual zero. -/
theorem partialSumRate_zero_add_le {a : ℝ} (q : XiZeroCopy)
    (hlo : 1 / 2 ≤ (q.1 : ℂ).re + a) (hhi : (q.1 : ℂ).re + a ≤ 1) :
    partialSumRate ((q.1 : ℂ) + (a : ℂ)) ≤ 14 * |xiCopyOrdinate q| := by
  let w : ℂ := (q.1 : ℂ) + (a : ℂ)
  have hwre : w.re = (q.1 : ℂ).re + a := by simp only [w, add_re, ofReal_re]
  have hwim : |w.im| = |xiCopyOrdinate q| := by
    simp only [w, add_im, ofReal_im, add_zero, xiCopyOrdinate]
  have hr : 0 < w.re := by rw [hwre]; linarith only [hlo]
  have hγ1 : 1 ≤ |xiCopyOrdinate q| := by
    have hh := four_lt_abs_xiCopyOrdinate q
    linarith only [hh]
  have hnorm : ‖w‖ ≤ 2 * |xiCopyOrdinate q| := by
    have hcoord : ‖w‖ ≤ |w.re| + |w.im| := by
      have hsq : ‖w‖ ^ 2 ≤ (|w.re| + |w.im|) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith only [abs_nonneg w.re, abs_nonneg w.im, sq_abs w.re, sq_abs w.im]
      nlinarith only [hsq, norm_nonneg w, abs_nonneg w.re, abs_nonneg w.im]
    rw [abs_of_pos hr, hwre, hwim] at hcoord
    linarith only [hcoord, hhi, hγ1]
  have hinv : 1 / w.re ≤ 2 := (div_le_iff₀ hr).mpr (by rw [hwre]; linarith only [hlo])
  have hcoef : ‖w‖ * (1 + 1 / w.re) + 1 ≤ 7 * |xiCopyOrdinate q| := by
    have hh := mul_le_mul hnorm (by linarith only [hinv] : 1 + 1 / w.re ≤ 3)
      (by positivity : 0 ≤ 1 + 1 / w.re) (by positivity : 0 ≤ 2 * |xiCopyOrdinate q|)
    linarith only [hh, hγ1]
  have hpow : (2 : ℝ) ^ w.re ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by rwa [hwre] : w.re ≤ 1)
  change (‖w‖ * (1 + 1 / w.re) + 1) * (2 : ℝ) ^ w.re ≤ _
  calc
    _ ≤ (7 * |xiCopyOrdinate q|) * 2 :=
      mul_le_mul hcoef hpow (by positivity) (by positivity)
    _ = _ := by ring

/-- The exact finite power prefix has an error uniform over all actual
zeros in the retained strip, after dividing by its shifted denominator. -/
theorem norm_powerTailZeroPrefix_remainder_div_le {a : ℝ} (q : XiZeroCopy)
    (hlo : 1 / 2 ≤ (q.1 : ℂ).re + a) (hhi : (q.1 : ℂ).re + a ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖powerTailZeroPrefixRemainder a q N‖ ≤
      14 * (N : ℝ) ^ (-((q.1 : ℂ).re + a)) := by
  have hr : 0 < ((q.1 : ℂ) + (a : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hlo]
  have hne : (q.1 : ℂ) + (a : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.one_im] at hh
    have hγ := four_lt_abs_xiCopyOrdinate q
    simp only [xiCopyOrdinate, hh, abs_zero] at hγ
    linarith only [hγ]
  have hb := norm_cpowPartialSum_sub_le hr hne hN (x := (N : ℝ)) le_rfl (by linarith)
  simp only [Complex.add_re, Complex.ofReal_re] at hb
  have hd : 0 < ‖(q.1 : ℂ) - (a : ℂ)‖ :=
    norm_pos_iff.mpr (zero_sub_real_ne_zero q a)
  have hrate : partialSumRate ((q.1 : ℂ) + (a : ℂ)) ≤
      14 * ‖(q.1 : ℂ) - (a : ℂ)‖ :=
    (partialSumRate_zero_add_le q hlo hhi).trans
      (mul_le_mul_of_nonneg_left (abs_ordinate_le_norm_zero_sub_real q a) (by norm_num))
  rw [powerTailZeroPrefixRemainder, norm_div, div_le_iff₀ hd]
  calc
    _ ≤ partialSumRate ((q.1 : ℂ) + (a : ℂ)) *
        (N : ℝ) ^ (-((q.1 : ℂ).re + a)) := hb
    _ ≤ (14 * ‖(q.1 : ℂ) - (a : ℂ)‖) * (N : ℝ) ^ (-((q.1 : ℂ).re + a)) :=
      mul_le_mul_of_nonneg_right hrate (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

/-- Boundary normalization gives the same reciprocal-cutoff error for
every retained zero, independently of its ordinate and boundary deficit. -/
theorem norm_normalized_powerTailZeroPrefixRemainder_le {a : ℝ} (q : XiZeroCopy)
    (hlo : 1 / 2 ≤ (q.1 : ℂ).re + a) (hhi : (q.1 : ℂ).re + a ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
      powerTailZeroPrefixRemainder a q N‖ ≤ 14 / (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hNp, Complex.sub_re, Complex.ofReal_re]
  calc
    _ ≤ (N : ℝ) ^ ((q.1 : ℂ).re - (1 - a)) *
        (14 * (N : ℝ) ^ (-((q.1 : ℂ).re + a))) :=
      mul_le_mul_of_nonneg_left (norm_powerTailZeroPrefix_remainder_div_le q hlo hhi hN)
        (Real.rpow_nonneg hNp.le _)
    _ = 14 * (N : ℝ) ^ (-(1 : ℝ)) := by
      calc
        _ = 14 * ((N : ℝ) ^ ((q.1 : ℂ).re - (1 - a)) *
            (N : ℝ) ^ (-((q.1 : ℂ).re + a))) := by ring
        _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring
    _ = _ := by rw [Real.rpow_neg hNp.le, Real.rpow_one, div_eq_mul_inv]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
