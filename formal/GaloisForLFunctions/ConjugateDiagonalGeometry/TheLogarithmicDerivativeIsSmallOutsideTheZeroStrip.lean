import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.CCM.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound
import GaloisForLFunctions.HTGeometry.ThreeCircles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The logarithmic derivative outside the zero strip

The zero-free half-plane to the right of seven eighths gives a logarithmic bound
for `ζ'/ζ`. Three circles interpolate this bound with the bounded Dirichlet series
on a smaller disk lying to the right of one. Every fixed line between seven
eighths and one therefore has `ζ'/ζ = o(log |t|)`.
-/

noncomputable section

open Complex Metric Filter Topology

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open RHTower
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

private theorem xi_halfPlane_three_eighths : XiZeroHalfPlaneBound (3 / 8) := by
  intro z hz
  have hζ := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hz).1
  have hle : z.re ≤ 7 / 8 := le_of_not_gt fun h =>
    riemannZeta_ne_zero_of_seven_eighths_lt_re h hζ
  linarith only [hle]

private theorem norm_logDeriv_zeta_right_le {z : ℂ}
    (hlo : (17 : ℝ) / 16 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖logDeriv riemannZeta z‖ ≤ 2048 := by
  have hz : 1 < z.re := by linarith only [hlo]
  have h := norm_zeta_logDeriv_le_line hz hhi
  have hd : (1 : ℝ) / 16 ≤ z.re - 1 := by linarith only [hlo]
  have hs : (1 : ℝ) / 256 ≤ (z.re - 1) ^ 2 := by
    nlinarith only [sq_nonneg (z.re - 1 - 1 / 16), hd]
  have hden : 0 < (z.re - 1) ^ 2 := by linarith only [hs]
  rw [logDeriv_apply]
  exact h.trans ((div_le_iff₀ hden).mpr (by nlinarith only [hs]))

/-- A fixed disk strictly inside the zero-free half-plane has logarithmic growth. -/
private theorem exists_logDeriv_disk_log_bound {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 8 ≤ |t| →
      ∀ z : ℂ, ‖z - ((9 / 8 : ℂ) + (t : ℂ) * I)‖ ≤ r →
        ‖logDeriv riemannZeta z‖ ≤ K * Real.log |t| := by
  obtain ⟨C, hC, hb⟩ :=
    Sieve.exists_logDeriv_zeta_bound_of_xiZeroHalfPlaneBound
      (by norm_num : (0 : ℝ) ≤ 3 / 8) xi_halfPlane_three_eighths
  refine ⟨2 * C / (1 / 4 - r) + 2048, by positivity, ?_⟩
  intro t ht z hz
  have hδ : 0 < (1 : ℝ) / 4 - r := by linarith only [hr]
  have hcre : ((9 / 8 : ℂ) + (t : ℂ) * I).re = 9 / 8 := by norm_num
  have hcim : ((9 / 8 : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hre := Complex.abs_re_le_norm (z - ((9 / 8 : ℂ) + (t : ℂ) * I))
  have him := Complex.abs_im_le_norm (z - ((9 / 8 : ℂ) + (t : ℂ) * I))
  rw [Complex.sub_re, hcre] at hre
  rw [Complex.sub_im, hcim] at him
  have hrelo : 9 / 8 - r ≤ z.re := by linarith only [(abs_le.mp (hre.trans hz)).1]
  have hrehi : z.re ≤ 9 / 8 + r := by linarith only [(abs_le.mp (hre.trans hz)).2]
  have himdiff : |z.im - t| ≤ r := him.trans hz
  have htlo : |t| - r ≤ |z.im| := by
    have h := abs_sub_abs_le_abs_sub t z.im
    rw [abs_sub_comm t z.im] at h
    linarith only [h, himdiff]
  have hthi : |z.im| ≤ |t| + r := by
    have h := abs_sub_abs_le_abs_sub z.im t
    linarith only [h, himdiff]
  have ht0 : 0 < |t| := by linarith only [ht]
  have hz0 : 0 < |z.im| := by linarith only [htlo, ht, hr]
  have htlog : 1 ≤ Real.log |t| := by
    have he : Real.exp 1 ≤ |t| := by
      have he := Real.exp_one_lt_d9
      linarith only [he, ht]
    have h := Real.log_le_log (Real.exp_pos 1) he
    simpa only [Real.log_exp] using h
  have hzlog : Real.log |z.im| ≤ 2 * Real.log |t| := by
    have h := Real.log_le_log hz0 (show |z.im| ≤ 2 * |t| by
      linarith only [hthi, hr, ht])
    rw [Real.log_mul (by norm_num) ht0.ne'] at h
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [this]
    linarith only [h, h2, htlog]
  rcases le_or_gt z.re (9 / 8) with hzright | hzright
  · have hgap : 0 < z.re - (1 / 2 + 3 / 8) := by
      linarith only [hrelo, hr]
    have hbz := hb z.re z.im (by linarith only [htlo, ht, hr])
      (by linarith only [hgap]) hzright
    rw [Complex.re_add_im] at hbz
    have hq : C * Real.log |z.im| / (z.re - (1 / 2 + 3 / 8)) ≤
        (2 * C / (1 / 4 - r)) * Real.log |t| := by
      have hnum : C * Real.log |z.im| ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hzlog hC.le
      calc C * Real.log |z.im| / (z.re - (1 / 2 + 3 / 8))
          ≤ C * (2 * Real.log |t|) / (1 / 4 - r) :=
            div_le_div₀ (by positivity) hnum hδ (by linarith only [hrelo])
        _ = _ := by ring
    exact (hbz.trans hq).trans (by
      have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2048) (by linarith : 0 ≤ Real.log |t|)
      nlinarith only [this])
  · have hbz := norm_logDeriv_zeta_right_le
      (by linarith only [hzright]) (by linarith only [hrehi, hr])
    have hK0 : 0 ≤ 2 * C / (1 / 4 - r) := by positivity
    have hx := mul_nonneg hK0 (show 0 ≤ Real.log |t| by linarith only [htlog])
    nlinarith only [hbz, htlog, hx]

end GaloisForLFunctions.ConjugateDiagonalGeometry
