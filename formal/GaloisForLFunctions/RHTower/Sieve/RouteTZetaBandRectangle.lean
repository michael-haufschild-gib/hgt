import GaloisForLFunctions.RHTower.Sieve.RouteTZetaBandGrowth
import GaloisForLFunctions.RHTower.Sieve.ZetaWideRectangle

/-!
# Route-T rectangle across the abscissa

The hybrid estimate controls the left half.  On and right of `1`, the harmonic head at the same
cubic truncation controls zeta.  Both halves fit one centre-dependent polylogarithmic majorant.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

def routeTBandGrowthBound (t : ℝ) : ℝ :=
  20 + 2 * Real.log (routeTGlobalStart (routeTBandShell t) : ℝ) +
    (topExponent (t - 1) : ℝ) * 6912

theorem routeTBandGrowthBound_one_le (t : ℝ) : 1 ≤ routeTBandGrowthBound t := by
  have hA : (1 : ℝ) ≤ routeTGlobalStart (routeTBandShell t) := by
    exact_mod_cast Nat.one_le_two_pow
  have hlog : 0 ≤ Real.log (routeTGlobalStart (routeTBandShell t) : ℝ) :=
    Real.log_nonneg hA
  unfold routeTBandGrowthBound
  nlinarith

/-- **The complete centre rectangle.**  The bound is uniform in the ordinate and crosses `Re=1`. -/
theorem norm_riemannZeta_le_routeT_band_rectangle
    {t y σ : ℝ} (ht : 100000 ≤ t)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t)
    (hylo : t - 1 ≤ y) (hyhi : y ≤ t + 1)
    (hσlo : routeTStripAbscissa (routeTBandShell t) ≤ σ) (hσhi : σ ≤ 2) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (y : ℂ))‖ ≤ routeTBandGrowthBound t := by
  rcases lt_or_ge σ 1 with hσone | hσone
  · have hmain := norm_riemannZeta_le_routeT_band ht hlarge hylo hyhi hσlo hσone
    have hblocks : routeTBandBlocks t ≤ topExponent (t - 1) := by
      unfold routeTBandBlocks
      exact Nat.sub_le _ _
    have hblocksR : (routeTBandBlocks t : ℝ) ≤ (topExponent (t - 1) : ℝ) := by
      exact_mod_cast hblocks
    unfold routeTBandGrowthBound
    nlinarith
  · let w : ℂ := (σ : ℂ) + Complex.I * (y : ℂ)
    let N : ℕ := 2 ^ topExponent (t - 1)
    have hy0 : 0 < y := by linarith
    have him : 1 ≤ |w.im| := by
      have hwim : w.im = y := by simp [w]
      rw [hwim, abs_of_pos hy0]
      linarith
    have hN : 1 ≤ N := by
      dsimp only [N]
      exact Nat.one_le_two_pow
    have hwre : w.re = σ := by simp [w]
    have hright := norm_riemannZeta_ge_one_le (w := w) (by simpa only [hwre] using hσone) him hN
    have htail := routeT_band_truncation_tails_le_nine ht hylo hyhi
      (σ := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    have hfirst : 0 ≤
        (((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (1 - (1 : ℝ))) /
          ‖(1 : ℂ) + Complex.I * (y : ℂ) - 1‖ := by positivity
    have htail2 :
        ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ *
          ((((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (-(1 : ℝ))) / (1 : ℝ)) ≤ 9 := by
      calc
        ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ *
            ((((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (-(1 : ℝ))) / (1 : ℝ)) ≤
          (((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (1 - (1 : ℝ))) /
              ‖(1 : ℂ) + Complex.I * (y : ℂ) - 1‖ +
            ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ *
              ((((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (-(1 : ℝ))) / (1 : ℝ)) :=
          le_add_of_nonneg_left hfirst
        _ ≤ 9 := htail
    have hwnorm : ‖w‖ ≤ y + 2 := by
      have hwre : w.re = σ := by simp [w]
      have hwim : w.im = y := by simp [w]
      calc
        ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        _ = σ + y := by
          rw [hwre, hwim, abs_of_pos (by linarith : 0 < σ), abs_of_pos hy0]
        _ ≤ y + 2 := by linarith
    have honeNorm : y ≤ ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ := by
      have himle := Complex.abs_im_le_norm ((1 : ℂ) + Complex.I * (y : ℂ))
      have himval : ((1 : ℂ) + Complex.I * (y : ℂ)).im = y := by simp
      rw [himval, abs_of_pos hy0] at himle
      exact himle
    have hratio : ‖w‖ / (N : ℝ) ≤ 18 := by
      have hN0 : (0 : ℝ) < (N : ℝ) := by positivity
      have hpow : ((N : ℝ) ^ (-(1 : ℝ))) = 1 / (N : ℝ) := by
        rw [Real.rpow_neg hN0.le, Real.rpow_one]
        rw [one_div]
      have hbase : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ / (N : ℝ) ≤ 9 := by
        change ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ *
          (((N : ℝ) ^ (-(1 : ℝ))) / (1 : ℝ)) ≤ 9 at htail2
        rw [hpow, div_one, mul_one_div] at htail2
        exact htail2
      have hcompare : ‖w‖ ≤ 2 * ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ := by
        nlinarith [hwnorm, honeNorm]
      have hh := div_le_div_of_nonneg_right hcompare hN0.le
      calc
        ‖w‖ / (N : ℝ) ≤ (2 * ‖(1 : ℂ) + Complex.I * (y : ℂ)‖) / (N : ℝ) := hh
        _ = 2 * (‖(1 : ℂ) + Complex.I * (y : ℂ)‖ / (N : ℝ)) := by ring
        _ ≤ 2 * 9 := mul_le_mul_of_nonneg_left hbase (by norm_num)
        _ = 18 := by norm_num
    have hlog2 : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlogN : Real.log (N : ℝ) ≤ (topExponent (t - 1) : ℝ) := by
      have hcast : (N : ℝ) = (2 : ℝ) ^ (topExponent (t - 1) : ℕ) := by
        simp only [N, Nat.cast_pow, Nat.cast_ofNat]
      rw [hcast, Real.log_pow]
      have hT0 : (0 : ℝ) ≤ (topExponent (t - 1) : ℝ) := by positivity
      nlinarith
    have hA : (1 : ℝ) ≤ routeTGlobalStart (routeTBandShell t) := by
      exact_mod_cast Nat.one_le_two_pow
    have hlogA : 0 ≤ Real.log (routeTGlobalStart (routeTBandShell t) : ℝ) :=
      Real.log_nonneg hA
    dsimp only [w, N] at hright hratio
    unfold routeTBandGrowthBound
    nlinarith

end

end RHTower.Sieve
