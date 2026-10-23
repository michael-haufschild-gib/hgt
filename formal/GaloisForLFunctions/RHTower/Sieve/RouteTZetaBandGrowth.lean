import GaloisForLFunctions.RHTower.Sieve.RouteTZetaBandParameters

/-!
# Uniform Route-T growth on a unit height band

This is the growth object consumed by Landau discs.  One shell and one cubic truncation, selected
at the centre height, control every ordinate within distance one.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

def routeTBandBlocks (t : ℝ) : ℕ :=
  topExponent (t - 1) - routeTGlobalExponent (routeTBandShell t)

theorem routeTBandBlocks_pos {t : ℝ} (ht : 2 < t)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    1 ≤ routeTBandBlocks t := by
  unfold routeTBandBlocks
  have hdepth := routeTBandCanonicalDepth ht hlarge
  omega

theorem routeTBandTruncation_eq {t : ℝ} (ht : 2 < t)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    routeTGlobalStart (routeTBandShell t) * 2 ^ routeTBandBlocks t =
      2 ^ topExponent (t - 1) := by
  have hdepth := routeTBandCanonicalDepth ht hlarge
  have hsum : routeTGlobalExponent (routeTBandShell t) +
      (topExponent (t - 1) - routeTGlobalExponent (routeTBandShell t)) =
        topExponent (t - 1) := Nat.add_sub_of_le (by omega)
  calc
    routeTGlobalStart (routeTBandShell t) * 2 ^ routeTBandBlocks t =
        2 ^ routeTGlobalExponent (routeTBandShell t) *
          2 ^ (topExponent (t - 1) - routeTGlobalExponent (routeTBandShell t)) := rfl
    _ = 2 ^ (routeTGlobalExponent (routeTBandShell t) +
          (topExponent (t - 1) - routeTGlobalExponent (routeTBandShell t))) :=
      (pow_add _ _ _).symm
    _ = 2 ^ topExponent (t - 1) := congrArg (fun e : ℕ => 2 ^ e) hsum

private theorem routeTBand_two_pow_eq_two_mul_pred {R : ℕ} (hR : 1 ≤ R) :
    2 ^ R = 2 * 2 ^ (R - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, (Nat.sub_add_cancel hR).symm⟩
  rw [pow_succ]
  exact Nat.mul_comm _ _

theorem routeTBandTruncation_low {t : ℝ} (ht : 100000 ≤ t)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t) :
    8 * Real.pi *
      (((routeTGlobalStart (routeTBandShell t) *
          2 ^ (routeTBandBlocks t - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤ t - 1 := by
  let A := routeTGlobalStart (routeTBandShell t)
  let R := routeTBandBlocks t
  let T := topExponent (t - 1)
  have ht2 : 2 < t := by linarith
  have ht8 : 8 * Real.pi ≤ t - 1 := by nlinarith [Real.pi_lt_d2]
  have hA : 1 ≤ A := by
    dsimp only [A, routeTGlobalStart]
    exact Nat.one_le_two_pow
  have hR : 1 ≤ R := by simpa only [R] using routeTBandBlocks_pos ht2 hlarge
  have hpowR : 2 ^ R = 2 * 2 ^ (R - 1) := routeTBand_two_pow_eq_two_mul_pred hR
  have hbase : A * 2 ^ (R - 1) + 1 ≤ A * 2 ^ R := by
    rw [hpowR]
    have hpos : 1 ≤ A * 2 ^ (R - 1) := by
      calc
        1 = 1 * 1 := (Nat.one_mul 1).symm
        _ ≤ A * 2 ^ (R - 1) := Nat.mul_le_mul hA Nat.one_le_two_pow
    calc
      A * 2 ^ (R - 1) + 1 ≤ A * 2 ^ (R - 1) + A * 2 ^ (R - 1) :=
        Nat.add_le_add_left hpos _
      _ = A * (2 * 2 ^ (R - 1)) := by ring
  have htopNat : A * 2 ^ R = 2 ^ T := by
    simpa only [A, R, T] using routeTBandTruncation_eq ht2 hlarge
  have hcast : ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by
    exact_mod_cast hbase.trans_eq htopNat
  have hrpow : ((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
      ((2 ^ T : ℕ) : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by norm_num)
  have htopShape : ((2 ^ T : ℕ) : ℝ) ^ ((1 : ℝ) / 3) =
      (2 : ℝ) ^ ((T : ℝ) / 3) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) T,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply congrArg (fun e : ℝ => (2 : ℝ) ^ e)
    ring
  have htop := topExponent_bound ht8
  rw [htopShape] at hrpow
  calc
    8 * Real.pi * (((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤
        8 * Real.pi * (2 : ℝ) ^ ((T : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ t - 1 := by simpa only [T] using htop

/-- The continuation tails remain bounded when truncation is selected one unit below the centre. -/
theorem routeT_band_truncation_tails_le_nine
    {t y σ : ℝ} (ht : 100000 ≤ t) (hylo : t - 1 ≤ y) (hyhi : y ≤ t + 1)
    (hσhalf : 1 / 2 ≤ σ) (hσone : σ ≤ 1)
    (hthird : 1 - σ ≤ (1 : ℝ) / 3) :
    (((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (1 - σ)) /
        ‖(σ : ℂ) + Complex.I * (y : ℂ) - 1‖ +
      ‖(σ : ℂ) + Complex.I * (y : ℂ)‖ *
        ((((2 ^ topExponent (t - 1) : ℕ) : ℝ) ^ (-σ)) / σ) ≤ 9 := by
  let N : ℝ := ((2 ^ topExponent (t - 1) : ℕ) : ℝ)
  let w : ℂ := (σ : ℂ) + Complex.I * (y : ℂ)
  have ht0 : 0 < t - 1 := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le ht0 hylo
  have hσ0 : 0 < σ := by linarith
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_two_pow
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have ht8 : 8 * Real.pi ≤ t - 1 := by linarith [Real.pi_lt_d2]
  have hNroot : N ^ ((1 : ℝ) / 3) =
      (2 : ℝ) ^ (((topExponent (t - 1) : ℕ) : ℝ) / 3) := by
    dsimp only [N]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hrootle : N ^ ((1 : ℝ) / 3) ≤ (t - 1) / (8 * Real.pi) := by
    rw [hNroot, le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using topExponent_bound ht8
  have hratiole : (t - 1) / (8 * Real.pi) ≤ t - 1 := by
    have hden : (1 : ℝ) ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
    exact (div_le_iff₀ (by positivity)).2
      (by linarith [mul_le_mul_of_nonneg_left hden ht0.le])
  have hnum1 : N ^ (1 - σ) ≤ y := by
    calc
      N ^ (1 - σ) ≤ N ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hthird
      _ ≤ (t - 1) / (8 * Real.pi) := hrootle
      _ ≤ t - 1 := hratiole
      _ ≤ y := hylo
  have hdennorm : y ≤ ‖w - 1‖ := by
    have him := Complex.abs_im_le_norm (w - 1)
    have himw : (w - 1).im = y := by simp [w]
    rw [himw, abs_of_pos hy0] at him
    exact him
  have htail1 : N ^ (1 - σ) / ‖w - 1‖ ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le hy0 hdennorm)]
    exact hnum1.trans hdennorm
  have hcube := cube_le_two_pow_topExponent ht8
  have hcubeN : ((t - 1) / (8 * Real.pi)) ^ (3 : ℕ) ≤ 2 * N := by
    dsimp only [N]
    rw [show 2 * (((2 ^ topExponent (t - 1) : ℕ) : ℝ)) =
        (((2 ^ (topExponent (t - 1) + 1) : ℕ) : ℝ)) by
      push_cast
      rw [pow_succ]
      ring]
    exact hcube
  have hpi2 : Real.pi ^ 2 < 10 := by
    linarith [mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
  have hpi3 : Real.pi ^ 3 < 32 := by
    linarith [mul_lt_mul'' hpi2 Real.pi_lt_d2 (sq_nonneg Real.pi) Real.pi_pos.le]
  have hform : ((t - 1) / (8 * Real.pi)) ^ (3 : ℕ) =
      (t - 1) ^ 3 / (512 * Real.pi ^ 3) := by
    field_simp
    ring
  have hcubelower : (t - 1) ^ 3 / 16384 ≤
      ((t - 1) / (8 * Real.pi)) ^ (3 : ℕ) := by
    rw [hform, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hpi3.le (pow_pos ht0 3).le]
  have hNlower : (t - 1) ^ 3 ≤ 32768 * N := by
    linarith [hcubelower, hcubeN]
  have hsquare : (y + 2) ^ 2 ≤ 2 * (t - 1) ^ 2 := by
    have hy4 : y + 2 ≤ (t - 1) + 4 := by linarith
    have hnonneg : 0 ≤ y + 2 := by linarith
    have hs1 : (y + 2) ^ 2 ≤ ((t - 1) + 4) ^ 2 := pow_le_pow_left₀ hnonneg hy4 2
    linarith [mul_le_mul_of_nonneg_right (by linarith : (10 : ℝ) ≤ t - 1) ht0.le]
  have hmul : 4096 * (t - 1) ^ 2 ≤ (t - 1) ^ 3 := by
    have h4096 : (4096 : ℝ) ≤ t - 1 := by linarith
    have hh := mul_le_mul_of_nonneg_right h4096 (sq_nonneg (t - 1))
    linarith
  have hNbig : (y + 2) ^ 2 ≤ 16 * N := by
    linarith [hsquare, hmul, hNlower]
  have hsqrtmul : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hsqrtnn : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsqrtpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsqrt : y + 2 ≤ 4 * Real.sqrt N := by
    have hquarter : (y + 2) / 4 ≤ Real.sqrt N :=
      (Real.le_sqrt (by positivity) hN0.le).mpr (by
        rw [div_pow]
        norm_num
        linarith [hNbig])
    linarith
  have hmono : N ^ (-σ) ≤ N ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsqrtN : N ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hN0.le]
    exact (one_div _).symm
  have hnum2 : N ^ (-σ) ≤ 1 / Real.sqrt N := by rw [← hsqrtN]; exact hmono
  have hmulnum : N ^ (-σ) * Real.sqrt N ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hnum2 hsqrtnn
    rwa [one_div, inv_mul_cancel₀ hsqrtpos.ne'] at hh
  have hdiv : N ^ (-σ) / σ ≤ 2 / Real.sqrt N := by
    rw [div_le_div_iff₀ hσ0 hsqrtpos]
    exact hmulnum.trans (by linarith [hσhalf])
  have hwnorm : ‖w‖ ≤ y + 2 := by
    have hwre : w.re = σ := by simp [w]
    have hwim : w.im = y := by simp [w]
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ = σ + y := by rw [hwre, hwim, abs_of_pos hσ0, abs_of_pos hy0]
      _ ≤ y + 2 := by linarith
  have htail2 : ‖w‖ * (N ^ (-σ) / σ) ≤ 8 := by
    calc
      ‖w‖ * (N ^ (-σ) / σ) ≤ (y + 2) * (2 / Real.sqrt N) := by
        calc
          ‖w‖ * (N ^ (-σ) / σ) ≤ (y + 2) * (N ^ (-σ) / σ) :=
            mul_le_mul_of_nonneg_right hwnorm (by positivity)
          _ ≤ (y + 2) * (2 / Real.sqrt N) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ 8 := by
        rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hsqrtpos]
        linarith
  dsimp only [N, w] at htail1 htail2 ⊢
  linarith

/-- **Uniform unit-band growth.**  The centre-selected parameters control all ordinates in the
unit band and all real parts from their common Route-T edge to one. -/
theorem norm_riemannZeta_le_routeT_band
    {t y σ : ℝ} (ht : 100000 ≤ t)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t)
    (hylo : t - 1 ≤ y) (hyhi : y ≤ t + 1)
    (hσlo : routeTStripAbscissa (routeTBandShell t) ≤ σ) (hσone : σ < 1) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (y : ℂ))‖ ≤
      11 + 2 * Real.log (routeTGlobalStart (routeTBandShell t) : ℝ) +
        (routeTBandBlocks t : ℝ) * 6912 := by
  let V := routeTBandShell t
  let A := routeTGlobalStart V
  let R := routeTBandBlocks t
  have ht2 : 2 < t := by linarith
  have hy : 1 < y := by linarith
  have hdepth := routeTBandCanonicalDepth ht2 hlarge
  have hσ0 : 0 < σ := lt_of_lt_of_le (routeTStripAbscissa_pos V) (by
    simpa only [V] using hσlo)
  have hdelta : 1 - σ ≤ routeTStripWidth V := by
    have hlo : routeTStripAbscissa V ≤ σ := by simpa only [V] using hσlo
    unfold routeTStripAbscissa at hlo
    linarith
  have hroute : 2 * (1 - σ) ≤
      1 / (5000000000000000 * (V : ℝ) ^ 4) := by
    exact (mul_le_mul_of_nonneg_left hdelta (by norm_num)).trans
      (routeTStripWidth_route_condition (by
        have hh := routeTBandShell_pos t
        have hh' : 1 ≤ routeTBandShell t := (by norm_num : (1 : ℕ) ≤ 2).trans hh
        simpa only [V] using hh'))
  have hderivative : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ (566 : ℕ)) :=
    hdelta.trans (routeTStripWidth_derivative_condition V)
  have hmain := norm_riemannZeta_le_routeT_uniform
    (A := A) (V := V) (R := R) (σ := σ) (t := y)
    (routeTGlobalStart_two_le V) hσ0 hσone hy
    (routeTGlobalStart_size V)
    (by simpa only [A, V] using routeTBandHeight_upper (by linarith : 1 ≤ t) hyhi)
    (routeTGlobalStart_factorial V)
    (by
      have hlow := routeTBandTruncation_low ht hlarge
      simpa only [A, R, V] using hlow.trans hylo)
    hroute hderivative
  have htrunc := routeTBandTruncation_eq ht2 hlarge
  rw [htrunc] at hmain
  have hhead := routeTGlobalHead_le_of_abscissa
    (V := V) (σ := σ) (by simpa only [V] using hσlo) hσone
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (566 : ℕ) := one_le_pow₀ (by norm_num)
  have hden : (3 : ℝ) ≤ 3 * (2 : ℝ) ^ (566 : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [mul_one] using hh
  have hthird : 1 - σ ≤ (1 : ℝ) / 3 :=
    hderivative.trans (one_div_le_one_div_of_le (by norm_num) hden)
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  have htail := routeT_band_truncation_tails_le_nine ht hylo hyhi hσhalf hσone.le hthird
  dsimp only [A, R, V] at hmain hhead ⊢
  linarith

end

end RHTower.Sieve
