import GaloisForLFunctions.RHTower.SuzukiFinitePoleContourTransport
import GaloisForLFunctions.RHTower.XiHorizontalRatioSelection

namespace RHTower

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped BigOperators Interval

noncomputable section

theorem suzukiCanonicalTheta_horizontal_eq_xi_ratio
    (omega y T : ℝ) :
    suzukiCanonicalTheta omega ((T : ℂ) + (y : ℂ) * Complex.I) =
      xi (((1 / 2 - omega + y : ℝ) : ℂ) - (T : ℂ) * Complex.I) /
        xi (((1 / 2 + omega + y : ℝ) : ℂ) - (T : ℂ) * Complex.I) := by
  rw [suzukiCanonicalTheta]
  have hprod : ((T : ℂ) + (y : ℂ) * Complex.I) * Complex.I =
      (T : ℂ) * Complex.I - (y : ℂ) := by
    calc
      ((T : ℂ) + (y : ℂ) * Complex.I) * Complex.I =
          (T : ℂ) * Complex.I + (y : ℂ) * (Complex.I * Complex.I) := by ring
      _ = (T : ℂ) * Complex.I - (y : ℂ) := by rw [Complex.I_mul_I]; ring
  congr 2 <;> rw [hprod] <;> push_cast <;> ring

theorem exists_suzukiCanonicalTheta_selected_horizontal_bound
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2) :
    ∃ M : ℕ, ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
        1 ≤ T n ∧ ‖suzukiCanonicalTheta omega
          ((T n : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (T n) ^ M ∧
          ‖suzukiCanonicalTheta omega
            ((-(T n) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (T n) ^ M := by
  obtain ⟨M, n0, hsel⟩ := exists_xi_horizontal_ratio_nat_bound
  let base : ℕ → ℝ := fun n => max n0 10 + n
  have hbase0 : ∀ n : ℕ, n0 ≤ base n := by
    intro n
    dsimp [base]
    exact le_trans (le_max_left n0 10) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  let T : ℕ → ℝ := fun n => (hsel (base n) (hbase0 n)).choose
  have hTspec : ∀ n : ℕ, base n ≤ T n ∧ T n ≤ base n + 1 ∧
      ∀ sigma tau : ℝ, -1 ≤ sigma → sigma ≤ 2 → -1 ≤ tau → tau ≤ 2 →
        ‖xi ((sigma : ℂ) + (T n : ℂ) * I)‖ ≤
            (T n) ^ M * ‖xi ((tau : ℂ) + (T n : ℂ) * I)‖ ∧
          ‖xi ((sigma : ℂ) - (T n : ℂ) * I)‖ ≤
            (T n) ^ M * ‖xi ((tau : ℂ) - (T n : ℂ) * I)‖ := by
    intro n
    exact (hsel (base n) (hbase0 n)).choose_spec
  have hbaseTop : Tendsto base atTop atTop := by
    simpa only [base] using
      (Filter.tendsto_atTop_add_const_left atTop (max n0 10) tendsto_natCast_atTop_atTop)
  have hTtop : Tendsto T atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [(tendsto_atTop.1 hbaseTop b)] with n hn
    exact le_trans hn (hTspec n).1
  refine ⟨M, T, hTtop, ?_⟩
  intro n y hy0 hy1
  have hT1 : 1 ≤ T n := by
    have hbase10 : 10 ≤ base n := by
      dsimp [base]
      exact le_trans (le_max_right n0 10) (le_add_of_nonneg_right (Nat.cast_nonneg n))
    exact le_trans (by norm_num) (le_trans hbase10 (hTspec n).1)
  let sigma : ℝ := 1 / 2 - omega + y
  let tau : ℝ := 1 / 2 + omega + y
  have hsigma1 : -1 ≤ sigma := by dsimp [sigma]; linarith
  have hsigma2 : sigma ≤ 2 := by dsimp [sigma]; linarith
  have htau1 : -1 ≤ tau := by dsimp [tau]; linarith
  have htau2 : tau ≤ 2 := by dsimp [tau]; linarith
  have hratio := (hTspec n).2.2 sigma tau hsigma1 hsigma2 htau1 htau2
  refine ⟨hT1, ?_, ?_⟩
  rw [suzukiCanonicalTheta_horizontal_eq_xi_ratio]
  rw [norm_div]
  by_cases hden : ‖xi ((tau : ℂ) - (T n : ℂ) * I)‖ = 0
  · rw [hden, div_zero]
    positivity
  · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hden))]
    simpa only [sigma, tau] using hratio.2
  have htheta : suzukiCanonicalTheta omega
      (-((T n : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        xi ((sigma : ℂ) + (T n : ℂ) * Complex.I) /
          xi ((tau : ℂ) + (T n : ℂ) * Complex.I) := by
    simpa only [ofReal_neg, neg_mul, neg_neg, sub_neg_eq_add, sigma, tau] using
      (suzukiCanonicalTheta_horizontal_eq_xi_ratio omega y (-(T n)))
  rw [htheta]
  rw [norm_div]
  by_cases hden : ‖xi ((tau : ℂ) + (T n : ℂ) * I)‖ = 0
  · rw [hden, div_zero]
    positivity
  · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hden))]
    simpa only [sigma, tau] using hratio.1

/-- For `0 < omega < 1/2`, selected Xi-good vertical sides kill Suzuki's exact test integrand
without any global pointwise inverse-Xi bound. -/
theorem exists_suzukiCanonicalHankelContour_vertical_tendsto_zero
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      Tendsto (fun n => VIntegral
        (suzukiCanonicalHankelContourIntegrand omega g r) (T n) 0 1)
        atTop (nhds 0) ∧
      Tendsto (fun n => VIntegral
        (suzukiCanonicalHankelContourIntegrand omega g r) (-(T n)) 0 1)
        atTop (nhds 0) := by
  obtain ⟨M, T, hTtop, htheta⟩ :=
    exists_suzukiCanonicalTheta_selected_horizontal_bound homega0 homegaHalf
  obtain ⟨T0, C, hC, hMellin⟩ :=
    hasStripRapidDecrease_deningerMeyerStrongLogMellin g 0 1 (M + 2)
  let D : ℝ := C * Real.exp |r|
  have hD : 0 ≤ D := mul_nonneg hC (Real.exp_pos _).le
  have hgo : Tendsto (fun n => 1 + T n) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop 1 hTtop
  have hdecay : Tendsto (fun n => D * (1 + T n) ^ (-(2 : ℝ))) atTop (nhds 0) := by
    have hinv := (tendsto_rpow_neg_atTop (y := (2 : ℝ)) (by norm_num)).comp hgo
    simpa only [Function.comp_apply, mul_zero] using hinv.const_mul D
  have hpowCollapse : ∀ n : ℕ,
      (1 + T n) ^ M * (C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ))) * Real.exp |r| =
        D * (1 + T n) ^ (-(2 : ℝ)) := by
    intro n
    have hbase : 0 < 1 + T n := by linarith [(htheta n 0 (by norm_num) (by norm_num)).1]
    have hrpow :
        (1 + T n) ^ (M : ℝ) * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ)) =
          (1 + T n) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hbase]
      congr 1
      push_cast
      ring
    rw [← Real.rpow_natCast, ← hrpow]
    dsimp [D]
    ring
  have hrightBound : ∀ᶠ n : ℕ in atTop,
      ‖VIntegral (suzukiCanonicalHankelContourIntegrand omega g r) (T n) 0 1‖ ≤
        D * (1 + T n) ^ (-(2 : ℝ)) := by
    filter_upwards [hTtop.eventually_ge_atTop T0] with n hn
    have hT1 := (htheta n 0 (by norm_num) (by norm_num)).1
    have hTnonneg : 0 ≤ T n := le_trans (by norm_num) hT1
    have hbase : 0 < 1 + T n := by linarith
    have hpoint : ∀ y ∈ Set.uIoc (0 : ℝ) 1,
        ‖suzukiCanonicalHankelContourIntegrand omega g r
          ((T n : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          D * (1 + T n) ^ (-(2 : ℝ)) := by
      intro y hy
      have hyI : y ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact le_of_lt (by simpa using hy.1)
        · simpa using hy.2
      have hthetaY := (htheta n y hyI.1 hyI.2).2.1
      have hheight : T0 ≤
          |(((y : ℂ) - (T n : ℂ) * Complex.I).im)| := by
        simpa [abs_of_nonneg hTnonneg] using hn
      have hM :
          ‖deningerMeyerStrongLogMellin g
              ((y : ℂ) - (T n : ℂ) * Complex.I)‖ ≤
            C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ)) := by
        simpa [abs_of_nonneg hTnonneg] using hMellin
          ((y : ℂ) - (T n : ℂ) * Complex.I)
          (by simp; exact hyI.1) (by simp; exact hyI.2)
          hheight
      have hrot : -Complex.I * ((T n : ℂ) + (y : ℂ) * Complex.I) =
          (y : ℂ) - (T n : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      rw [suzukiCanonicalHankelContourIntegrand, norm_mul, norm_mul, hrot]
      have hexp : ‖Complex.exp
          (((y : ℂ) - (T n : ℂ) * Complex.I) * (r : ℂ))‖ ≤
          Real.exp |r| := by
        rw [Complex.norm_exp]
        have hre :
            (((y : ℂ) - (T n : ℂ) * Complex.I) * (r : ℂ)).re = y * r := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        exact Real.exp_le_exp.mpr (by
          calc y * r ≤ |y * r| := le_abs_self _
            _ = y * |r| := by rw [abs_mul, abs_of_nonneg hyI.1]
            _ ≤ |r| := by
              simpa using mul_le_mul_of_nonneg_right hyI.2 (abs_nonneg r))
      have hTpow : (T n) ^ M ≤ (1 + T n) ^ M := by
        exact pow_le_pow_left₀ (by linarith) (by linarith) M
      calc
        ‖suzukiCanonicalTheta omega ((T n : ℂ) + (y : ℂ) * Complex.I)‖ *
              ‖deningerMeyerStrongLogMellin g ((y : ℂ) - (T n : ℂ) * Complex.I)‖ *
              ‖Complex.exp (((y : ℂ) - (T n : ℂ) * Complex.I) * (r : ℂ))‖
            ≤ (T n) ^ M * (C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ))) * Real.exp |r| := by
              gcongr
        _ ≤ (1 + T n) ^ M * (C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ))) *
              Real.exp |r| := by
              gcongr
        _ = D * (1 + T n) ^ (-(2 : ℝ)) := hpowCollapse n
    rw [VIntegral, norm_smul, norm_I, one_mul]
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hleftBound : ∀ᶠ n : ℕ in atTop,
      ‖VIntegral (suzukiCanonicalHankelContourIntegrand omega g r) (-(T n)) 0 1‖ ≤
        D * (1 + T n) ^ (-(2 : ℝ)) := by
    filter_upwards [hTtop.eventually_ge_atTop T0] with n hn
    have hT1 := (htheta n 0 (by norm_num) (by norm_num)).1
    have hTnonneg : 0 ≤ T n := le_trans (by norm_num) hT1
    have hbase : 0 < 1 + T n := by linarith
    have hpoint : ∀ y ∈ Set.uIoc (0 : ℝ) 1,
        ‖suzukiCanonicalHankelContourIntegrand omega g r
          (((-(T n) : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          D * (1 + T n) ^ (-(2 : ℝ)) := by
      intro y hy
      have hyI : y ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact le_of_lt (by simpa using hy.1)
        · simpa using hy.2
      have hthetaY := (htheta n y hyI.1 hyI.2).2.2
      have hheight : T0 ≤
          |(((y : ℂ) + (T n : ℂ) * Complex.I).im)| := by
        simpa [abs_of_nonneg hTnonneg] using hn
      have hM :
          ‖deningerMeyerStrongLogMellin g
              ((y : ℂ) + (T n : ℂ) * Complex.I)‖ ≤
            C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ)) := by
        simpa [abs_of_nonneg hTnonneg] using hMellin
          ((y : ℂ) + (T n : ℂ) * Complex.I)
          (by simp; exact hyI.1) (by simp; exact hyI.2)
          hheight
      have hrot : -Complex.I * ((-(T n) : ℂ) + (y : ℂ) * Complex.I) =
          (y : ℂ) + (T n : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      have hzneg : (((-(T n) : ℝ) : ℂ)) = -(T n : ℂ) := by simp
      rw [suzukiCanonicalHankelContourIntegrand, norm_mul, norm_mul, hzneg, hrot]
      have hexp : ‖Complex.exp
          (((y : ℂ) + (T n : ℂ) * Complex.I) * (r : ℂ))‖ ≤
          Real.exp |r| := by
        rw [Complex.norm_exp]
        have hre :
            (((y : ℂ) + (T n : ℂ) * Complex.I) * (r : ℂ)).re = y * r := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        exact Real.exp_le_exp.mpr (by
          calc y * r ≤ |y * r| := le_abs_self _
            _ = y * |r| := by rw [abs_mul, abs_of_nonneg hyI.1]
            _ ≤ |r| := by
              simpa using mul_le_mul_of_nonneg_right hyI.2 (abs_nonneg r))
      have hTpow : (T n) ^ M ≤ (1 + T n) ^ M := by
        exact pow_le_pow_left₀ (by linarith) (by linarith) M
      calc
        ‖suzukiCanonicalTheta omega ((-(T n) : ℂ) + (y : ℂ) * Complex.I)‖ *
              ‖deningerMeyerStrongLogMellin g ((y : ℂ) + (T n : ℂ) * Complex.I)‖ *
              ‖Complex.exp (((y : ℂ) + (T n : ℂ) * Complex.I) * (r : ℂ))‖
            ≤ (T n) ^ M * (C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ))) * Real.exp |r| := by
              gcongr
        _ ≤ (1 + T n) ^ M * (C * (1 + T n) ^ (-((M + 2 : ℕ) : ℝ))) *
              Real.exp |r| := by
              gcongr
        _ = D * (1 + T n) ^ (-(2 : ℝ)) := hpowCollapse n
    rw [VIntegral, norm_smul, norm_I, one_mul]
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  refine ⟨T, hTtop, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
      (Eventually.of_forall fun n => norm_nonneg _) hrightBound
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
      (Eventually.of_forall fun n => norm_nonneg _) hleftBound

end

end RHTower
