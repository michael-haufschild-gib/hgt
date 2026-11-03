import GaloisForLFunctions.WindowTowerOfSpecZ.TheUniformGammaReserveHasANegativeDirection
import GaloisForLFunctions.WindowTowerOfSpecZ.TheUniformGammaReserveCannotPayTheFirstFold
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderRetainsHigherLags
import GaloisForLFunctions.WindowTowerOfSpecZ.ThePrimitiveVarianceRetainsTheOddMoment
import GaloisForLFunctions.ArithmeticIncidencePositivity.CurvedFoldOddWindowPositivity

/-!
# Higher Gamma terms repair the quadratic cutoff

The third and fourth lag energies of the quadratic endpoint cutoff are exact
polynomial integrals. The stronger exterior reserve and these local terms
supply a positive lower form on the same profile whose mass-only reserve fails.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open SpacingScaleHarmonicAnalysis

private def quadraticCutoffCorrUpper : ℝ :=
  let l : ℝ := 693147180/1000000000
  let h : ℝ := 693147181/1000000000
  128/3465-256/315*l^2+128/21*h^4-128/15*l^5+512/105*h^7-128/63*l^9+256/693*h^11

private theorem quadraticCutoffCorr_le_upper :
    autocorr quadraticCutoffWindow (Real.log 2) ≤ quadraticCutoffCorrUpper := by
  have hl : (693147180/1000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hu : Real.log 2 ≤ (693147181/1000000000 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have lo (n : ℕ) := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 693147180/1000000000) hl n
  have hi (n : ℕ) := pow_le_pow_left₀ h0 hu n
  rw [quadraticCutoffWindow_autocorr h0 (by linarith only [hu])]
  unfold quadraticCutoffCorrUpper quadraticCutoffCorrPoly
  dsimp only
  linarith only [lo 2, hi 4, lo 5, hi 7, lo 9, hi 11]

private theorem quadraticCutoff_prime_gain_ge :
    -2*(49/100)*quadraticCutoffCorrUpper ≤
      -(2*(Real.log 2/Real.sqrt 2)*autocorr quadraticCutoffWindow (Real.log 2)) := by
  have hs : Real.sqrt 2 ≤ 14143/10000 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hw : (49/100 : ℝ) ≤ Real.log 2/Real.sqrt 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith only [hs, Real.log_two_gt_d9]
  have hc0 : quadraticCutoffCorrUpper ≤ 0 := by norm_num [quadraticCutoffCorrUpper]
  have h1 := mul_le_mul_of_nonpos_left quadraticCutoffCorr_le_upper
    (show -(2*(Real.log 2/Real.sqrt 2)) ≤ 0 by linarith only [hw])
  have h2 := mul_le_mul_of_nonneg_right hw (neg_nonneg.mpr hc0)
  nlinarith only [h1, h2]

private theorem quadraticCutoff_pole_cost_le :
    sinhPairing quadraticCutoffWindow ^ 2 / 2 ≤
      (97/192)*(4/105)^2+(97/483840)*(128/3465) := by
  have hs : tsupport quadraticCutoffWindow ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hi
    exact hx (quadraticCutoffWindow_outside hi)
  have h := unit_sinhPairing_square_le_position continuous_quadraticCutoffWindow hs
  simpa only [quadraticCutoffWindow_position_moment, quadraticCutoffWindow_mass] using h

/-- Every polynomial lag moment of the quadratic cutoff has an exact rational expression. -/
theorem quadraticCutoffWindow_jump_moment (k : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1,
      t^k*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t)) =
      256/315/((k : ℝ)+3)-128/21/((k : ℝ)+5)+128/15/((k : ℝ)+6)-
        512/105/((k : ℝ)+8)+128/63/((k : ℝ)+10)-256/693/((k : ℝ)+12) := by
  rw [quadraticCutoffWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1, t^k*(128/3465-autocorr quadraticCutoffWindow t)) =
      ∫ t in (0 : ℝ)..1,
        (256/315*t^(k+2)-128/21*t^(k+4)+128/15*t^(k+5)-512/105*t^(k+7)+
          128/63*t^(k+9)-256/693*t^(k+11)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [quadraticCutoffWindow_autocorr ht.1.le ht.2]
    unfold quadraticCutoffCorrPoly
    simp only [pow_add]
    ring
  rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num [pow_add, Nat.cast_add, Nat.cast_ofNat] <;> ring

theorem quadraticCutoffWindow_jump_third_moment :
    (∫ t in Ioc (0 : ℝ) 1,
      t^3*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t)) =
      256/(315*6)-128/(21*8)+128/(15*9)-512/(105*11)+128/(63*13)-256/(693*15) := by
  convert quadraticCutoffWindow_jump_moment 3 using 1 <;> norm_num

theorem quadraticCutoffWindow_jump_fourth_moment :
    (∫ t in Ioc (0 : ℝ) 1,
      t^4*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t)) =
      256/(315*7)-128/(21*9)+128/(15*10)-512/(105*12)+128/(63*14)-256/(693*16) := by
  convert quadraticCutoffWindow_jump_moment 4 using 1 <;> norm_num

private theorem quadraticCutoff_higher_reserve_certificate :
    0 < (128/315-32/21+128/75-512/735+128/567-256/7623 : ℝ) -
      (577216/1000000+11448/10000+693147181/1000000000)*(128/3465) -
      (64/315-64/63+128/105-512/945+128/693-256/9009)/24 -
      (4/105)^2/16 - ((97/192)*(4/105)^2+(97/483840)*(128/3465)) -
      2*(49/100)*quadraticCutoffCorrUpper+(193/10000)*(128/3465) +
      (256/(315*6)-128/(21*8)+128/(15*9)-512/(105*11)+128/(63*13)-256/(693*15))/960 +
      (256/(315*7)-128/(21*9)+128/(15*10)-512/(105*12)+128/(63*14)-256/(693*16))/192 := by
  norm_num [quadraticCutoffCorrUpper]

/-- The stronger mass reserve and two higher lag energies pay the quadratic cutoff. -/
theorem retainedOddGamma_quadraticCutoff_add_higher_reserve_pos :
    0 < retainedOddGammaLowerForm quadraticCutoffWindow +
      (193/10000)*(∫ x, quadraticCutoffWindow x^2) +
      (∫ t in Ioc (0 : ℝ) 1, t^3*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t))/960 +
      (∫ t in Ioc (0 : ℝ) 1, t^4*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t))/192 := by
  have hg : Real.eulerMascheroniConstant+Real.log Real.pi+Real.log 2 ≤
      577216/1000000+11448/10000+693147181/1000000000 := by
    linarith only [ArithmeticIncidencePositivity.log_pi_le_11448, Real.log_two_lt_d9,
      _root_.RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]
  rw [quadraticCutoffWindow_jump_third_moment, quadraticCutoffWindow_jump_fourth_moment,
    retainedOddGammaLowerForm, quadraticCutoffWindow_logarithmic_integral,
    quadraticCutoffWindow_jump_first_moment, quadraticCutoffWindow_mass,
    quadraticCutoffWindow_position_moment]
  linarith only [hg, quadraticCutoff_prime_gain_ge, quadraticCutoff_pole_cost_le,
    quadraticCutoff_higher_reserve_certificate]

private theorem quadraticCutoff_smooth_compact (n : ℕ) :
    HasCompactSupport (unitSmoothQuadraticCutoff n) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => unitSmoothQuadraticCutoff_outside n hx)

private theorem quadraticCutoff_smooth_mass_tendsto :
    Tendsto (fun n => ∫ x, unitSmoothQuadraticCutoff n x^2) atTop
      (𝓝 (∫ x, quadraticCutoffWindow x^2)) :=
  unitWindow_square_mass_tendsto unitSmoothQuadraticCutoff_contDiff
    (fun n _ hx => unitSmoothQuadraticCutoff_outside n hx)
    unitSmoothQuadraticCutoff_abs_le_one unitSmoothQuadraticCutoff_lipschitz
    unitSmoothQuadraticCutoff_tendsto

private theorem quadraticCutoff_smooth_retained_tendsto :
    Tendsto (fun n => retainedOddGammaLowerForm (unitSmoothQuadraticCutoff n)) atTop
      (𝓝 (retainedOddGammaLowerForm quadraticCutoffWindow)) :=
  retainedOddGammaLowerForm_tendsto_of_unit_window unitSmoothQuadraticCutoff_contDiff
    (fun n _ hx => unitSmoothQuadraticCutoff_outside n hx)
    unitSmoothQuadraticCutoff_abs_le_one unitSmoothQuadraticCutoff_lipschitz
    unitSmoothQuadraticCutoff_tendsto

private theorem quadraticCutoff_smooth_integrand_bound (n : ℕ) (t x : ℝ) :
    ‖unitSmoothQuadraticCutoff n x * unitSmoothQuadraticCutoff n (x+t)‖ ≤
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
  · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul (unitSmoothQuadraticCutoff_abs_le_one n x)
      (unitSmoothQuadraticCutoff_abs_le_one n (x+t)) (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)
  · rw [indicator_of_notMem hx, unitSmoothQuadraticCutoff_outside n hx, zero_mul, norm_zero]

private theorem quadraticCutoff_smooth_autocorr_tendsto (t : ℝ) :
    Tendsto (fun n => autocorr (unitSmoothQuadraticCutoff n) t) atTop
      (𝓝 (autocorr quadraticCutoffWindow t)) := by
  have hBi : Integrable ((Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ))) :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  change Tendsto (fun n => ∫ x, unitSmoothQuadraticCutoff n x * unitSmoothQuadraticCutoff n (x+t))
    atTop (𝓝 (∫ x, quadraticCutoffWindow x * quadraticCutoffWindow (x+t)))
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hBi (fun n => ?_) ?_
  · exact ((unitSmoothQuadraticCutoff_contDiff n).continuous.mul
      ((unitSmoothQuadraticCutoff_contDiff n).continuous.comp
        (continuous_add_const t))).aestronglyMeasurable
  · exact Eventually.of_forall (quadraticCutoff_smooth_integrand_bound n t)
  · exact Eventually.of_forall fun x =>
      (unitSmoothQuadraticCutoff_tendsto x).mul (unitSmoothQuadraticCutoff_tendsto (x+t))

private theorem quadraticCutoff_smooth_autocorr_abs_le_one (n : ℕ) (t : ℝ) :
    |autocorr (unitSmoothQuadraticCutoff n) t| ≤ 1 := by
  have hBi : Integrable ((Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ))) :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have h := norm_integral_le_of_norm_le hBi
    (Eventually.of_forall (quadraticCutoff_smooth_integrand_bound n t))
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.norm_eq_abs] at h
  norm_num at h
  exact h

/-- Bounded correlations preserve every polynomial lag moment of the smooth cutoff family. -/
private theorem quadraticCutoff_smooth_lag_tendsto (k : ℕ) :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) 1,
      t^k*((∫ x, unitSmoothQuadraticCutoff n x^2)-autocorr (unitSmoothQuadraticCutoff n) t))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        t^k*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t))) := by
  have hBi : IntegrableOn (fun t : ℝ => 2*|t^k|) (Ioc (0 : ℝ) 1) :=
    (continuous_const.mul (continuous_pow k).abs).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hBi (fun n => ?_) ?_
  · have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr
      (unitSmoothQuadraticCutoff_contDiff n) (quadraticCutoff_smooth_compact n)
    exact ((continuous_pow k).mul (continuous_const.sub hc)).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t => by
      have hE : |∫ x, unitSmoothQuadraticCutoff n x^2| ≤ 1 := by
        simpa only [autocorr, add_zero, pow_two] using
          quadraticCutoff_smooth_autocorr_abs_le_one n 0
      have hC := quadraticCutoff_smooth_autocorr_abs_le_one n t
      have htriangle := abs_add_le (∫ x, unitSmoothQuadraticCutoff n x^2)
        (-autocorr (unitSmoothQuadraticCutoff n) t)
      rw [← sub_eq_add_neg, abs_neg] at htriangle
      have hD : |(∫ x, unitSmoothQuadraticCutoff n x^2)-autocorr (unitSmoothQuadraticCutoff n) t| ≤ 2 := by
        linarith only [htriangle, hE, hC]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hD (abs_nonneg (t^k))
  · exact Eventually.of_forall fun t =>
      (quadraticCutoff_smooth_mass_tendsto.sub
        (quadraticCutoff_smooth_autocorr_tendsto t)).const_mul (t^k)

/-- Higher Gamma terms repair a smooth test on which the mass-only reserve fails. -/
theorem exists_odd_unit_reservedGamma_neg_weil_pos :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ x, F (-x) = -F x) ∧
      retainedOddGammaLowerForm F+(∫ x, F x^2)/64 < 0 ∧ 0 < weilQuad F := by
  have hneg := (quadraticCutoff_smooth_retained_tendsto.add
    (quadraticCutoff_smooth_mass_tendsto.div_const 64)).eventually
      (Iio_mem_nhds retainedOddGamma_quadraticCutoff_add_reserve_neg)
  have hgood := ((quadraticCutoff_smooth_retained_tendsto.add
    (quadraticCutoff_smooth_mass_tendsto.const_mul (193/10000))).add
      ((quadraticCutoff_smooth_lag_tendsto 3).div_const 960)).add
        ((quadraticCutoff_smooth_lag_tendsto 4).div_const 192)
  have hpos := hgood.eventually
    (Ioi_mem_nhds retainedOddGamma_quadraticCutoff_add_higher_reserve_pos)
  obtain ⟨n, hn, hp⟩ := (hneg.and hpos).exists
  exact ⟨_, unitSmoothQuadraticCutoff_contDiff n, unitSmoothQuadraticCutoff_support n,
    unitSmoothQuadraticCutoff_odd n, hn, hp.trans_le
      (weilQuad_ge_retainedOddGamma_add_higher_lags (unitSmoothQuadraticCutoff_contDiff n)
        (unitSmoothQuadraticCutoff_support n) (unitSmoothQuadraticCutoff_odd n))⟩

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGamma_quadraticCutoff_add_higher_reserve_pos

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quadraticCutoffWindow_jump_moment
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_odd_unit_reservedGamma_neg_weil_pos
