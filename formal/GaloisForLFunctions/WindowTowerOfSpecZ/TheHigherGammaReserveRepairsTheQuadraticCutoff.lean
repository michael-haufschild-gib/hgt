import GaloisForLFunctions.WindowTowerOfSpecZ.TheUniformGammaReserveHasANegativeDirection
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
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ

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

theorem quadraticCutoffWindow_jump_third_moment :
    (∫ t in Ioc (0 : ℝ) 1,
      t^3*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t)) =
      256/(315*6)-128/(21*8)+128/(15*9)-512/(105*11)+128/(63*13)-256/(693*15) := by
  rw [quadraticCutoffWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1, t^3*(128/3465-autocorr quadraticCutoffWindow t)) =
      ∫ t in (0 : ℝ)..1,
        (256/315*t^5-128/21*t^7+128/15*t^8-512/105*t^10+128/63*t^12-256/693*t^14) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [quadraticCutoffWindow_autocorr ht.1.le ht.2]
    unfold quadraticCutoffCorrPoly
    ring
  rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem quadraticCutoffWindow_jump_fourth_moment :
    (∫ t in Ioc (0 : ℝ) 1,
      t^4*((∫ x, quadraticCutoffWindow x^2)-autocorr quadraticCutoffWindow t)) =
      256/(315*7)-128/(21*9)+128/(15*10)-512/(105*12)+128/(63*14)-256/(693*16) := by
  rw [quadraticCutoffWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1, t^4*(128/3465-autocorr quadraticCutoffWindow t)) =
      ∫ t in (0 : ℝ)..1,
        (256/315*t^6-128/21*t^8+128/15*t^9-512/105*t^11+128/63*t^13-256/693*t^15) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [quadraticCutoffWindow_autocorr ht.1.le ht.2]
    unfold quadraticCutoffCorrPoly
    ring
  rw [he]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

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

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGamma_quadraticCutoff_add_higher_reserve_pos
