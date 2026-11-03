import GaloisForLFunctions.WindowTowerOfSpecZ.TheRetainedGammaLowerFormHasANegativeDirection

/-!
# A quadratic endpoint cutoff defeats the uniform Gamma reserve

The odd quintic `2x(1−4x²)²`, extended by zero outside the unit window,
has a negative retained Gamma form even after adding `‖F‖²/64`.
Centering the overlap gives its exact correlation polynomial. The argument
retains the signed prime-two contribution and bounds the sinh pole from below.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- The odd unit-window profile with a quadratic zero at each endpoint. -/
def quadraticCutoffWindow (x : ℝ) : ℝ := 2 * cubicWindow x * (1 - 4 * x ^ 2)

theorem continuous_quadraticCutoffWindow : Continuous quadraticCutoffWindow := by
  unfold quadraticCutoffWindow
  exact (continuous_const.mul continuous_cubicWindow).mul
    (continuous_const.sub (continuous_const.mul (continuous_pow 2)))

theorem quadraticCutoffWindow_inside {x : ℝ}
    (hl : -(1 / 2 : ℝ) ≤ x) (hr : x ≤ 1 / 2) :
    quadraticCutoffWindow x = 2 * x - 16 * x ^ 3 + 32 * x ^ 5 := by
  rw [quadraticCutoffWindow, cubicWindow_inside hl hr]
  ring

theorem quadraticCutoffWindow_outside {x : ℝ}
    (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2)) : quadraticCutoffWindow x = 0 := by
  rw [quadraticCutoffWindow, cubicWindow_outside hx, mul_zero, zero_mul]

theorem compact_quadraticCutoffWindow : HasCompactSupport quadraticCutoffWindow :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => quadraticCutoffWindow_outside hx)

theorem quadraticCutoffWindow_odd (x : ℝ) :
    quadraticCutoffWindow (-x) = -quadraticCutoffWindow x := by
  simp only [quadraticCutoffWindow, cubicWindow_odd, neg_sq]
  ring

/-- The exact positive-lag correlation of the quadratic endpoint cutoff. -/
def quadraticCutoffCorrPoly (t : ℝ) : ℝ :=
  128 / 3465 - 256 / 315 * t ^ 2 + 128 / 21 * t ^ 4 - 128 / 15 * t ^ 5 +
    512 / 105 * t ^ 7 - 128 / 63 * t ^ 9 + 256 / 693 * t ^ 11

private def centeredCorrAnti (t x : ℝ) : ℝ :=
  (2*x+t)^11/22 - (4+5*t^2)*(2*x+t)^9/18 +
    (6+8*t^2+10*t^4)*(2*x+t)^7/14 - (4+2*t^2+10*t^6)*(2*x+t)^5/10 +
    (1+2*t^4-8*t^6+5*t^8)*(2*x+t)^3/6 - t^2*(1-t^2)^4*(2*x+t)/2

private theorem centeredCorrAnti_deriv (t x : ℝ) :
    HasDerivAt (centeredCorrAnti t)
      ((2*x-16*x^3+32*x^5) * (2*(x+t)-16*(x+t)^3+32*(x+t)^5)) x := by
  have h := ((hasDerivAt_id x).const_mul 2).add_const t
  have h1 := (h.pow 11).div_const 22
  have h2 := ((h.pow 9).const_mul (4+5*t^2)).div_const 18
  have h3 := ((h.pow 7).const_mul (6+8*t^2+10*t^4)).div_const 14
  have h4 := ((h.pow 5).const_mul (4+2*t^2+10*t^6)).div_const 10
  have h5 := ((h.pow 3).const_mul (1+2*t^4-8*t^6+5*t^8)).div_const 6
  have h6 := (h.const_mul (t^2*(1-t^2)^4)).div_const 2
  exact (((((h1.sub h2).add h3).sub h4).add h5).sub h6).congr_deriv (by
    simp only [id_eq]
    ring)

/-- Centering the overlap reduces the correlation to an even polynomial integral. -/
theorem quadraticCutoffWindow_autocorr {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    autocorr quadraticCutoffWindow t = quadraticCutoffCorrPoly t := by
  have he : (fun x => quadraticCutoffWindow x * quadraticCutoffWindow (x+t)) =
      (Icc (-(1/2 : ℝ)) (1/2-t)).indicator
        (fun x => (2*x-16*x^3+32*x^5) * (2*(x+t)-16*(x+t)^3+32*(x+t)^5)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2-t)
    · rw [indicator_of_mem hx,
        quadraticCutoffWindow_inside hx.1 (by linarith only [hx.2, ht]),
        quadraticCutoffWindow_inside (by linarith only [hx.1, ht]) (by linarith only [hx.2])]
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -(1/2 : ℝ)
      · rw [quadraticCutoffWindow_outside (fun h => not_lt_of_ge h.1 hl), zero_mul]
      · have hr : 1/2 < x+t := by
          have h := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith only [h]
        rw [quadraticCutoffWindow_outside (x := x+t) (fun h => not_lt_of_ge h.2 hr), mul_zero]
  unfold autocorr
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [ht1] : -(1/2 : ℝ) ≤ 1/2-t),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => centeredCorrAnti_deriv t x)
      ((by fun_prop : Continuous (fun x : ℝ =>
        (2*x-16*x^3+32*x^5)*(2*(x+t)-16*(x+t)^3+32*(x+t)^5))).intervalIntegrable _ _)]
  unfold centeredCorrAnti quadraticCutoffCorrPoly
  ring

theorem quadraticCutoffWindow_mass : (∫ x, quadraticCutoffWindow x ^ 2) = 128 / 3465 := by
  have h := quadraticCutoffWindow_autocorr (t := 0) le_rfl (by norm_num)
  simpa [autocorr, quadraticCutoffCorrPoly, sq] using h

theorem quadraticCutoffWindow_position_moment :
    (∫ x, x * quadraticCutoffWindow x) = 4 / 105 := by
  have he : (fun x => x * quadraticCutoffWindow x) =
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun x => 2*x^2-16*x^4+32*x^6) := by
    funext x
    by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
    · rw [indicator_of_mem hx, quadraticCutoffWindow_inside hx.1 hx.2]; ring
    · rw [indicator_of_notMem hx, quadraticCutoffWindow_outside hx, mul_zero]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2)]
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  norm_num

private def quadraticCutoffLagQuotient (t : ℝ) : ℝ :=
  256/315*t-128/21*t^3+128/15*t^4-512/105*t^6+128/63*t^8-256/693*t^10

private theorem quadraticCutoffLagQuotient_eq {t : ℝ} (ht : t ≠ 0) :
    (128 / 3465 - quadraticCutoffCorrPoly t) / t = quadraticCutoffLagQuotient t := by
  unfold quadraticCutoffCorrPoly quadraticCutoffLagQuotient
  field_simp
  ring

theorem quadraticCutoffWindow_logarithmic_integral :
    (∫ t in Ioc (0 : ℝ) 1,
      ((∫ x, quadraticCutoffWindow x ^ 2) - autocorr quadraticCutoffWindow t) / t) =
      128/315-32/21+128/75-512/735+128/567-256/7623 := by
  rw [quadraticCutoffWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1,
      (128/3465 - autocorr quadraticCutoffWindow t) / t) =
      ∫ t in (0 : ℝ)..1, quadraticCutoffLagQuotient t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [quadraticCutoffWindow_autocorr ht.1.le ht.2, quadraticCutoffLagQuotient_eq ht.1.ne']
  rw [he]
  unfold quadraticCutoffLagQuotient
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow]
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

theorem quadraticCutoffWindow_jump_first_moment :
    (∫ t in Ioc (0 : ℝ) 1,
      t * ((∫ x, quadraticCutoffWindow x ^ 2) - autocorr quadraticCutoffWindow t)) =
      64/315-64/63+128/105-512/945+128/693-256/9009 := by
  rw [quadraticCutoffWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1, t * (128/3465 - autocorr quadraticCutoffWindow t)) =
      ∫ t in (0 : ℝ)..1,
        (256/315*t^3-128/21*t^5+128/15*t^6-512/105*t^8+128/63*t^10-256/693*t^12) := by
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

private def quadraticCutoffCorrLower : ℝ :=
  let l : ℝ := 693147180 / 1000000000
  let h : ℝ := 693147181 / 1000000000
  128/3465-256/315*h^2+128/21*l^4-128/15*h^5+512/105*l^7-128/63*h^9+256/693*l^11

private theorem quadraticCutoffCorrLower_le :
    quadraticCutoffCorrLower ≤ autocorr quadraticCutoffWindow (Real.log 2) := by
  have hl : (693147180/1000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hu : Real.log 2 ≤ (693147181/1000000000 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have lo (n : ℕ) := pow_le_pow_left₀
    (by norm_num : (0 : ℝ) ≤ 693147180/1000000000) hl n
  have hi (n : ℕ) := pow_le_pow_left₀ h0 hu n
  rw [quadraticCutoffWindow_autocorr h0 (by linarith only [hu])]
  unfold quadraticCutoffCorrLower quadraticCutoffCorrPoly
  dsimp only
  linarith only [hi 2, lo 4, hi 5, lo 7, hi 9, lo 11]

private theorem quadraticCutoff_prime_cost_le :
    -(2 * (Real.log 2 / Real.sqrt 2) * autocorr quadraticCutoffWindow (Real.log 2)) ≤
      -2 * (4902/10000) * quadraticCutoffCorrLower := by
  have hw := ArithmeticIncidencePositivity.vonMangoldtAtom_two_bounds
  simp only [vonMangoldtAtom, if_pos le_rfl,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] at hw
  have hc0 : quadraticCutoffCorrLower ≤ 0 := by norm_num [quadraticCutoffCorrLower]
  have h1 := mul_le_mul_of_nonpos_left quadraticCutoffCorrLower_le
    (show -(2 * (Real.log 2 / Real.sqrt 2)) ≤ 0 by linarith only [hw.1])
  have h2 := mul_le_mul_of_nonneg_right hw.2 (neg_nonneg.mpr hc0)
  nlinarith only [h1, h2]

private theorem quadraticCutoffWindow_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ quadraticCutoffWindow x := by
  by_cases hi : x ∈ Icc (-(1/2 : ℝ)) (1/2)
  · rw [quadraticCutoffWindow, cubicWindow_inside hi.1 hi.2]
    have he : 2 * (x * (1-4*x^2)) * (1-4*x^2) = 2*x*(1-4*x^2)^2 := by ring
    rw [he]
    positivity
  · rw [quadraticCutoffWindow_outside hi]

private theorem quadraticCutoff_pole_cost_ge :
    (8/11025 : ℝ) ≤ sinhPairing quadraticCutoffWindow ^ 2 / 2 := by
  have hpos (x : ℝ) (hx : 0 ≤ x) :
      x * quadraticCutoffWindow x ≤ quadraticCutoffWindow x * (2 * Real.sinh (x/2)) := by
    have h := HTGeometry.self_le_sinh_of_nonneg (by positivity : 0 ≤ x/2)
    have hm := mul_le_mul_of_nonneg_right (show x ≤ 2*Real.sinh (x/2) by linarith only [h])
      (quadraticCutoffWindow_nonneg hx)
    simpa only [mul_comm] using hm
  have hpt (x : ℝ) :
      x * quadraticCutoffWindow x ≤ quadraticCutoffWindow x * (2 * Real.sinh (x/2)) := by
    by_cases hx : 0 ≤ x
    · exact hpos x hx
    · have h := hpos (-x) (by linarith only [not_le.mp hx])
      simpa only [quadraticCutoffWindow_odd, neg_div, Real.sinh_neg, mul_neg, neg_mul, neg_neg] using h
  have hi1 : Integrable (fun x => x * quadraticCutoffWindow x) :=
    (continuous_id.mul continuous_quadraticCutoffWindow).integrable_of_hasCompactSupport
      compact_quadraticCutoffWindow.mul_left
  have hi2 : Integrable (fun x => quadraticCutoffWindow x * (2 * Real.sinh (x/2))) :=
    (continuous_quadraticCutoffWindow.mul (by fun_prop)).integrable_of_hasCompactSupport
      compact_quadraticCutoffWindow.mul_right
  have h := integral_mono hi1 hi2 hpt
  rw [quadraticCutoffWindow_position_moment] at h
  change (4/105 : ℝ) ≤ sinhPairing quadraticCutoffWindow at h
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4/105) h 2
  norm_num at hs
  linarith only [hs]

private theorem gamma_constant_lower :
    577215/1000000+1098612/1000000+1-3/(314159/100000)+693147180/1000000000 ≤
      Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 := by
  have hp : (314159/100000 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d6]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 3/Real.pi)
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) Real.pi_ne_zero] at hlog
  have hdiv : 3/Real.pi ≤ 3/(314159/100000 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    norm_num
    linarith only [hp]
  have he := SelectivePositivityAndThresholdLaws.eulerMascheroniConstant_gt_577215_div_1000000
  linarith only [hlog, hdiv, he, Real.log_three_gt_d9, Real.log_two_gt_d9]

private theorem quadraticCutoff_reserved_certificate :
    (128/315-32/21+128/75-512/735+128/567-256/7623 : ℝ) -
      (577215/1000000+1098612/1000000+1-3/(314159/100000)+693147180/1000000000) * (128/3465) -
      (64/315-64/63+128/105-512/945+128/693-256/9009)/24 -
      (4/105)^2/16 - 8/11025 - 2*(4902/10000)*quadraticCutoffCorrLower + (128/3465)/64 < 0 := by
  norm_num [quadraticCutoffCorrLower]

/-- The quadratic cutoff defeats the retained form even with its uniform exterior reserve. -/
theorem retainedOddGamma_quadraticCutoff_add_reserve_neg :
    retainedOddGammaLowerForm quadraticCutoffWindow +
      (∫ x, quadraticCutoffWindow x ^ 2) / 64 < 0 := by
  rw [retainedOddGammaLowerForm, quadraticCutoffWindow_logarithmic_integral,
    quadraticCutoffWindow_jump_first_moment, quadraticCutoffWindow_mass,
    quadraticCutoffWindow_position_moment]
  linarith only [gamma_constant_lower, quadraticCutoff_prime_cost_le,
    quadraticCutoff_pole_cost_ge, quadraticCutoff_reserved_certificate]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quadraticCutoffWindow_autocorr
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGamma_quadraticCutoff_add_reserve_neg
