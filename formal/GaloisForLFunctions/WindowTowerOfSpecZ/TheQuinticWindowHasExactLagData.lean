import GaloisForLFunctions.WindowTowerOfSpecZ.TheCubicWindowHasExactJumpMoments

/-!
# Exact lag data of the odd quintic window

The source `2x(1−4x²)(1−2x²)` on the unit window tests the retained Gamma
comparison. Its correlation and logarithmic lag integral are exact polynomials
and rational numbers, respectively; no endpoint logarithm estimate is needed.
-/

noncomputable section
open Real MeasureTheory Set intervalIntegral
namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- The odd quintic supported on the unit window. -/
def quinticWindow (x : ℝ) : ℝ := 2 * cubicWindow x * (1 - 2 * x ^ 2)

theorem continuous_quinticWindow : Continuous quinticWindow := by
  unfold quinticWindow
  exact (continuous_const.mul continuous_cubicWindow).mul
    (continuous_const.sub (continuous_const.mul (continuous_pow 2)))

theorem quinticWindow_inside {x : ℝ} (hl : -(1 / 2 : ℝ) ≤ x) (hr : x ≤ 1 / 2) :
    quinticWindow x = 2 * x - 12 * x ^ 3 + 16 * x ^ 5 := by
  rw [quinticWindow, cubicWindow_inside hl hr]
  ring

theorem quinticWindow_outside {x : ℝ} (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    quinticWindow x = 0 := by
  rw [quinticWindow, cubicWindow_outside hx, mul_zero, zero_mul]

theorem compact_quinticWindow : HasCompactSupport quinticWindow :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => quinticWindow_outside hx)

theorem quinticWindow_odd (x : ℝ) : quinticWindow (-x) = -quinticWindow x := by
  simp only [quinticWindow, cubicWindow_odd, neg_sq]
  ring

/-- Positive-lag correlation of the quintic for `0 ≤ t ≤ 1`. -/
def quinticCorrPoly (t : ℝ) : ℝ :=
  62 / 1155 - 334 / 315 * t ^ 2 + 2 / 3 * t ^ 3 + 88 / 21 * t ^ 4 -
    86 / 15 * t ^ 5 + 268 / 105 * t ^ 7 - 16 / 21 * t ^ 9 + 64 / 693 * t ^ 11

private def quinticCorrAnti (t x : ℝ) : ℝ :=
  (4 * t - 24 * t ^ 3 + 32 * t ^ 5) * x ^ 2 / 2 +
  (4 - 72 * t ^ 2 + 160 * t ^ 4) * x ^ 3 / 3 +
  (-96 * t + 464 * t ^ 3 - 192 * t ^ 5) * x ^ 4 / 4 +
  (-48 + 752 * t ^ 2 - 960 * t ^ 4) * x ^ 5 / 5 +
  (624 * t - 2112 * t ^ 3 + 256 * t ^ 5) * x ^ 6 / 6 +
  (208 - 2496 * t ^ 2 + 1280 * t ^ 4) * x ^ 7 / 7 +
  (-1536 * t + 2560 * t ^ 3) * x ^ 8 / 8 +
  (-384 + 2560 * t ^ 2) * x ^ 9 / 9 +
  1280 * t * x ^ 10 / 10 + 256 * x ^ 11 / 11

private theorem deriv_quinticCorrAnti (t x : ℝ) :
    HasDerivAt (quinticCorrAnti t)
      ((2 * x - 12 * x ^ 3 + 16 * x ^ 5) *
        (2 * (x + t) - 12 * (x + t) ^ 3 + 16 * (x + t) ^ 5)) x := by
  have h1 := ((hasDerivAt_pow 2 x).const_mul (4*t-24*t^3+32*t^5)).div_const 2
  have h2 := ((hasDerivAt_pow 3 x).const_mul (4-72*t^2+160*t^4)).div_const 3
  have h3 := ((hasDerivAt_pow 4 x).const_mul (-96*t+464*t^3-192*t^5)).div_const 4
  have h4 := ((hasDerivAt_pow 5 x).const_mul (-48+752*t^2-960*t^4)).div_const 5
  have h5 := ((hasDerivAt_pow 6 x).const_mul (624*t-2112*t^3+256*t^5)).div_const 6
  have h6 := ((hasDerivAt_pow 7 x).const_mul (208-2496*t^2+1280*t^4)).div_const 7
  have h7 := ((hasDerivAt_pow 8 x).const_mul (-1536*t+2560*t^3)).div_const 8
  have h8 := ((hasDerivAt_pow 9 x).const_mul (-384+2560*t^2)).div_const 9
  have h9 := ((hasDerivAt_pow 10 x).const_mul (1280*t)).div_const 10
  have h10 := ((hasDerivAt_pow 11 x).const_mul 256).div_const 11
  exact (((((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).congr_deriv
    (by ring)

/-- Integrating over the overlap gives the quintic's exact correlation. -/
theorem quinticWindow_autocorr {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x, quinticWindow x * quinticWindow (x + t)) = quinticCorrPoly t := by
  have he : (fun x => quinticWindow x * quinticWindow (x + t)) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2 - t)).indicator
        (fun x => (2 * x - 12 * x ^ 3 + 16 * x ^ 5) *
          (2 * (x + t) - 12 * (x + t) ^ 3 + 16 * (x + t) ^ 5)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 - t)
    · rw [indicator_of_mem hx, quinticWindow_inside hx.1 (by linarith only [hx.2, ht]),
        quinticWindow_inside (by linarith only [hx.1, ht]) (by linarith only [hx.2])]
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -(1 / 2 : ℝ)
      · rw [quinticWindow_outside (fun h => not_lt_of_ge h.1 hl), zero_mul]
      · have hr : 1 / 2 < x + t := by
          have h := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith only [h]
        rw [quinticWindow_outside (x := x + t) (fun h => not_lt_of_ge h.2 hr), mul_zero]
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [ht1] : -(1 / 2 : ℝ) ≤ 1 / 2 - t)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => deriv_quinticCorrAnti t x)
    ((by fun_prop : Continuous (fun x : ℝ => (2*x-12*x^3+16*x^5) *
      (2*(x+t)-12*(x+t)^3+16*(x+t)^5))).intervalIntegrable _ _)]
  unfold quinticCorrAnti quinticCorrPoly
  ring

/-- The quintic's exact mass. -/
theorem quinticWindow_mass : (∫ x, quinticWindow x ^ 2) = 62 / 1155 := by
  have h := quinticWindow_autocorr (t := 0) le_rfl (by norm_num)
  simpa [quinticCorrPoly, sq] using h

/-- The linear position moment controlling the pole's linear part. -/
theorem quinticWindow_position_moment : (∫ x, x * quinticWindow x) = 11 / 210 := by
  have he : (fun x => x * quinticWindow x) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (fun x => 2 * x ^ 2 - 12 * x ^ 4 + 16 * x ^ 6) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [indicator_of_mem hx, quinticWindow_inside hx.1 hx.2]
      ring
    · rw [indicator_of_notMem hx, quinticWindow_outside hx, mul_zero]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => 2 * y ^ 3 / 3 - 12 * y ^ 5 / 5 + 16 * y ^ 7 / 7)
      (2 * x ^ 2 - 12 * x ^ 4 + 16 * x ^ 6) x := by
    have h1 := ((hasDerivAt_pow 3 x).const_mul 2).div_const 3
    have h2 := ((hasDerivAt_pow 5 x).const_mul 12).div_const 5
    have h3 := ((hasDerivAt_pow 7 x).const_mul 16).div_const 7
    exact ((h1.sub h2).add h3).congr_deriv (by ring)
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous (fun x : ℝ => 2*x^2-12*x^4+16*x^6)).intervalIntegrable _ _)]
  norm_num

private def quinticLagQuotient (t : ℝ) : ℝ :=
  334 / 315 * t - 2 / 3 * t ^ 2 - 88 / 21 * t ^ 3 + 86 / 15 * t ^ 4 -
    268 / 105 * t ^ 6 + 16 / 21 * t ^ 8 - 64 / 693 * t ^ 10

private theorem quinticCorrPoly_deficit (t : ℝ) :
    62 / 1155 - quinticCorrPoly t = t * quinticLagQuotient t := by
  unfold quinticCorrPoly quinticLagQuotient
  ring

private theorem integral_quinticLagQuotient :
    (∫ t in (0 : ℝ)..1, quinticLagQuotient t) =
      167 / 315 - 2 / 9 - 22 / 21 + 86 / 75 - 268 / 735 + 16 / 189 - 64 / 7623 := by
  have hd (t : ℝ) :
      HasDerivAt (fun s : ℝ => 167*s^2/315-2*s^3/9-22*s^4/21+86*s^5/75-
        268*s^7/735+16*s^9/189-64*s^11/7623) (quinticLagQuotient t) t := by
    have h1 := ((hasDerivAt_pow 2 t).const_mul 167).div_const 315
    have h2 := ((hasDerivAt_pow 3 t).const_mul 2).div_const 9
    have h3 := ((hasDerivAt_pow 4 t).const_mul 22).div_const 21
    have h4 := ((hasDerivAt_pow 5 t).const_mul 86).div_const 75
    have h5 := ((hasDerivAt_pow 7 t).const_mul 268).div_const 735
    have h6 := ((hasDerivAt_pow 9 t).const_mul 16).div_const 189
    have h7 := ((hasDerivAt_pow 11 t).const_mul 64).div_const 7623
    exact ((((((h1.sub h2).sub h3).add h4).sub h5).add h6).sub h7).congr_deriv
      (by unfold quinticLagQuotient; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by unfold quinticLagQuotient; fun_prop : Continuous quinticLagQuotient).intervalIntegrable _ _)]
  norm_num

/-- The logarithmic jump integral is rational because its zero-lag singularity cancels. -/
theorem quinticWindow_logarithmic_integral :
    (∫ t in Ioc (0 : ℝ) 1,
      ((∫ x, quinticWindow x ^ 2) - ∫ x, quinticWindow x * quinticWindow (x + t)) / t) =
      167 / 315 - 2 / 9 - 22 / 21 + 86 / 75 - 268 / 735 + 16 / 189 - 64 / 7623 := by
  rw [quinticWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1,
      (62 / 1155 - ∫ x, quinticWindow x * quinticWindow (x + t)) / t) =
      ∫ t in Ioc (0 : ℝ) 1, quinticLagQuotient t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change (62 / 1155 - ∫ x, quinticWindow x * quinticWindow (x + t)) / t = _
    rw [quinticWindow_autocorr ht.1.le ht.2, quinticCorrPoly_deficit,
      mul_div_cancel_left₀ _ ht.1.ne']
  rw [he, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_quinticLagQuotient

/-- The logarithmic lag integrand is integrable at zero. -/
theorem integrableOn_quinticWindow_logarithmic_deficit :
    IntegrableOn (fun t : ℝ =>
      ((∫ x, quinticWindow x ^ 2) - ∫ x, quinticWindow x * quinticWindow (x + t)) / t)
      (Ioc (0 : ℝ) 1) := by
  have hc : Continuous quinticLagQuotient := by unfold quinticLagQuotient; fun_prop
  refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [quinticWindow_mass, quinticWindow_autocorr ht.1.le ht.2,
    quinticCorrPoly_deficit, mul_div_cancel_left₀ _ ht.1.ne']

/-- The first lag cost keeps the exact primitive correction for the quintic. -/
theorem quinticWindow_jump_first_moment :
    (∫ t in Ioc (0 : ℝ) 1,
      t * ((∫ x, quinticWindow x ^ 2) - ∫ x, quinticWindow x * quinticWindow (x + t))) =
      167 / 630 - 2 / 15 - 44 / 63 + 86 / 105 - 268 / 945 + 16 / 231 - 64 / 9009 := by
  rw [quinticWindow_mass]
  have he : (∫ t in Ioc (0 : ℝ) 1,
      t * (62 / 1155 - ∫ x, quinticWindow x * quinticWindow (x + t))) =
      ∫ t in Ioc (0 : ℝ) 1, t * (62 / 1155 - quinticCorrPoly t) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change t * (62 / 1155 - ∫ x, quinticWindow x * quinticWindow (x + t)) = _
    rw [quinticWindow_autocorr ht.1.le ht.2]
  have hd (t : ℝ) : HasDerivAt
      (fun s : ℝ => 167*s^4/630-2*s^5/15-44*s^6/63+86*s^7/105-
        268*s^9/945+16*s^11/231-64*s^13/9009)
      (t * (62 / 1155 - quinticCorrPoly t)) t := by
    have h1 := ((hasDerivAt_pow 4 t).const_mul 167).div_const 630
    have h2 := ((hasDerivAt_pow 5 t).const_mul 2).div_const 15
    have h3 := ((hasDerivAt_pow 6 t).const_mul 44).div_const 63
    have h4 := ((hasDerivAt_pow 7 t).const_mul 86).div_const 105
    have h5 := ((hasDerivAt_pow 9 t).const_mul 268).div_const 945
    have h6 := ((hasDerivAt_pow 11 t).const_mul 16).div_const 231
    have h7 := ((hasDerivAt_pow 13 t).const_mul 64).div_const 9009
    exact ((((((h1.sub h2).sub h3).add h4).sub h5).add h6).sub h7).congr_deriv
      (by unfold quinticCorrPoly; ring)
  rw [he, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by unfold quinticCorrPoly; fun_prop :
        Continuous (fun t : ℝ => t * (62 / 1155 - quinticCorrPoly t))).intervalIntegrable _ _)]
  norm_num

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quinticWindow_autocorr
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quinticWindow_mass
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quinticWindow_logarithmic_integral
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quinticWindow_position_moment
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.quinticWindow_jump_first_moment
