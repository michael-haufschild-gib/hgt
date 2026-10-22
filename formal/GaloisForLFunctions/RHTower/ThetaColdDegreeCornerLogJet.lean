import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionFourthTuran

/-!
# Literal theta sign at the cold/degree corner

The third logarithmic derivative in the squared spatial coordinate is strictly negative
on `[9, infinity)`. Exact first-atom formulas and complete higher-tail bounds control
the three derivatives; no differentiated asymptotic or zero data is used.

This supplies the signed profile for a joint Gaussian-aperture/degree limit. The transfer
to that limit is a separate obligation. No degree-zero aperture or RH conclusion follows.
-/

open Real Set Filter Topology
namespace RHTower.ThetaColdCorner
noncomputable section

private theorem tail_log_bounds {x : ℝ} (hx : 0 < x) :
    thetaCuspHigherLikelihoodLogJetOne x ≤ 1 / 10 ∧
    -(1 / 100 : ℝ) ≤ thetaCuspHigherLikelihoodLogJetTwo x ∧
    thetaCuspHigherLikelihoodLogJetThree x ≤ 30 := by
  let s := 1 + thetaCuspHigherToFirstAtomLikelihoodRatio x
  have hs : 1 ≤ s := by
    dsimp [s]
    linarith [thetaCuspHigherToFirstAtomLikelihoodRatio_nonneg hx]
  have hs0 : 0 < s := by linarith
  let a := thetaCuspHigherLikelihoodJetOne x / s
  let b := thetaCuspHigherLikelihoodJetTwo x / s
  let c := thetaCuspHigherLikelihoodJetThree x / s
  have ha : |a| ≤ 1 / 10 := by
    dsimp [a]
    rw [abs_div, abs_of_pos hs0]
    exact (div_le_self (abs_nonneg _) hs).trans (abs_thetaCuspHigherLikelihoodJetOne_lt hx).le
  have hb0 : 0 ≤ b := div_nonneg (thetaCuspHigherLikelihoodJetTwo_pos hx).le hs0.le
  have hb : b ≤ 13 / 10 :=
    (div_le_self (thetaCuspHigherLikelihoodJetTwo_pos hx).le hs).trans
      (thetaCuspHigherLikelihoodJetTwo_lt hx).le
  have hc : c ≤ 29 := by
    dsimp [c]
    exact (le_abs_self _).trans ((by
      rw [abs_div, abs_of_pos hs0]
      exact (div_le_self (abs_nonneg _) hs).trans
        (abs_thetaCuspHigherLikelihoodJetThree_lt hx).le) :
      |thetaCuspHigherLikelihoodJetThree x / s| ≤ 29)
  have ha' := abs_le.mp ha
  have ha2 : a ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by nlinarith
  have ha3 : a ^ 3 ≤ (1 / 10 : ℝ) ^ 3 := by nlinarith [sq_nonneg (a - 1 / 10)]
  have hab : -(13 / 100 : ℝ) ≤ a * b := by nlinarith
  have heq2 : thetaCuspHigherLikelihoodLogJetTwo x = b - a ^ 2 := by
    simp only [thetaCuspHigherLikelihoodLogJetTwo, a, b, s, div_pow]
  have heq3 : thetaCuspHigherLikelihoodLogJetThree x = c - 3 * a * b + 2 * a ^ 3 := by
    simp only [thetaCuspHigherLikelihoodLogJetThree, a, b, c]
    change _ / s - 3 * _ * _ / s^2 + 2 * _^3 / s^3 = _
    field_simp
  refine ⟨ha'.2, ?_, ?_⟩
  · rw [heq2]; nlinarith
  · rw [heq3]; nlinarith

private theorem first_log_bounds {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFirstAtomLogJetOne x ≤ -2 * thetaCuspMorseScale 1 x + 13 / 2 ∧
    -4 * thetaCuspMorseScale 1 x - 8 ≤ thetaCuspFirstAtomLogJetTwo x ∧
    thetaCuspFirstAtomLogJetThree x ≤ -8 * thetaCuspMorseScale 1 x + 48 := by
  let s := thetaCuspMorseScale 1 x
  let q := thetaCuspBornWittenWeight 1 x
  have hsq : q = s - 3 / 2 := thetaCuspBornWittenWeight_eq 1 x
  have hs : 3 ≤ s := le_trans Real.pi_gt_three.le (thetaCuspMorseScale_pi_le (by norm_num) hx)
  have hq : 3 / 2 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hi : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hi' : q⁻¹ ≤ 2 / 3 := by rw [inv_eq_one_div, div_le_iff₀ hq0]; linarith
  have hi2 : (q⁻¹) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by gcongr
  have hi3 : (q⁻¹) ^ 3 ≤ (2 / 3 : ℝ) ^ 3 := by gcongr
  have h1 : thetaCuspFirstAtomLogJetOne x = -2 * s + 9 / 2 + 3 * q⁻¹ := by
    dsimp only [thetaCuspFirstAtomLogJetOne, thetaCuspBornWittenSuperpotential,
      thetaCuspMorseSuperpotential]
    change -2 * (s - 5 / 4 - s / q) = _
    rw [show s = q + 3 / 2 by linarith]
    field_simp
    ring
  have h2 : thetaCuspFirstAtomLogJetTwo x = -4 * s - 6 * q⁻¹ - 9 * (q⁻¹)^2 := by
    dsimp only [thetaCuspFirstAtomLogJetTwo, thetaCuspBornWittenLogCurvature,
      thetaCuspBornWittenCurvature]
    change - (2 * (2 * s + 3 * s / q ^ 2)) = _
    rw [show s = q + 3 / 2 by linarith]
    field_simp
    ring
  have h3 : thetaCuspFirstAtomLogJetThree x = -8 * s + 12 * q⁻¹ +
      54 * (q⁻¹)^2 + 54 * (q⁻¹)^3 := by
    dsimp only [thetaCuspFirstAtomLogJetThree, thetaCuspBornWittenLogThirdDerivative]
    change -((2 * q + 3) * (4 - 6 / q ^ 2 - 18 / q ^ 3)) = _
    rw [show s = q + 3 / 2 by linarith]
    field_simp
    ring
  rw [h1, h2, h3]
  dsimp only [s] at *
  constructor
  · linarith
  constructor <;> linarith

/-- Literal theta logarithmic jets expose a negative square-coordinate tail. -/
theorem logarithmic_jet_combination_neg {x : ℝ} (hx : 3 ≤ x) :
    x^2 * iteratedDeriv 3 thetaCuspLogSource x -
      3*x * iteratedDeriv 2 thetaCuspLogSource x +
      3 * iteratedDeriv 1 thetaCuspLogSource x < 0 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h1, h2, h3⟩ := first_log_bounds hx0.le
  obtain ⟨t1, t2, t3⟩ := tail_log_bounds hx0
  have j1 : iteratedDeriv 1 thetaCuspLogSource x ≤ -2 * thetaCuspMorseScale 1 x + 33 / 5 := by
    rw [iteratedDeriv_one_thetaCuspLogSource_eq_full_jets hx0]; linarith
  have j2 : -4 * thetaCuspMorseScale 1 x - 801 / 100 ≤ iteratedDeriv 2 thetaCuspLogSource x := by
    rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx0]
    change -4 * thetaCuspMorseScale 1 x - 801 / 100 ≤
      thetaCuspFirstAtomLogJetTwo x + thetaCuspHigherLikelihoodLogJetTwo x
    linarith
  have j3 : iteratedDeriv 3 thetaCuspLogSource x ≤ -8 * thetaCuspMorseScale 1 x + 78 := by
    rw [iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx0]; linarith
  have hexp : 4 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hscale : 48 < thetaCuspMorseScale 1 x := by
    simp only [thetaCuspMorseScale, Nat.cast_one, one_mul]
    have hsq : 16 ≤ Real.exp x ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hpoly : 2*x^2 ≤ 4*x^2-6*x+3 := by nlinarith [sq_nonneg (x-3)]
  have hp0 : 0 < 4*x^2-6*x+3 := by nlinarith [sq_nonneg x]
  have hm := mul_lt_mul_of_pos_right hscale hp0
  have hh1 := mul_le_mul_of_nonneg_left j1 (by norm_num : (0:ℝ) ≤ 3)
  have hh2 := mul_le_mul_of_nonneg_left j2 (show 0 ≤ 3*x by positivity)
  have hh3 := mul_le_mul_of_nonneg_left j3 (sq_nonneg x)
  nlinarith [sq_nonneg (x-3)]

/-- Logarithm of the literal source in the squared spatial coordinate. -/
def squareLog (y : ℝ) : ℝ := thetaCuspLogSource (Real.sqrt y)

private def squareLogJetOne (y : ℝ) : ℝ :=
  iteratedDeriv 1 thetaCuspLogSource (Real.sqrt y) / (2 * Real.sqrt y)

private def squareLogJetTwo (y : ℝ) : ℝ :=
  (Real.sqrt y * iteratedDeriv 2 thetaCuspLogSource (Real.sqrt y) -
    iteratedDeriv 1 thetaCuspLogSource (Real.sqrt y)) / (4 * Real.sqrt y ^ 3)

private theorem hasDerivAt_log_iterated (m : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv m thetaCuspLogSource)
      (iteratedDeriv (m+1) thetaCuspLogSource x) x := by
  have h : ContDiff ℝ (↑(⊤ : ℕ∞)) thetaCuspLogSource :=
    contDiff_thetaCuspFullSource.log fun z => (thetaCuspFullSource_pos_all z).ne'
  simpa only [iteratedDeriv_succ] using
    (h.differentiable_iteratedDeriv m (by exact_mod_cast (ENat.coe_lt_top m))).differentiableAt.hasDerivAt (x := x)

private theorem hasDerivAt_squareLog {y : ℝ} (hy : 0 < y) :
    HasDerivAt squareLog (squareLogJetOne y) y := by
  have h := (hasDerivAt_log_iterated 0 (Real.sqrt y)).comp y (Real.hasDerivAt_sqrt hy.ne')
  simpa only [iteratedDeriv_zero, squareLog, squareLogJetOne, Function.comp_def, mul_one_div] using! h

private theorem hasDerivAt_squareLogJetOne {y : ℝ} (hy : 0 < y) :
    HasDerivAt squareLogJetOne (squareLogJetTwo y) y := by
  have hs := Real.hasDerivAt_sqrt hy.ne'
  have hr : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hd := (hasDerivAt_log_iterated 1 (Real.sqrt y)).comp y hs
  convert! hd.div (hs.const_mul 2) (mul_ne_zero (by norm_num) hr) using 1
  dsimp only [squareLogJetTwo, Function.comp_def]
  field_simp
  ring

private theorem hasDerivAt_squareLogJetTwo {y : ℝ} (hy : 0 < y) :
    HasDerivAt squareLogJetTwo
      ((Real.sqrt y ^ 2 * iteratedDeriv 3 thetaCuspLogSource (Real.sqrt y) -
        3 * Real.sqrt y * iteratedDeriv 2 thetaCuspLogSource (Real.sqrt y) +
        3 * iteratedDeriv 1 thetaCuspLogSource (Real.sqrt y)) /
      (8 * Real.sqrt y ^ 5)) y := by
  have hs := Real.hasDerivAt_sqrt hy.ne'
  have hr : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have h1 := (hasDerivAt_log_iterated 1 (Real.sqrt y)).comp y hs
  have h2 := (hasDerivAt_log_iterated 2 (Real.sqrt y)).comp y hs
  convert! ((hs.mul h2).sub h1).div ((hs.pow 3).const_mul 4)
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr)) using 1
  dsimp only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
  field_simp
  ring

/-- Exact coordinate change for the third logarithmic derivative. -/
theorem iteratedDeriv_three_squareLog {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 3 squareLog y =
      ((Real.sqrt y ^ 2 * iteratedDeriv 3 thetaCuspLogSource (Real.sqrt y) -
        3 * Real.sqrt y * iteratedDeriv 2 thetaCuspLogSource (Real.sqrt y) +
        3 * iteratedDeriv 1 thetaCuspLogSource (Real.sqrt y)) /
      (8 * Real.sqrt y ^ 5)) := by
  have h1 : ∀ z > 0, iteratedDeriv 1 squareLog z = squareLogJetOne z := by
    intro z hz
    simpa only [iteratedDeriv_one] using (hasDerivAt_squareLog hz).deriv
  have h2 : ∀ z > 0, iteratedDeriv 2 squareLog z = squareLogJetTwo z := by
    intro z hz
    rw [show 2 = 1+1 by rfl, iteratedDeriv_succ]
    apply HasDerivAt.deriv
    apply (hasDerivAt_squareLogJetOne hz).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hz] with t ht
    exact h1 t ht
  rw [show 3 = 2+1 by rfl, iteratedDeriv_succ]
  apply HasDerivAt.deriv
  apply (hasDerivAt_squareLogJetTwo hy).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact h2 t ht

/-- The actual theta logarithmic corner profile is strictly negative on `y ≥ 9`. -/
theorem squareLog_third_neg {y : ℝ} (hy : 9 ≤ y) :
    iteratedDeriv 3 squareLog y < 0 := by
  have hy0 : 0 < y := by linarith
  have hroot : 3 ≤ Real.sqrt y := by
    nlinarith [Real.sq_sqrt hy0.le, Real.sqrt_nonneg y]
  rw [iteratedDeriv_three_squareLog hy0]
  exact div_neg_of_neg_of_pos (logarithmic_jet_combination_neg hroot) (by positivity)

/-- A fixed, exact negative incoming profile value, with no numerical premise. -/
theorem squareLog_third_nine_neg : iteratedDeriv 3 squareLog 9 < 0 :=
  squareLog_third_neg le_rfl

end
end RHTower.ThetaColdCorner
