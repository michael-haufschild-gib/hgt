import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherConservation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Positive arithmetic Noether charge at the boundary

Each theta prime-link current is a nonnegative real number; the link at
the prime two is strictly positive. The full current is therefore strictly
positive. Integrability of each link and a summable uniform majorant show
that this current vanishes at positive infinity.

The conserved prime--Gamma--pole balance then identifies a strictly
positive boundary charge with the limiting integrated arithmetic exchange.
All statements use the actual theta source without a zero-location premise.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace RHTower.ThetaSourceWard

theorem integrable_primeShiftLinkDensity (S T : ThetaSource) (n : ℕ) :
    Integrable (primeShiftLinkDensity S T n) := by
  have hS : Integrable (fun y => (S.k y : ℂ)) := by
    simpa only [zero_mul, Complex.exp_zero, mul_one] using integrable_bilateralLaplace S 0
  obtain ⟨B, _, hB⟩ := T.norm_le (M := 0)
  apply hS.mul_bdd
    ((Complex.continuous_ofReal.comp (T.cont.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable)
  filter_upwards with y
  change ‖(T.k (y - Real.log n) : ℂ)‖ ≤ B
  simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using hB (y - Real.log n)

theorem tendsto_primeShiftNoetherCurrent_atTop (S T : ThetaSource) (n : ℕ) :
    Tendsto (primeShiftNoetherCurrent S T n) atTop (𝓝 0) := by
  have hi := integrable_primeShiftLinkDensity S T n
  have h₁ := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi.integrableOn
    (tendsto_atTop_add_const_right atTop (Real.log n) tendsto_id)
  have h₂ := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi.integrableOn
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have he (x : ℝ) :
      primeCoefficient n * ((∫ y in (0 : ℝ)..x + Real.log n, primeShiftLinkDensity S T n y) -
        ∫ y in (0 : ℝ)..x, primeShiftLinkDensity S T n y) =
      primeShiftNoetherCurrent S T n x := by
    rw [intervalIntegral.integral_interval_sub_left hi.intervalIntegrable hi.intervalIntegrable]
    rfl
  simpa only [id_eq, he, sub_self, mul_zero] using (h₁.sub h₂).const_mul (primeCoefficient n)

/-- All prime powers can be passed through the boundary limit. -/
theorem tendsto_fullPrimeShiftNoetherCurrent_atTop (S T : ThetaSource) :
    Tendsto (fullPrimeShiftNoetherCurrent S T) atTop (𝓝 0) := by
  obtain ⟨b, hb, hbound⟩ := exists_summable_primeShiftNoetherCurrent_bound S T
  have h := tendsto_tsum_of_dominated_convergence hb
    (fun n => tendsto_primeShiftNoetherCurrent_atTop S T n)
    (Eventually.of_forall fun x n => hbound n x)
  change Tendsto (fun x => ∑' n, primeShiftNoetherCurrent S T n x) atTop (𝓝 0)
  simpa only [tsum_zero] using h

/-- Every arithmetic current is the real positive-source link integral. -/
theorem primeShiftNoetherCurrent_eq_real (S T : ThetaSource) (n : ℕ) (x : ℝ) :
    primeShiftNoetherCurrent S T n x =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        ∫ y in x..x + Real.log n, S.k y * T.k (y - Real.log n) : ℝ) : ℂ) := by
  simp only [primeShiftNoetherCurrent, primeCoefficient_eq, primeShiftLinkDensity,
    ← Complex.ofReal_mul, intervalIntegral.integral_ofReal]

theorem primeShiftNoetherCurrent_re_nonneg (S T : ThetaSource) (n : ℕ) (x : ℝ) :
    0 ≤ (primeShiftNoetherCurrent S T n x).re := by
  rw [primeShiftNoetherCurrent_eq_real, Complex.ofReal_re]
  apply mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  exact intervalIntegral.integral_nonneg_of_forall
    (le_add_of_nonneg_right (Real.log_natCast_nonneg n))
    (fun y => (mul_pos (S.pos y) (T.pos (y - Real.log n))).le)

theorem primeShiftNoetherCurrent_two_re_pos (S T : ThetaSource) (x : ℝ) :
    0 < (primeShiftNoetherCurrent S T 2 x).re := by
  rw [primeShiftNoetherCurrent_eq_real, Complex.ofReal_re,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  apply mul_pos (div_pos hl (Real.sqrt_pos.mpr zero_lt_two))
  exact intervalIntegral.intervalIntegral_pos_of_pos
    ((S.cont.mul (T.cont.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _)
    (fun y => mul_pos (S.pos y) (T.pos (y - Real.log 2))) (lt_add_of_pos_right x hl)

/-- The complete current has strictly positive real part at every finite point. -/
theorem fullPrimeShiftNoetherCurrent_re_pos (S T : ThetaSource) (x : ℝ) :
    0 < (fullPrimeShiftNoetherCurrent S T x).re := by
  have hs := summable_primeShiftNoetherCurrent S T x
  rw [fullPrimeShiftNoetherCurrent, Complex.re_tsum hs]
  exact (Complex.hasSum_re hs.hasSum).summable.tsum_pos
    (fun n => primeShiftNoetherCurrent_re_nonneg S T n x) 2
    (primeShiftNoetherCurrent_two_re_pos S T x)

theorem fullPrimeShiftNoetherCurrent_im (S T : ThetaSource) (x : ℝ) :
    (fullPrimeShiftNoetherCurrent S T x).im = 0 := by
  rw [fullPrimeShiftNoetherCurrent,
    Complex.im_tsum (summable_primeShiftNoetherCurrent S T x)]
  simp only [primeShiftNoetherCurrent_eq_real, Complex.ofReal_im, tsum_zero]

/-- The literal Gamma/pole and multiplication exchange accumulates exactly the prime charge. -/
theorem completeTheta_primeShiftNoether_boundary :
    Tendsto (fun x : ℝ => ∫ y in (0 : ℝ)..x,
      2 * (y : ℂ) * (thetaCuspFullSource y : ℂ) ^ 2 -
        (thetaCuspFullSource y : ℂ) *
          (thetaArchimedeanShiftSource y - thetaArchimedeanShiftSource (-y)))
      atTop (𝓝 (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0)) := by
  have he (x : ℝ) : (∫ y in (0 : ℝ)..x,
      2 * (y : ℂ) * (thetaCuspFullSource y : ℂ) ^ 2 -
        (thetaCuspFullSource y : ℂ) *
          (thetaArchimedeanShiftSource y - thetaArchimedeanShiftSource (-y))) =
      fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0 -
        fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource x := by
    have hc := completeTheta_primeShiftNoether_conservation x
    have hf (y : ℝ) :
        2 * (y : ℂ) * (thetaCuspFullSource y : ℂ) ^ 2 -
          (thetaCuspFullSource y : ℂ) *
            (thetaArchimedeanShiftSource y - thetaArchimedeanShiftSource (-y)) =
        -((thetaCuspFullSource y : ℂ) *
          (thetaArchimedeanShiftSource y - thetaArchimedeanShiftSource (-y)) -
            2 * (y : ℂ) * (thetaCuspFullSource y : ℂ) ^ 2) := by ring
    simp only [hf]
    rw [intervalIntegral.integral_neg]
    linear_combination hc
  simpa only [he, sub_zero] using
    (tendsto_fullPrimeShiftNoetherCurrent_atTop thetaCuspTiltSource thetaCuspTiltSource).const_sub
      (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0)

end RHTower.ThetaSourceWard
