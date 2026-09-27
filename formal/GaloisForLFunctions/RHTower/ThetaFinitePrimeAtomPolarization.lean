import GaloisForLFunctions.RHTower.ThetaPrimeSensitivePolarization
import GaloisForLFunctions.RHTower.ThetaRealTranslatedCoercivity

/-!
# Finite arithmetic cross interaction in physical ground mass

Ordered compact profiles have an exact finite prime-correlation difference
whenever their active translations lie in a specified finite set. Each shift
pairing is bounded by half the sum of the physical masses. Thus the complete
prime correction is controlled by the actual sum of critical von Mangoldt
weights, with no exclusion of active prime powers.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap BigOperators

namespace RHTower.ThetaSourceWard

def thetaGroundShiftCross (phi psi : 𝓢(ℝ, ℝ)) (h : ℝ) : ℝ :=
  ∫ x : ℝ, (thetaCuspFullSource x * phi x) *
    (thetaCuspFullSource (x + h) * psi (x + h))

theorem integrable_thetaGroundShiftCross (phi psi : 𝓢(ℝ, ℝ))
    (hc : HasCompactSupport phi) (h : ℝ) :
    Integrable (fun x : ℝ => (thetaCuspFullSource x * phi x) *
      (thetaCuspFullSource (x + h) * psi (x + h))) := by
  have hk := contDiff_thetaCuspFullSource.continuous
  have hleft : HasCompactSupport (fun x => thetaCuspFullSource x * phi x) := hc.mul_left
  exact ((hk.mul phi.continuous).mul
    ((hk.mul psi.continuous).comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hleft.mul_right

theorem abs_thetaGroundShiftCross_le_mass (phi psi : 𝓢(ℝ, ℝ))
    (hc : HasCompactSupport phi) (h : ℝ) :
    |thetaGroundShiftCross phi psi h| ≤
      (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) / 2 := by
  have hi := integrable_thetaGroundShiftCross phi psi hc h
  have hp := integrable_thetaGroundNormDensity (thetaComplexify phi)
  have hq := (integrable_thetaGroundNormDensity (thetaComplexify psi)).comp_add_right h
  have hle := integral_mono (hi.abs.const_mul 2) (hp.fun_add hq) (fun x => by
    simp only [thetaGroundNormDensity, thetaComplexify_apply, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [abs_mul]
    nlinarith [sq_nonneg (|thetaCuspFullSource x * phi x| -
      |thetaCuspFullSource (x + h) * psi (x + h)|),
      sq_abs (thetaCuspFullSource x * phi x),
      sq_abs (thetaCuspFullSource (x + h) * psi (x + h))])
  rw [integral_const_mul, integral_add hp hq,
    integral_add_right_eq_self (thetaGroundNormDensity (thetaComplexify psi)) h] at hle
  have habs : |thetaGroundShiftCross phi psi h| ≤
      ∫ x : ℝ, |(thetaCuspFullSource x * phi x) *
        (thetaCuspFullSource (x + h) * psi (x + h))| := abs_integral_le_integral_abs
  change 2 * _ ≤ thetaGroundNormSq (thetaComplexify phi) +
    thetaGroundNormSq (thetaComplexify psi) at hle
  linarith

/-- The full prime difference is the finite sum of its actual active shifts. -/
theorem thetaPrimeScalingCross_difference_eq_finite
    (phi psi : 𝓢(ℝ, ℝ)) (S : Finset ℕ)
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hactive : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, IsPrimePow n → x - y = Real.log n → n ∈ S) :
    thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction =
      ∑ n ∈ S, 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        thetaGroundShiftCross phi psi (Real.log n) := by
  let F (p : ℕ × ℝ) := thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
      (thetaComplexify (phi + psi)).toBoundedContinuousFunction p -
    thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
      (thetaComplexify (phi - psi)).toBoundedContinuousFunction p
  have hi : Integrable F thetaPrimeLinkMeasure :=
    (integrable_thetaPrimeScalingCrossDensity _ _ _).sub
      (integrable_thetaPrimeScalingCrossDensity _ _ _)
  have hpoint (n : ℕ) (x : ℝ) : F (n, x) =
      2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((thetaCuspFullSource x * phi x) *
          (thetaCuspFullSource (x + Real.log n) * psi (x + Real.log n))) := by
    have hlog : 0 ≤ Real.log n := by
      by_cases hn : n = 0
      · simp [hn]
      exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have hreverse : phi (x + Real.log n) * psi x = 0 := by
      by_cases hp : phi (x + Real.log n) = 0
      · simp [hp]
      by_cases hq : psi x = 0
      · simp [hq]
      have h := hsep x hq (x + Real.log n) hp
      linarith
    simp only [F, thetaPrimeScalingCrossDensity, thetaPrimeLinkDensity_eq_real,
      SchwartzMap.toBoundedContinuousFunction_apply, thetaComplexify_apply, add_apply,
      sub_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
      thetaCuspTiltSource_k]
    linear_combination 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      thetaCuspFullSource x * thetaCuspFullSource (x + Real.log n) * hreverse
  have hrow (n : ℕ) : (∫ x : ℝ, F (n, x)) =
      2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        thetaGroundShiftCross phi psi (Real.log n) := by
    simp_rw [hpoint]
    exact integral_const_mul _ _
  have hout (n : ℕ) (hn : n ∉ S) : (∫ x : ℝ, F (n, x)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with x
    rw [hpoint]
    by_cases hw : ArithmeticFunction.vonMangoldt n = 0
    · simp [hw]
    by_cases hp : phi x = 0
    · simp [hp]
    by_cases hq : psi (x + Real.log n) = 0
    · simp [hq]
    exact False.elim (hn (hactive _ hq _ hp n
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hw) (by ring)))
  unfold thetaPrimeScalingCross
  rw [← integral_sub (integrable_thetaPrimeScalingCrossDensity _ _ _)
    (integrable_thetaPrimeScalingCrossDensity _ _ _)]
  change (∫ p, F p ∂thetaPrimeLinkMeasure) = _
  rw [integral_prod _ hi, integral_countable hi.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rw [tsum_eq_sum (s := S) hout]
  exact Finset.sum_congr rfl (fun n _ => hrow n)

theorem abs_thetaPrimeScalingCross_difference_le_finite_mass
    (phi psi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi) (S : Finset ℕ)
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hactive : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, IsPrimePow n → x - y = Real.log n → n ∈ S) :
    |thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction| ≤
      (∑ n ∈ S, ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  rw [thetaPrimeScalingCross_difference_eq_finite phi psi S hsep hactive, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg (mul_nonneg (by positivity) hw)]
  have h := mul_le_mul_of_nonneg_left (abs_thetaGroundShiftCross_le_mass phi psi hc (Real.log n))
    (mul_nonneg (show (0 : ℝ) ≤ 2 by positivity) hw)
  linarith only [h]

end RHTower.ThetaSourceWard
