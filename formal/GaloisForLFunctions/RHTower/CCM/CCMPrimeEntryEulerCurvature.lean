import GaloisForLFunctions.RHTower.CCM.CCMPrimeEntryProductLocalization
import GaloisForLFunctions.RHTower.LocalizedHalfDensityGerm

/-!
# Exact Euler-deformation curvature of the critical prime-pair source

The half-density Euler coefficients have an exact inverse law. Localizing
their product fibres by the actual finite overlap introduces a curvature
term. Its sign is nonnegative, and its complete contribution to the signed
critical energy is identified below, together with the endpoint term.
Positivity supplies a lower estimate; the required upper estimate must
still retain the continuous background and signed mixed work.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

theorem ccmPrimeEntryOverlap_pos {T a b : ℝ} (hzero : 0 ≤ max a b) (hT : max a b < T) :
    0 < ccmPrimeEntryOverlap T a b := by
  have hT0 : 0 < T := hzero.trans_lt hT
  have hc : Continuous (fun t => Real.exp (-t) * ccmPrimeEntryTent a t * ccmPrimeEntryTent b t) := by
    unfold ccmPrimeEntryTent
    fun_prop
  apply intervalIntegral.integral_pos hT0 hc.continuousOn
  · intro t _
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _)) (le_max_right _ _)
  · refine ⟨(max a b + T) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    have ha : 0 < (max a b + T) / 2 - a := by linarith [le_max_left a b]
    have hb : 0 < (max a b + T) / 2 - b := by linarith [le_max_right a b]
    exact mul_pos (mul_pos (Real.exp_pos _) (ha.trans_le (le_max_left _ _)))
      (hb.trans_le (le_max_left _ _))

/-- Separating a product into two nonnegative entry times increases its
finite overlap relative to the endpoint factorization. -/
theorem ccmPrimeEntryOverlap_add_le {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ccmPrimeEntryOverlap T (a + b) 0 ≤ ccmPrimeEntryOverlap T a b := by
  have hi (a b : ℝ) : IntervalIntegrable (fun t =>
      Real.exp (-t) * ccmPrimeEntryTent a t * ccmPrimeEntryTent b t) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold ccmPrimeEntryTent
    fun_prop
  apply intervalIntegral.integral_mono_on hT (hi _ _) (hi _ _)
  intro t ht
  by_cases hab : t ≤ a + b
  · simp only [ccmPrimeEntryTent, max_eq_right (sub_nonpos.mpr hab), mul_zero, zero_mul]
    positivity
  · have hab' : a + b ≤ t := (lt_of_not_ge hab).le
    have hat : a ≤ t := by linarith
    have hbt : b ≤ t := by linarith
    simp only [ccmPrimeEntryTent, sub_zero, max_eq_left (sub_nonneg.mpr hab'),
      max_eq_left (sub_nonneg.mpr hat), max_eq_left (sub_nonneg.mpr hbt),
      max_eq_left ht.1]
    have hp : (t - (a + b)) * t ≤ (t - a) * (t - b) := by nlinarith only [mul_nonneg ha hb]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (Real.exp_pos (-t)).le

def ccmPrimeEntryEulerCurvature (T : ℝ) (R : ℕ) : ℝ :=
  ((1 / 2 : ℂ) * iteratedDeriv 2
    (halfDensityFibre (ccmPrimeEntryProductKernel T R) R) 0).re

/-- Exact response of the existing Euler inverse family to the actual
product-dependent ratio localization. -/
theorem ccmPrimeEntryEulerCurvature_eq (T : ℝ) {R : ℕ} (hR : R ≠ 0) :
    ccmPrimeEntryEulerCurvature T R =
      localizedVonMangoldtPair (ccmPrimeEntryProductKernel T R) R -
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R *
          ccmPrimeEntryOverlap T (Real.log R) 0 := by
  have h := congrArg Complex.re (halfDensityFibre_second_derivative
    (ccmPrimeEntryProductKernel T R) (ccmPrimeEntryProductKernel_even T R) hR)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  change ccmPrimeEntryEulerCurvature T R = _ at h
  have he : ccmPrimeEntryProductKernel T R (Real.log R) =
      ccmPrimeEntryOverlap T (Real.log R) 0 := by
    unfold ccmPrimeEntryProductKernel
    congr 1 <;> ring
  rwa [he] at h

/-- Every individual localized product layer has nonnegative curvature.
This is a surviving source term, so the inverse law alone gives no upper
bound on the full centered energy. -/
theorem ccmPrimeEntryEulerCurvature_nonneg {T : ℝ} (hT : 0 ≤ T) {R : ℕ} (hR : R ≠ 0) :
    0 ≤ ccmPrimeEntryEulerCurvature T R := by
  rw [ccmPrimeEntryEulerCurvature_eq T hR, localizedVonMangoldtPair,
    ArithmeticFunction.mul_apply, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro x hx
  obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hn : 0 < x.1 := by
    by_contra h
    have hz : x.1 = 0 := by omega
    rw [hz, zero_mul] at hprod
    exact hR hprod.symm
  have hm : 0 < x.2 := by
    by_contra h
    have hz : x.2 = 0 := by omega
    rw [hz, mul_zero] at hprod
    exact hR hprod.symm
  have hnR : (1 : ℝ) ≤ x.1 := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ x.2 := by exact_mod_cast hm
  have hlog : Real.log R = Real.log x.1 + Real.log x.2 := by
    rw [← hprod, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  rw [← hprod, ccmPrimeEntryProductKernel_log_ratio T hn hm, hprod, hlog]
  have hk := ccmPrimeEntryOverlap_add_le hT (Real.log_nonneg hnR) (Real.log_nonneg hmR)
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
  exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hk hw)

theorem ccmPrimeEntryPairPrefix_eq_euler_curvature {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryPairPrefix T ⌊Real.exp T⌋₊ =
      ∑ R ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊),
        (ccmPrimeEntryEulerCurvature T R +
          (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R *
            ccmPrimeEntryOverlap T (Real.log R) 0) := by
  rw [ccmPrimeEntryPairPrefix_eq_product_layers hT]
  apply Finset.sum_congr rfl
  intro R hR
  rw [ccmPrimeEntryEulerCurvature_eq T (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hR).1)]
  ring

/-- The complete centered critical energy in Euler-deformation coordinates.
Both signed continuous terms and every arithmetic endpoint remain present. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_eq_euler_curvature {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      Real.exp T - Real.exp (-T) - 2 * T -
        2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
          ∑ R ∈ Finset.Icc 1 (⌊Real.exp T⌋₊ * ⌊Real.exp T⌋₊),
            (ccmPrimeEntryEulerCurvature T R +
              (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) R *
                ccmPrimeEntryOverlap T (Real.log R) 0) := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_pair hT,
    ccmPrimeEntryPairPrefix_eq_euler_curvature hT]

/-- The localized response is strictly positive on every two-prime product
at its product-entry time. The exact Euler inverse law does not annihilate
this actual arithmetic curvature. -/
theorem ccmPrimeEntryEulerCurvature_two_prime_pos {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    0 < ccmPrimeEntryEulerCurvature (Real.log (p * q : ℕ)) (p * q) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlog : Real.log (p * q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul hpR.ne' hqR.ne']
  have hT : 0 ≤ Real.log (p * q : ℕ) := by rw [hlog]; positivity
  rw [ccmPrimeEntryEulerCurvature_eq _ (Nat.mul_ne_zero hp.ne_zero hq.ne_zero),
    ccmPrimeEntryOverlap_eq_zero_of_left_ge hT le_rfl, mul_zero, sub_zero]
  have hpair := localizedVonMangoldtPair_ccmPrimeEntryProductKernel_two_prime
    (Real.log (p * q : ℕ)) hp hq hpq (a := 1) (b := 1) (by norm_num) (by norm_num)
  simp only [pow_one, Nat.cast_one, one_mul] at hpair
  rw [hpair, ccmPrimeEntryProductKernel_log_ratio _ hp.pos hq.pos]
  apply mul_pos (mul_pos (mul_pos (by norm_num) hlp) hlq)
  apply ccmPrimeEntryOverlap_pos (hlp.le.trans (le_max_left _ _))
  rw [hlog]
  exact max_lt (by linarith) (by linarith)

end RHTower
