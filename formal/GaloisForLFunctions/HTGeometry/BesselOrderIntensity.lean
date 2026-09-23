import GaloisForLFunctions.HTGeometry.BesselOrderFactorialGrowth
import GaloisForLFunctions.HTGeometry.BesselOrderIntensityShift
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence

/-!
# Modified-Bessel order intensity

This file joins the analytic Schlaefli carrier to the algebraic and growth interfaces:

* the actual fixed-argument `K` carrier satisfies the affine order recurrence;
* its reflected intensity is entire and has the explicit order-three scalar annihilator;
* on the physical line `1 + iτ`, the reflected product is exactly the squared modulus;
* real-order values and intensities have the factorial lower bounds used in the
  hypertranscendence argument.
-/

open Filter
open scoped ComplexConjugate

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- Reflected order intensity `K_ν(s) K_{ν-2}(s)`. -/
def modifiedBesselOrderIntensity (s : ℝ) (ν : ℂ) : ℂ :=
  modifiedBesselKOrder s ν * modifiedBesselKOrder s (ν - 2)

theorem differentiable_modifiedBesselOrderIntensity {s : ℝ} (hs : 0 < s) :
    Differentiable ℂ (modifiedBesselOrderIntensity s) := by
  have hK := differentiable_modifiedBesselKOrder hs
  unfold modifiedBesselOrderIntensity
  fun_prop

/-- The reflected intensity is entire in complex order. -/
theorem analyticOnNhd_modifiedBesselOrderIntensity {s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (modifiedBesselOrderIntensity s) Set.univ :=
  (differentiable_modifiedBesselOrderIntensity hs).differentiableOn.analyticOnNhd
    isOpen_univ

/-- On `ν = 1 + iτ`, reflection and conjugation identify the reflected product with
the squared modulus. -/
theorem modifiedBesselOrderIntensity_one_add_mul_I (s τ : ℝ) :
    modifiedBesselOrderIntensity s (1 + (τ : ℂ) * Complex.I) =
      (Complex.normSq (modifiedBesselKOrder s (1 + (τ : ℂ) * Complex.I)) : ℂ) := by
  let ν : ℂ := 1 + (τ : ℂ) * Complex.I
  have harg : -(ν - 2) = conj ν := by
    simp [ν]
    ring
  have href := modifiedBesselKOrder_neg s (ν - 2)
  rw [harg, modifiedBesselKOrder_conj] at href
  change modifiedBesselKOrder s ν * modifiedBesselKOrder s (ν - 2) = _
  rw [← href]
  exact Complex.mul_conj _

/-- The actual Schlaefli carrier satisfies the affine recurrence with coefficient `2/s`. -/
theorem modifiedBesselKOrder_affineOrderShiftRecurrence
    {s : ℝ} (hs : 0 < s) :
    AffineOrderShiftRecurrence (2 / (s : ℂ)) (modifiedBesselKOrder s) := by
  intro ν
  rw [modifiedBesselKOrder_add_one hs]
  ring

/-- Explicit scalar shift annihilator for the actual reflected Bessel intensity. -/
theorem modifiedBesselOrderIntensity_scalar_annihilator
    {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    ∑ j : Fin 4,
      orderShiftIntensityCoeff (2 / (s : ℂ)) ν j *
        modifiedBesselOrderIntensity s (ν + (j : ℕ)) = 0 := by
  simpa only [modifiedBesselOrderIntensity, orderShiftIntensity] using
    orderShiftIntensity_scalar_annihilator
      (modifiedBesselKOrder_affineOrderShiftRecurrence hs) ν

theorem modifiedBesselOrderIntensityCoeffPoly_zero_ne_zero
    {s : ℝ} (hs : 0 < s) :
    orderShiftIntensityCoeffPoly (2 / (s : ℂ)) 0 ≠ 0 := by
  apply orderShiftIntensityCoeffPoly_zero_ne_zero
  exact div_ne_zero (by norm_num) (by exact_mod_cast hs.ne')

theorem modifiedBesselOrderIntensityCoeffPoly_three_ne_zero
    {s : ℝ} (hs : 0 < s) :
    orderShiftIntensityCoeffPoly (2 / (s : ℂ)) 3 ≠ 0 := by
  apply orderShiftIntensityCoeffPoly_three_ne_zero
  exact div_ne_zero (by norm_num) (by exact_mod_cast hs.ne')

/-- Real form of the exact Bessel order recurrence. -/
theorem realModifiedBesselKOrder_realAffineOrderShiftRecurrence
    {s : ℝ} (hs : 0 < s) :
    RealAffineOrderShiftRecurrence (2 / s) (realModifiedBesselKOrder s) := by
  intro x
  have h := modifiedBesselKOrder_add_one hs (x : ℂ)
  have hp : ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  have hm : ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hp, hm, modifiedBesselKOrder_ofReal hs, modifiedBesselKOrder_ofReal hs,
    modifiedBesselKOrder_ofReal hs] at h
  have hr : realModifiedBesselKOrder s (x + 1) =
      realModifiedBesselKOrder s (x - 1) +
        (2 * x / s) * realModifiedBesselKOrder s x := by
    exact_mod_cast h
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hr

/-- Formula `(10)`: exact rising-product lower bound for every positive starting order. -/
theorem realModifiedBesselKOrder_risingProduct_lower
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    realModifiedBesselKOrder s x * (2 / s) ^ N * realOrderRisingProduct x N <
      realModifiedBesselKOrder s (x + N) :=
  realAffineOrderShiftRecurrence_factorial_lower
    (realModifiedBesselKOrder_realAffineOrderShiftRecurrence hs)
    (realModifiedBesselKOrder_pos hs) (div_pos (by norm_num) hs) hx hN

/-- Formula `(10)` with the rising product weakened to `N!`. -/
theorem realModifiedBesselKOrder_factorial_lower
    {s x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) {N : ℕ} (hN : 1 ≤ N) :
    realModifiedBesselKOrder s x * (2 / s) ^ N * (N.factorial : ℝ) <
      realModifiedBesselKOrder s (x + N) :=
  realAffineOrderShiftRecurrence_factorial_lower'
    (realModifiedBesselKOrder_realAffineOrderShiftRecurrence hs)
    (realModifiedBesselKOrder_pos hs) (div_pos (by norm_num) hs) hx hN

/-- Formula `(11)`: the reflected real intensity has a factorial-squared lower bound. -/
theorem realModifiedBesselOrderIntensity_factorialSq_lower
    {s x : ℝ} (hs : 0 < s) (hx : 3 ≤ x) {N : ℕ} (hN : 1 ≤ N) :
    (realModifiedBesselKOrder s x * realModifiedBesselKOrder s (x - 2)) *
        (2 / s) ^ (2 * N) * (N.factorial : ℝ) ^ (2 : ℕ) <
      realModifiedBesselKOrder s (x + N) *
        realModifiedBesselKOrder s (x - 2 + N) := by
  exact mul_realAffineOrderShiftRecurrence_factorial_lower
    (realModifiedBesselKOrder_realAffineOrderShiftRecurrence hs)
    (realModifiedBesselKOrder_realAffineOrderShiftRecurrence hs)
    (realModifiedBesselKOrder_pos hs) (realModifiedBesselKOrder_pos hs)
    (div_pos (by norm_num) hs) (by linarith) (by linarith) hN

/-- No polynomial-times-exponential upper envelope can hold on a positive integer-order ray. -/
theorem realModifiedBesselKOrder_not_eventually_polynomialExponential_upper
    {s x C A : ℝ} (hs : 0 < s) (hx : 1 ≤ x) (hC : 0 < C) (hA : 0 < A)
    (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop,
      realModifiedBesselKOrder s (x + n) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n) := by
  exact not_eventually_polynomial_exponential_upper_of_factorial_lower
    (g := fun n => realModifiedBesselKOrder s (x + n))
    (realModifiedBesselKOrder_pos hs x) (div_pos (by norm_num) hs)
    (fun n hn => realModifiedBesselKOrder_factorial_lower hs hx hn) hC hA d

/-- No polynomial-times-exponential upper envelope can hold after sampling a positive integer
period. -/
theorem realModifiedBesselKOrder_not_eventually_polynomialExponential_upper_multiple
    {s x C A : ℝ} (hs : 0 < s) (hx : 1 ≤ x)
    {ell : ℕ} (hell : 1 ≤ ell) (hC : 0 < C) (hA : 0 < A) (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop,
      realModifiedBesselKOrder s (x + (ell * n : ℕ)) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n) := by
  exact not_eventually_polynomial_exponential_upper_of_factorial_lower_multiple
    (g := fun n => realModifiedBesselKOrder s (x + (ell * n : ℕ)))
    (realModifiedBesselKOrder_pos hs x) (div_pos (by norm_num) hs) hell
    (fun n hn => realModifiedBesselKOrder_factorial_lower hs hx
      (by exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
        (Nat.one_le_iff_ne_zero.mp hell) (Nat.one_le_iff_ne_zero.mp hn))))
    hC hA d

/-- The reflected real intensity likewise admits no polynomial-times-exponential upper envelope. -/
theorem realModifiedBesselOrderIntensity_not_eventually_polynomialExponential_upper
    {s x C A : ℝ} (hs : 0 < s) (hx : 3 ≤ x) (hC : 0 < C) (hA : 0 < A)
    (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop,
      realModifiedBesselKOrder s (x + n) *
          realModifiedBesselKOrder s (x - 2 + n) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n) := by
  let c : ℝ := (2 / s) ^ (2 : ℕ)
  have hc : 0 < c := pow_pos (div_pos (by norm_num) hs) 2
  have hy₀ : 0 < realModifiedBesselKOrder s x * realModifiedBesselKOrder s (x - 2) :=
    mul_pos (realModifiedBesselKOrder_pos hs x)
      (realModifiedBesselKOrder_pos hs (x - 2))
  exact not_eventually_polynomial_exponential_upper_of_factorial_lower
    (g := fun n => realModifiedBesselKOrder s (x + n) *
      realModifiedBesselKOrder s (x - 2 + n)) hy₀ hc (by
        intro n hn
        have hsq := realModifiedBesselOrderIntensity_factorialSq_lower hs hx hn
        have hfac : (n.factorial : ℝ) ≤ (n.factorial : ℝ) ^ (2 : ℕ) := by
          have h1 : (1 : ℝ) ≤ n.factorial := by
            have hnpos := Nat.factorial_pos n
            exact_mod_cast hnpos
          nlinarith
        refine lt_of_le_of_lt ?_ hsq
        dsimp [c]
        rw [← pow_mul]
        exact mul_le_mul_of_nonneg_left hfac
          (mul_nonneg hy₀.le
            (pow_nonneg (div_pos (by norm_num) hs).le (2 * n)))) hC hA d

/-- The reflected intensity also excludes polynomial-times-exponential growth on every positive
integer-period progression. -/
theorem realModifiedBesselOrderIntensity_not_eventually_polynomialExponential_upper_multiple
    {s x C A : ℝ} (hs : 0 < s) (hx : 3 ≤ x)
    {ell : ℕ} (hell : 1 ≤ ell) (hC : 0 < C) (hA : 0 < A) (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop,
      realModifiedBesselKOrder s (x + (ell * n : ℕ)) *
          realModifiedBesselKOrder s (x - 2 + (ell * n : ℕ)) ≤
        C * ((n : ℝ) + 1) ^ d * A ^ n) := by
  let c : ℝ := (2 / s) ^ (2 : ℕ)
  have hc : 0 < c := pow_pos (div_pos (by norm_num) hs) 2
  have hy₀ : 0 < realModifiedBesselKOrder s x * realModifiedBesselKOrder s (x - 2) :=
    mul_pos (realModifiedBesselKOrder_pos hs x)
      (realModifiedBesselKOrder_pos hs (x - 2))
  exact not_eventually_polynomial_exponential_upper_of_factorial_lower_multiple
    (g := fun n => realModifiedBesselKOrder s (x + (ell * n : ℕ)) *
      realModifiedBesselKOrder s (x - 2 + (ell * n : ℕ))) hy₀ hc hell (by
        intro n hn
        have hN : 1 ≤ ell * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
          (Nat.one_le_iff_ne_zero.mp hell) (Nat.one_le_iff_ne_zero.mp hn))
        have hsq := realModifiedBesselOrderIntensity_factorialSq_lower hs hx hN
        have hfac : (((ell * n).factorial : ℝ)) ≤
            ((ell * n).factorial : ℝ) ^ (2 : ℕ) := by
          have h1 : (1 : ℝ) ≤ (ell * n).factorial := by
            exact_mod_cast Nat.factorial_pos (ell * n)
          nlinarith
        refine lt_of_le_of_lt ?_ hsq
        dsimp [c]
        rw [← pow_mul]
        exact mul_le_mul_of_nonneg_left hfac
          (mul_nonneg hy₀.le
            (pow_nonneg (div_pos (by norm_num) hs).le (2 * (ell * n)))))
    hC hA d

end

end HTGeometry
end GaloisForLFunctions
