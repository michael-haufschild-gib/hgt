import GaloisForLFunctions.RHTower.ZetaZeroDirichletPolynomialMoment
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Prime projection in smoothed zero moments

A fixed smooth cutoff discharges the analytic test-function conditions in the
smoothed Landau–Gonek formula. Möbius multiplication leaves a prime-only arithmetic
main term. Removing one and every prime power leaves only the explicit error bound.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section

/-- A fixed smooth cutoff, equal to one near the origin and zero outside `[-1,1]`. -/
def landauBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The real cutoff viewed as a complex test function. -/
def landauProfile (x : ℝ) : ℂ := landauBump x

theorem contDiff_landauProfile : ContDiff ℝ 2 landauProfile :=
  Complex.ofRealCLM.contDiff.comp landauBump.contDiff

theorem landauProfile_zero : landauProfile 0 = 1 := by
  have h : landauBump (0 : ℝ) = 1 := landauBump.one_of_mem_closedBall (by simp [landauBump])
  simp only [landauProfile, h, Complex.ofReal_one]

theorem landauProfile_support : ∀ x, landauProfile x ≠ 0 → |x| ≤ 1 := by
  intro x hx
  by_contra h
  have hb : landauBump x = 0 := landauBump.zero_of_le_dist
    (by simpa [landauBump, Real.dist_eq] using (not_le.mp h).le)
  exact hx (by simp only [landauProfile, hb, Complex.ofReal_zero])

/-- Pointwise Möbius multiplication removes every higher prime power. -/
theorem moebius_mangoldt_prime_filter (n : ℕ) :
    (μ n : ℝ) * vonMangoldt n = if n.Prime then -Real.log n else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp, moebius_apply_prime hp, vonMangoldt_apply_prime hp]
    simp
  · rw [if_neg hp]
    by_cases hz : vonMangoldt n = 0
    · rw [hz, mul_zero]
    · rw [moebius_apply_isPrimePow_not_prime (vonMangoldt_ne_zero_iff.mp hz) hp]
      simp

open Finset
open _root_.RHTower _root_.Zeta23

/-- A finite Dirichlet polynomial averaged over the smoothed zeta-zero divisor. -/
def landauZeroMoment (a : ℕ → ℂ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
    paperFT landauProfile (gammaOf ρ / T) *
      ∑ n ∈ Icc 1 Y, a n * (n : ℂ) ^ (-((ρ : ℂ) - 1 / 2))

/-- The coefficient-weighted error supplied by the smoothed Landau formula. -/
def landauMomentError (a : ℕ → ℂ) (Y : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 Y, ‖a n‖ * (Real.sqrt n + Real.sqrt T)

/-- The prime-only arithmetic signal of a coefficient sequence. -/
def landauPrimeSignal (a : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ n ∈ (Icc 2 Y).filter Nat.Prime, a n * ((Real.log n / Real.sqrt n : ℝ) : ℂ)

/-- Möbius multiplication of the Dirichlet coefficients. -/
def moebiusWeightedCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ := (μ n : ℂ) * a n

/-- The Möbius-weighted Mangoldt signal is exactly the negative prime signal. -/
theorem moebiusWeightedSignal_eq_neg_primeSignal (a : ℕ → ℂ) (Y : ℕ) :
    (∑ n ∈ Icc 2 Y, moebiusWeightedCoeff a n * ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ)) =
      -landauPrimeSignal a Y := by
  rw [landauPrimeSignal, sum_filter, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n _
  have hr : (μ n : ℝ) * (vonMangoldt n / Real.sqrt n) =
      if n.Prime then -(Real.log n / Real.sqrt n) else 0 := by
    rw [← mul_div_assoc, moebius_mangoldt_prime_filter]
    split_ifs <;> simp only [neg_div, zero_div]
  have hc : (μ n : ℂ) * ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) =
      if n.Prime then -((Real.log n / Real.sqrt n : ℝ) : ℂ) else 0 := by
    by_cases hp : n.Prime
    · simp only [if_pos hp] at hr ⊢
      exact_mod_cast hr
    · simp only [if_neg hp] at hr ⊢
      exact_mod_cast hr
  rw [moebiusWeightedCoeff, mul_right_comm, hc]
  split_ifs <;> ring

/-- Smoothed zero moments of Möbius-weighted polynomials have a prime-only main term. -/
theorem exists_moebiusWeightedMoment_le :
    ∃ K : ℝ, ∀ (a : ℕ → ℂ) (Y : ℕ), 1 ≤ Y → ∀ T : ℝ, 2 ≤ T → (Y : ℝ) + 2 ≤ T →
      ‖landauZeroMoment (moebiusWeightedCoeff a) Y T -
        (a 1 * ((T : ℂ) * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst landauProfile) +
          (T : ℂ) * landauPrimeSignal a Y)‖ ≤ K * landauMomentError (moebiusWeightedCoeff a) Y T := by
  obtain ⟨K, hK⟩ := exists_zeroSum_dirichletPolynomial_le contDiff_landauProfile landauProfile_support
  refine ⟨K, fun a Y hY T hT hYT => ?_⟩
  have h := hK (moebiusWeightedCoeff a) Y hY T hT hYT
  simp only [landauProfile_zero, mul_one] at h
  rw [moebiusWeightedSignal_eq_neg_primeSignal] at h
  simpa only [landauZeroMoment, landauMomentError, moebiusWeightedCoeff, moebius_apply_one,
    Int.cast_one, one_mul, mul_neg, sub_neg_eq_add] using h

/-- Remove the coefficient at one and all coefficients at prime powers. -/
def compositeNonPowerCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 1 ∨ IsPrimePow n then 0 else a n

/-- The retained composite coefficients lie in the kernel of the Mangoldt multiplier. -/
theorem compositeNonPowerCoeff_mul_vonMangoldt (a : ℕ → ℂ) (n : ℕ) :
    compositeNonPowerCoeff a n * ((vonMangoldt n / Real.sqrt n : ℝ) : ℂ) = 0 := by
  by_cases h : n = 1 ∨ IsPrimePow n
  · rw [compositeNonPowerCoeff, if_pos h, zero_mul]
  · rw [vonMangoldt_eq_zero_iff.mpr (fun hn => h (Or.inr hn))]
    simp only [zero_div, Complex.ofReal_zero, mul_zero]

/-- The composite non-power part has no arithmetic main term in its smoothed zero moment. -/
theorem exists_compositeNonPowerMoment_le :
    ∃ K : ℝ, ∀ (a : ℕ → ℂ) (Y : ℕ), 1 ≤ Y → ∀ T : ℝ, 2 ≤ T → (Y : ℝ) + 2 ≤ T →
      ‖landauZeroMoment (compositeNonPowerCoeff a) Y T‖ ≤
        K * landauMomentError (compositeNonPowerCoeff a) Y T := by
  obtain ⟨K, hK⟩ := exists_zeroSum_dirichletPolynomial_le contDiff_landauProfile landauProfile_support
  refine ⟨K, fun a Y hY T hT hYT => ?_⟩
  have h := hK (compositeNonPowerCoeff a) Y hY T hT hYT
  have h1 : compositeNonPowerCoeff a 1 = 0 := by
    simp only [compositeNonPowerCoeff, eq_self, true_or, if_true]
  simpa only [landauZeroMoment, landauMomentError, h1, compositeNonPowerCoeff_mul_vonMangoldt, sum_const_zero,
    zero_mul, mul_zero, sub_zero] using h

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
