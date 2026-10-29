import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.PrimeFlipTail
import GaloisForLFunctions.ArithmeticCountingPositivity.NearMaximalGapsDoNotForceWeilPositivity
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane

/-!
# The prime-square correction in the actual complete Weil form

At separated atom widths the sign conjugacy changes only the prime matrix.
The Gamma term and both pole terms are identical on the two sides, so the
finite arithmetic correction transfers without discarding any analytic term.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
  ArithmeticCountingPositivity SelectiveMultiscaleArithmeticPositivity SpacingScaleHarmonicAnalysis

/-- The single-prime sign as an arithmetic function, with its required zero value at zero. -/
def singlePrimeGauge (p : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else finiteFlip {p} n, by simp⟩

theorem singlePrimeGauge_apply {n : ℕ} (p : ℕ) (hn : n ≠ 0) :
    singlePrimeGauge p n = finiteFlip {p} n := by
  change (if n = 0 then 0 else finiteFlip {p} n) = _
  rw [if_neg hn]

theorem singlePrimeGauge_mul (p a b : ℕ) :
    singlePrimeGauge p (a * b) = singlePrimeGauge p a * singlePrimeGauge p b := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_mul, ArithmeticFunction.map_zero]
  · by_cases hb : b = 0
    · subst b
      simp only [mul_zero, ArithmeticFunction.map_zero]
    · rw [singlePrimeGauge_apply p (mul_ne_zero ha hb), singlePrimeGauge_apply p ha,
        singlePrimeGauge_apply p hb]
      exact (finiteFlip_isSignGauge {p}).mul ha hb

theorem singlePrimeGauge_sign (p n : ℕ) (hn : 0 < n) :
    singlePrimeGauge p n = 1 ∨ singlePrimeGauge p n = -1 := by
  rw [singlePrimeGauge_apply p hn.ne']
  simp only [finiteFlip, prod_singleton]
  exact neg_one_pow_eq_or ℝ (n.factorization p)

theorem singlePrimeGauge_weight (p : ℕ) :
    (fun n => singlePrimeGauge p n * ArithmeticFunction.vonMangoldt n) = primeFlipWeight p := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [primeFlipWeight, ArithmeticFunction.map_zero, mul_zero]
  · rw [singlePrimeGauge_apply p hn, primeFlipWeight]

private theorem singlePrimeGauge_trial (p : ℕ) :
    (fun n => singlePrimeGauge p n * (primeSquareTrial p n / Real.sqrt n)) =
      fun n => finiteFlip {p} n * primeSquareTrial p n / Real.sqrt n := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, mul_zero]
  · rw [singlePrimeGauge_apply p hn]
    ring

/-- Exact transfer from the finite prime correction to the complete functional. -/
theorem primeSquareTrial_complete_correction {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hsep : w < atomSpacing N) (p : ℕ) :
    weilQuadTw (primeFlipWeight p)
        (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n) g) -
      weilQuad (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n) g) =
        (∫ u, g u ^ 2) *
          (atomicWeilForm N (fun n => primeSquareTrial p n / Real.sqrt n) -
            atomicWeilForm N (fun n => finiteFlip {p} n * primeSquareTrial p n / Real.sqrt n)) := by
  have h := weilQuadTw_atomicTest_sub_weilQuad (singlePrimeGauge_mul p)
    (singlePrimeGauge_sign p) hg hgc hsupp hsep
    (fun n => primeSquareTrial p n / Real.sqrt n)
  rw [singlePrimeGauge_weight,
    twistedAtomicWeilForm_eq (singlePrimeGauge_mul p) (singlePrimeGauge_sign p),
    singlePrimeGauge_trial] at h
  exact h

/-- The signed first-prime cancellation bounds the complete twisted form. -/
theorem primeSquareTrial_complete_le {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hsep : w < atomSpacing N) {p : ℕ} (hp : p.Prime) :
    weilQuadTw (primeFlipWeight p)
        (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n) g) ≤
      weilQuad (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n) g) +
        (∫ u, g u ^ 2) * primeSquareFlipBound p N := by
  have heq := primeSquareTrial_complete_correction hg hgc hsupp hsep p
  have hmass : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg (g u)
  have hle := mul_le_mul_of_nonneg_left (primeSquareTrial_prime_correction_le hp N)
    hmass
  change (∫ u, g u ^ 2) * _ ≤ (∫ u, g u ^ 2) * primeSquareFlipBound p N at hle
  linarith only [heq, hle]

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.primeSquareTrial_complete_le
