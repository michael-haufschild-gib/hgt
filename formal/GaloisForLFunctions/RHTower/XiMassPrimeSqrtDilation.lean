import GaloisForLFunctions.RHTower.XiMassPrimeMaskL1Quotient

/-!
# The square-root prime mask as a half dilation of the prime-square layer

The square-root mask `m(p) = Λ(p²) p^{-1} / (Λ(p) p^{-1/2}) = p^{-1/2}` reweights the prime atom
`Λ(p) p^{-1/2} ĝ(log p)` into the boundary term `Λ(p²) p^{-1} ĝ(log p)`. The mass test obeys the
half-dilation law `g_{a,τ}(x) = g_{a/2, 2τ}(x/2)`, so `ĝ_{a,τ}(w) = 2 ĝ_{a/2, 2τ}(2w)`, and since
`log p² = 2 log p` each boundary term is twice the centered atom at `p²` for the parameters
`(a/2, 2τ)`. Hence the square-root-masked prime layer at `(a, τ)` is exactly twice the
prime-square layer at `(a/2, 2τ)`.

## Main results

- `stripFourier_xiMassAnalyticTest_half_dilation`: `ĝ_{a,τ}(w) = 2 ĝ_{a/2, 2τ}(2w)` for `a > 0`.
- `xiMassPrimeSqrtMaskLayer_eq_boundaryLayer`: the masked layer equals
  `∑_p Λ(p²) p^{-1} ĝ(log p)`.
- `xiMassPrimeSqrtMaskLayer_eq_two_mul_primeSquareLayer`: the masked layer at `(a, τ)` equals
  `2 ·` prime-square layer at `(a/2, 2τ)`.

## Hypotheses

All results are unconditional; the dilation identities need only `0 < a`.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower


noncomputable section

/-- Half-dilation law of the mass test on the real line: for `a > 0`,
`g_{a,τ}(x) = g_{a/2, 2τ}(x/2)`. -/
theorem xiMassAnalyticTest_real_half_dilation
    {a : ℝ} (ha : 0 < a) (τ : ℂ) (x : ℝ) :
    xiMassAnalyticTest a τ (x : ℂ) =
      xiMassAnalyticTest (a / 2) (2 * τ) ((x / 2 : ℝ) : ℂ) := by
  have ha2 : 0 < a / 2 := by positivity
  rw [xiMassAnalyticTest, xiMassAnalyticTest,
    xiMassAnalyticSqrt_ofReal_eq ha,
    xiMassAnalyticSqrt_ofReal_eq ha2]
  have hbig : 0 ≤ x ^ (2 : ℕ) + a ^ (2 : ℕ) := by positivity
  have hsmall : 0 ≤ (x / 2) ^ (2 : ℕ) + (a / 2) ^ (2 : ℕ) := by positivity
  have hscale : (x / 2) ^ (2 : ℕ) + (a / 2) ^ (2 : ℕ) =
      (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / 4 := by ring
  have hsqBig := Real.sq_sqrt hbig
  have hsqSmall := Real.sq_sqrt hsmall
  have hsqrt : Real.sqrt ((x / 2) ^ (2 : ℕ) + (a / 2) ^ (2 : ℕ)) =
      Real.sqrt (x ^ (2 : ℕ) + a ^ (2 : ℕ)) / 2 := by
    nlinarith [Real.sqrt_nonneg (x ^ (2 : ℕ) + a ^ (2 : ℕ)),
      Real.sqrt_nonneg ((x / 2) ^ (2 : ℕ) + (a / 2) ^ (2 : ℕ))]
  rw [hsqrt]
  congr 1
  push_cast
  ring

/-- Fourier form of the half dilation: for `a > 0`, `ĝ_{a,τ}(w) = 2 ĝ_{a/2, 2τ}(2w)`. -/
theorem stripFourier_xiMassAnalyticTest_half_dilation
    {a : ℝ} (ha : 0 < a) (τ w : ℂ) :
    stripFourier (xiMassAnalyticTest a τ) w =
      2 * stripFourier (xiMassAnalyticTest (a / 2) (2 * τ)) (2 * w) := by
  unfold stripFourier
  let G : ℝ → ℂ := fun y =>
    xiMassAnalyticTest (a / 2) (2 * τ) (y : ℂ) *
      Complex.exp (-(I * (2 * w) * (y : ℂ)))
  have hpoint (x : ℝ) :
      xiMassAnalyticTest a τ (x : ℂ) *
          Complex.exp (-(I * w * (x : ℂ))) =
        G ((1 / 2 : ℝ) * x) := by
    rw [xiMassAnalyticTest_real_half_dilation ha τ x]
    dsimp only [G]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [show (∫ x : ℝ, xiMassAnalyticTest a τ (x : ℂ) *
        Complex.exp (-(I * w * (x : ℂ)))) =
      ∫ x : ℝ, G ((1 / 2 : ℝ) * x) by
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.Measure.integral_comp_mul_left G (1 / 2)]
  norm_num [G, Complex.real_smul]

/-- The square-root prime mask: ratio of the critical von Mangoldt terms at `p²` and at `p`,
equal to `p^{-1/2}`. -/
def xiMassPrimeSqrtMask (p : Nat.Primes) : ℂ :=
  LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) /
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (1 / 2 : ℂ) (p : ℕ)

/-- The prime layer masked by the square-root mask. -/
def xiMassPrimeSqrtMaskLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    xiMassPrimeSqrtMask p * xiMassCenteredPrimeAtom a τ (p : ℕ)

/-- Boundary layer `∑_p Λ(p²) p^{-1} ĝ(log p)`: square weights at prime frequencies. -/
def xiMassPrimeSqrtBoundaryLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) *
      stripFourier (xiMassAnalyticTest a τ) (Real.log (p : ℕ) : ℂ)

/-- The critical von Mangoldt term `Λ(p) p^{-1/2}` of a prime is nonzero. -/
theorem xiMassPrimeCriticalTerm_ne_zero (p : Nat.Primes) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (1 / 2 : ℂ) (p : ℕ) ≠ 0 := by
  rw [LSeries.term_of_ne_zero p.prop.ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  exact div_ne_zero
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (by exact_mod_cast p.prop.one_lt))))
    (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast p.prop.ne_zero)))

lemma div_mul_mul_eq_mul {a b c : ℂ} (hb : b ≠ 0) :
    (a / b) * (b * c) = a * c := by
  field_simp

theorem xiMassPrimeSqrtMask_mul_centeredAtom_eq_boundaryTerm
    (a : ℝ) (τ : ℂ) (p : Nat.Primes) :
    xiMassPrimeSqrtMask p * xiMassCenteredPrimeAtom a τ (p : ℕ) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) *
        stripFourier (xiMassAnalyticTest a τ) (Real.log (p : ℕ) : ℂ) := by
  unfold xiMassPrimeSqrtMask xiMassCenteredPrimeAtom
  exact div_mul_mul_eq_mul (xiMassPrimeCriticalTerm_ne_zero p)

/-- The square-root-masked prime layer equals the boundary layer `∑_p Λ(p²) p^{-1} ĝ(log p)`. -/
theorem xiMassPrimeSqrtMaskLayer_eq_boundaryLayer (a : ℝ) (τ : ℂ) :
    xiMassPrimeSqrtMaskLayer a τ = xiMassPrimeSqrtBoundaryLayer a τ := by
  unfold xiMassPrimeSqrtMaskLayer xiMassPrimeSqrtBoundaryLayer
  exact tsum_congr (xiMassPrimeSqrtMask_mul_centeredAtom_eq_boundaryTerm a τ)

/-- For `a > 0`, each boundary term `Λ(p²) p^{-1} ĝ_{a,τ}(log p)` is twice the centered atom
at `p²` for the parameters `(a/2, 2τ)`. -/
theorem xiMassPrimeSqrtBoundaryTerm_eq_two_mul_squareAtom
    {a : ℝ} (ha : 0 < a) (τ : ℂ) (p : Nat.Primes) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) *
      stripFourier (xiMassAnalyticTest a τ) (Real.log (p : ℕ) : ℂ) =
      2 * xiMassCenteredPrimeAtom (a / 2) (2 * τ) ((p : ℕ) ^ (2 : ℕ)) := by
  have hF := stripFourier_xiMassAnalyticTest_half_dilation
    ha τ (Real.log (p : ℕ) : ℂ)
  have hlogpow : Real.log (((p : ℕ) ^ (2 : ℕ) : ℕ) : ℝ) =
      2 * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogpowC :
      (Real.log (((p : ℕ) ^ (2 : ℕ) : ℕ) : ℝ) : ℂ) =
        2 * (Real.log (p : ℝ) : ℂ) := by
    exact_mod_cast hlogpow
  unfold xiMassCenteredPrimeAtom
  calc
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) *
        stripFourier (xiMassAnalyticTest a τ)
          (Real.log (p : ℕ) : ℂ) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) * (2 * stripFourier
        (xiMassAnalyticTest (a / 2) (2 * τ))
          (2 * (Real.log (p : ℕ) : ℂ))) := by rw [hF]
    _ = 2 * (LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 / 2 : ℂ) ((p : ℕ) ^ (2 : ℕ)) * stripFourier
        (xiMassAnalyticTest (a / 2) (2 * τ))
          (Real.log ((((p : ℕ) ^ (2 : ℕ) : ℕ) : ℝ)) : ℂ)) := by
      rw [hlogpowC]
      ring

/-- For `a > 0`, the square-root-masked prime layer at `(a, τ)` is twice the prime-square layer
at `(a/2, 2τ)`. -/
theorem xiMassPrimeSqrtMaskLayer_eq_two_mul_primeSquareLayer
    {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    xiMassPrimeSqrtMaskLayer a τ =
      2 * xiMassPrimeSquareLayer (a / 2) (2 * τ) := by
  rw [xiMassPrimeSqrtMaskLayer_eq_boundaryLayer]
  unfold xiMassPrimeSqrtBoundaryLayer xiMassPrimeSquareLayer
  rw [← tsum_mul_left]
  exact tsum_congr (xiMassPrimeSqrtBoundaryTerm_eq_two_mul_squareAtom ha τ)

theorem norm_xiMassPrimeSqrtMaskLayer_eq_two_mul_primeSquareLayer
    {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    ‖xiMassPrimeSqrtMaskLayer a τ‖ =
      2 * ‖xiMassPrimeSquareLayer (a / 2) (2 * τ)‖ := by
  rw [xiMassPrimeSqrtMaskLayer_eq_two_mul_primeSquareLayer ha, norm_mul]
  norm_num

end

end RHTower
