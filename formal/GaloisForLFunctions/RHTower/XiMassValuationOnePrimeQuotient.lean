import GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue
import GaloisForLFunctions.RHTower.XiMassPrimeOpenCore

/-!
# RH as vertical boundedness of the prime-only mass layer

The valuation-one prime layer is `∑_p Λ(p) p^{-1/2} ĝ(log p)`, the sum of centered mass atoms
over primes only, where `ĝ` is the Fourier transform of the mass test
`exp(-τ √(x² + a²))`. On a legal Euler line the von Mangoldt bottom integral equals this layer
plus the prime-square layer plus the cube-and-higher tail, and the last two are bounded on every
positive vertical line. So boundedness of the bottom integral on `Re τ = σ` is equivalent to
boundedness of the prime layer there, and by the existing equivalence between RH and the bottom
prime line bound, RH is equivalent to the prime layer being bounded on one vertical line.

## Main results

- `xiMassBottomPrimeIntegral_eq_valuationOne_add_square_add_high`: bottom prime integral
  `=` prime layer `+` square layer `+` high tail.
- `xiMassBottomPrimeLineBound_iff_valuationOnePrimeLineBound`: the bottom integral is bounded on
  `Re τ = σ` iff the prime layer is.
- `riemannHypothesis_iff_xiMassValuationOnePrimeLineBound`: `RiemannHypothesis` holds iff
  `u ↦ ∑_p Λ(p) p^{-1/2} ĝ_{a, σ + iu}(log p)` is bounded on `ℝ`.

## Hypotheses

The results are unconditional biconditionals and identities; the line-bound predicates
`XiMassValuationOnePrimeLineBound` and `XiMassBottomPrimeLineBound` appear only as sides of the
equivalences, not as premises. The parameters satisfy `1/2 < c < a` and `0 < σ`
(or `0 < Re τ` for the decomposition).
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The valuation-one prime layer `∑_p Λ(p) p^{-1/2} ĝ(log p)`: centered mass atoms at primes. -/
def xiMassValuationOnePrimeLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ (p : ℕ)

/-- The prime layer is bounded along the vertical line `τ = σ + iu`, `u ∈ ℝ`. -/
def XiMassValuationOnePrimeLineBound (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I)‖ ≤ C

/-- For `1/2 < c < a` and `0 < Re τ`, the von Mangoldt bottom integral is the prime layer plus
the prime-square layer plus the high prime-power tail. -/
theorem xiMassBottomPrimeIntegral_eq_valuationOne_add_square_add_high
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassBottomPrimeIntegral a c τ =
      xiMassValuationOnePrimeLayer a τ +
      xiMassPrimeSquareLayer a τ +
      xiMassHighPrimePowerTail a τ := by
  unfold xiMassBottomPrimeIntegral xiMassValuationOnePrimeLayer
  rw [integral_xiMassBottomPrimeIntegrand_eq_prime_add_square_add_high
    hhalf hca hτ]
  rfl

/-- For `a, σ > 0`, the non-prime remainder (prime-square layer plus high tail) is bounded on
the vertical line `Re τ = σ`. -/
theorem exists_norm_xiMassNonPrimeRemainder_vertical_bound
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
        xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)‖ ≤ B := by
  obtain ⟨B₂, hB₂⟩ := exists_norm_xiMassPrimeSquareLayer_vertical_bound ha hσ
  let Bₕ : ℝ :=
    (∑' pk : Nat.Primes × ℕ,
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) *
        (∫ x : ℝ, Real.exp (-σ * |x|))
  refine ⟨B₂ + Bₕ, fun u => ?_⟩
  calc
    ‖xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
        xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)‖ ≤
      ‖xiMassPrimeSquareLayer a ((σ : ℂ) + u * I)‖ +
        ‖xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)‖ :=
          norm_add_le _ _
    _ ≤ B₂ + Bₕ := add_le_add (hB₂ u)
      (by
        dsimp only [Bₕ]
        simpa only [neg_mul] using
          norm_xiMassHighPrimePowerTail_vertical_le ha hσ u)

/-- For `1/2 < c < a` and `0 < σ`, the bottom prime integral is bounded on `Re τ = σ` iff the
prime layer is, since they differ by a bounded remainder. -/
theorem xiMassBottomPrimeLineBound_iff_valuationOnePrimeLineBound
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    XiMassBottomPrimeLineBound a c σ ↔
      XiMassValuationOnePrimeLineBound a σ := by
  have ha : 0 < a := by linarith
  obtain ⟨B, hB⟩ := exists_norm_xiMassNonPrimeRemainder_vertical_bound ha hσ
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    have hdecomp :=
      xiMassBottomPrimeIntegral_eq_valuationOne_add_square_add_high
        hhalf hca
        (τ := ((σ : ℂ) + u * I)) (by simpa using hσ)
    have heq :
        xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) =
          xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I) -
            (xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
              xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)) := by
      rw [hdecomp]
      ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (hC u) (hB u))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    have hdecomp :=
      xiMassBottomPrimeIntegral_eq_valuationOne_add_square_add_high
        hhalf hca
        (τ := ((σ : ℂ) + u * I)) (by simpa using hσ)
    have heq :
        xiMassBottomPrimeIntegral a c ((σ : ℂ) + u * I) =
          xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I) +
            (xiMassPrimeSquareLayer a ((σ : ℂ) + u * I) +
              xiMassHighPrimePowerTail a ((σ : ℂ) + u * I)) := by
      rw [hdecomp]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (hC u) (hB u))

/-- RH criterion: for any `1/2 < c < a` and `0 < σ`, the Riemann Hypothesis is equivalent to
boundedness of the prime-only mass layer on the vertical line `Re τ = σ`. -/
theorem riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiMassValuationOnePrimeLineBound a σ := by
  exact (riemannHypothesis_iff_xiMassBottomPrimeLineBound hhalf hca hσ).trans
    (xiMassBottomPrimeLineBound_iff_valuationOnePrimeLineBound hhalf hca hσ)

end

end RHTower
