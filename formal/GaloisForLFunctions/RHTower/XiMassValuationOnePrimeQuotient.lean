import GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue
import GaloisForLFunctions.RHTower.XiMassPrimeOpenCore

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def xiMassValuationOnePrimeLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes, xiMassCenteredPrimeAtom a τ (p : ℕ)

def XiMassValuationOnePrimeLineBound (a σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ,
    ‖xiMassValuationOnePrimeLayer a ((σ : ℂ) + u * I)‖ ≤ C

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

theorem riemannHypothesis_iff_xiMassValuationOnePrimeLineBound
    {a c σ : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hσ : 0 < σ) :
    RiemannHypothesis ↔ XiMassValuationOnePrimeLineBound a σ := by
  exact (riemannHypothesis_iff_xiMassBottomPrimeLineBound hhalf hca hσ).trans
    (xiMassBottomPrimeLineBound_iff_valuationOnePrimeLineBound hhalf hca hσ)

end

end RHTower
