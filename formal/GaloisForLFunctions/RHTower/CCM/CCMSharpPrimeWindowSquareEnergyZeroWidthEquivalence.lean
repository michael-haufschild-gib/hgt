import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSquareEnergyWidthCollision
import GaloisForLFunctions.RHTower.Sieve.SquareWindowEnergyUnderRH

/-!
# Zero-width equivalence for square-aperture positive excess

This file closes the endpoint omitted from the width-transfer module.  Under RH, the established
dyadic Chebyshev estimate makes the full square-window correlation energy subpower, hence also its
one-sided positive-excess square energy.  Nonnegative Dirichlet summatory theory then gives the
critical absolute-abscissa bound.  The already proved square-energy zero tomography supplies both
reverse implications.

The result is the exact closed collision stated by the corresponding pipeline card:

`RH ↔ square-energy abscissa ≤ 1 ↔ all-supercritical summatory growth`.
-/

open Complex Filter Function Set LSeries

namespace RHTower

noncomputable section

/-- RH supplies the critical square-aperture positive-excess-square abscissa bound. -/
theorem squarePrimeWindowPositiveExcessSquare_abscissa_le_one_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
      ((1 : ℝ) : EReal) := by
  change LSeries.abscissaOfAbsConv
      (fun m => ((((dyadicWeightedPrimeWindowPositiveExcess (m ^ (2 : ℕ))) ^ (2 : ℕ) : ℝ)) : ℂ)) ≤
    ((1 : ℝ) : EReal)
  apply (abscissaOfAbsConv_le_iff_nonnegativeDirichletSummatoryGrowthAt
    (fun m => sq_nonneg (dyadicWeightedPrimeWindowPositiveExcess (m ^ (2 : ℕ))))
    zero_le_one).mpr
  intro delta hdelta
  exact squarePrimeWindowPositiveExcessSquare_summatory_isBigO
    (RHTower.Sieve.squarePrimeWindowCorrelationEnergySubpower_of_riemannHypothesis hRH)
    delta hdelta

/-- The critical square-energy abscissa is exactly equivalent to RH. -/
theorem riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_abscissa_le_one :
    RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
        ((1 : ℝ) : EReal) :=
  ⟨squarePrimeWindowPositiveExcessSquare_abscissa_le_one_of_riemannHypothesis,
    riemannHypothesis_of_squarePrimeWindowPositiveExcessSquare_abscissa_le_one⟩

/-- RH is exactly the literal all-supercritical summatory bound for squared positive excess. -/
theorem riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_summatory_subpower :
    RiemannHypothesis ↔
      ∀ delta : ℝ, 0 < delta →
        (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
          (dyadicWeightedPrimeWindowPositiveExcess (m ^ (2 : ℕ))) ^ (2 : ℕ)) =O[Filter.atTop]
            (fun M : ℕ => (M : ℝ) ^ (1 + delta)) := by
  constructor
  · intro hRH delta hdelta
    exact squarePrimeWindowPositiveExcessSquare_summatory_isBigO
      (RHTower.Sieve.squarePrimeWindowCorrelationEnergySubpower_of_riemannHypothesis hRH)
      delta hdelta
  · intro hGrowth
    apply riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergySubpower
    intro delta hdelta
    rw [funext squarePrimeWindowPositiveExcessSquareEnergy_eq_summatory]
    exact hGrowth delta hdelta

/-- The abscissa endpoint and the card's literal summatory condition are exactly equivalent. -/
theorem squarePrimeWindowPositiveExcessSquare_abscissa_le_one_iff_summatory_subpower :
    LSeries.abscissaOfAbsConv
        squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
      ((1 : ℝ) : EReal) ↔
      ∀ delta : ℝ, 0 < delta →
        (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
          (dyadicWeightedPrimeWindowPositiveExcess (m ^ (2 : ℕ))) ^ (2 : ℕ)) =O[Filter.atTop]
            (fun M : ℕ => (M : ℝ) ^ (1 + delta)) :=
  riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_abscissa_le_one.symm.trans
    riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_summatory_subpower

/-- Closed three-way zero-width collision certificate. -/
theorem squarePrimeWindowPositiveExcessSquare_zeroWidthCollision :
    (RiemannHypothesis ↔
      LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
        ((1 : ℝ) : EReal)) ∧
    (LSeries.abscissaOfAbsConv
          squarePrimeWindowPositiveExcessSquareDirichletCoefficient ≤
        ((1 : ℝ) : EReal) ↔
      ∀ delta : ℝ, 0 < delta →
        (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M,
          (dyadicWeightedPrimeWindowPositiveExcess (m ^ (2 : ℕ))) ^ (2 : ℕ)) =O[Filter.atTop]
            (fun M : ℕ => (M : ℝ) ^ (1 + delta))) :=
  ⟨riemannHypothesis_iff_squarePrimeWindowPositiveExcessSquare_abscissa_le_one,
    squarePrimeWindowPositiveExcessSquare_abscissa_le_one_iff_summatory_subpower⟩

end


end RHTower
