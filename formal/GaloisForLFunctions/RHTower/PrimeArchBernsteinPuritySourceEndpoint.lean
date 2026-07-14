import GaloisForLFunctions.RHTower.PrimeArchBernsteinLoschmidtPurity
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH

/-!
# Prime--archimedean dephased-purity source endpoint

This module joins the exact Bernstein Loschmidt purity to the rectangular prime-polar source
endpoint without lengthening the large cofinal source--temperature conjunction.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **Dephased-purity source law.**  The prime-polar critical absolute-abscissa bound is equivalent
to subexponential growth of the positive quadratic Bernstein purity.  By the exact Cesaro phase
identity, this is also the subexponential long-time Loschmidt return-energy condition. -/
theorem primeArchBernsteinPurity_sourceEndpoint_iff
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal)) ↔
      SubexponentialSquareEnergyAtNatInfinity primeArchEndpointBernsteinPurity := by
  exact
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalHausdorffQuadrant
      hL hN).trans
      (cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis.trans
        riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential)

end

end RHTower
