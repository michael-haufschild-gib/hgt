import GaloisForLFunctions.HTGeometry.ScaledCentralBinomialAbelTransfer
import GaloisForLFunctions.RHTower.XiBernsteinPurityHalfOrderAsymptotic

/-!
# Sharp half-order Abel boundary of the Xi Bernstein purity

Failure of RH produces a source-attained radius strictly inside the unit interval.  At that
radius the complete Xi endpoint purity susceptibility has an exact positive square-root boundary,
not merely divergence or a finite-packet model.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- The Abel susceptibility value of the complete source-defined Xi Bernstein purity. -/
def primeArchEndpointBernsteinAbelSusceptibility (t : ℝ) : ℝ :=
  ∑' n : ℕ, primeArchEndpointBernsteinPurity n * t ^ n

/-- **Exact positive half-order Abel boundary under failure of RH.**  The boundary is carried by
the full source-defined purity.  Its coefficient is the positive aggregate of the maximal
source-attained Xi coordinate packet. -/
theorem exists_positive_halfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta L : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      L = ∑ u ∈ xiEndpointCoordinateSet D,
        ‖xiEndpointCoordinateWeight D u‖ ^ (2 : ℕ) *
          bernsteinAffineRowHalfOrderConstant u ∧
      0 < L ∧ 0 < Real.sqrt Real.pi * L ∧
      Tendsto
        (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
          primeArchEndpointBernsteinAbelSusceptibility t)
        (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))))
        (nhds (Real.sqrt Real.pi * L)) := by
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hcoeff⟩ :=
    exists_positive_halfOrder_primeArchEndpointBernsteinPurity_of_not_rh hRH
  have hBpos : 0 < B := lt_trans zero_lt_one hB
  have hradial :=
    GaloisForLFunctions.HTGeometry.tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder
      hBpos hcoeff
  have hradial' : Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) *
        primeArchEndpointBernsteinAbelSusceptibility t)
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))))
      (nhds (Real.sqrt Real.pi * L)) := by
    simpa only [primeArchEndpointBernsteinAbelSusceptibility] using hradial
  exact ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub, hL, hLpos,
    mul_pos (Real.sqrt_pos.2 Real.pi_pos) hLpos, hradial'⟩

end

end RHTower

