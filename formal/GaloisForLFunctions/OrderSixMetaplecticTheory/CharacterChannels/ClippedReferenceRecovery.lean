import GaloisForLFunctions.OrderSixMetaplecticTheory.CharacterChannels.WeilCubicProjection
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedReferenceMass

/-!
# Recovering the signed order-six row from three clipped measurements

The actual finite row is the first moment of its projected residue packet.
Covariance alone forgets its phase. Adding the fixed references `0`, `1`, and
`i` before taking clipped covariance energies recovers that complex moment.
-/

noncomputable section
open scoped BigOperators Classical NNReal
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein
open HilbertMetric.Clipped

local instance : Finite ResidueFour :=
  (Ideal.span {(4 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (4 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
local instance : Fintype ResidueFour := Fintype.ofFinite _

/-- Finite order-six row with its full ramified phase. -/
def finiteOrderSixMoment (S : Finset O) (w : O → ℂ) : ℂ :=
  ∑ c ∈ S, fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c

/-- Residue packet after projection onto the contributing cubic character. -/
def projectedRowPacket (S : Finset O) (w : O → ℂ) (r : ResidueFour) : ℂ :=
  phase r * cubicProjection (gaussSquareClassMass S w) r

theorem sum_projectedRowPacket (S : Finset O) (w : O → ℂ) :
    (∑ r, projectedRowPacket S w r) = finiteOrderSixMoment S w :=
  (finite_row_sum_eq_projected S w).symm

/-- Three referenced clipped energies recover the complete signed row sum. -/
theorem finiteOrderSixMoment_from_referenceMass (S : Finset O) (w : O → ℂ)
    (c : ℝ≥0) (hc : 0 < c) :
    finiteOrderSixMoment S w =
      (((referenceMass c (projectedRowPacket S w) 1 -
        referenceMass c (projectedRowPacket S w) 0 - Fintype.card ResidueFour) / 2 : ℝ) : ℂ) +
      Complex.I * (((referenceMass c (projectedRowPacket S w) Complex.I -
        referenceMass c (projectedRowPacket S w) 0 - Fintype.card ResidueFour) / 2 : ℝ) : ℂ) := by
  rw [← sum_projectedRowPacket]
  exact firstMoment_from_referenceMass c hc _

/-- Matching all three referenced measurements forces equality of the signed rows. -/
theorem finiteOrderSixMoment_eq_of_reference_energies
    (S T : Finset O) (w v : O → ℂ) (c : ℝ≥0) (hc : 0 < c)
    (h : ∀ z ∈ ({0, 1, Complex.I} : Finset ℂ),
      energy c (columnCovariance (fun r => projectedRowPacket S w r + z)) =
        energy c (columnCovariance (fun r => projectedRowPacket T v r + z))) :
    finiteOrderSixMoment S w = finiteOrderSixMoment T v := by
  rw [← sum_projectedRowPacket, ← sum_projectedRowPacket]
  exact firstMoment_eq_of_reference_energies c hc _ _ h

#print axioms finiteOrderSixMoment_from_referenceMass
#print axioms finiteOrderSixMoment_eq_of_reference_energies

end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
