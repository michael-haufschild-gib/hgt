import GaloisForLFunctions.RHTower.EulerDeletionUpperHalfPrimeClockGrowth

/-!
The upper-half selected EDQ block minus its literal paired-source endpoint is
exactly the prime packet sum, hence has vanishing physical fibre energy.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory
namespace RHTower.DeletionPrimeWindowPhase
open DeletionResidueMartingale

def upperHalfSourceEndpointKernel (N L r : ℕ) (x : ℝ) : ℝ :=
  (x ^ r * ((1 - x ^ clock N) * pairedMoebiusSource N r) *
      (1 - x ^ clock N)⁻¹) /
    (∑ a ∈ range (clock L), x ^ a)

theorem truncatedDivisorBlockKernel_sub_sourceEndpoint_eq_upperHalfPrimePackets
    (N l r : ℕ) (x : ℝ) (hlN : l < N) (hN : N ≤ 2 * (l + 1)) :
    truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x -
      upperHalfSourceEndpointKernel N (l + 1) r x =
      ∑ p ∈ (Icc (l + 2) N).filter Nat.Prime,
        upperHalfPrimePacketKernel N (l + 1) p r x := by
  have hrep : r % clock l + (r / clock l) * clock l = r := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div r (clock l)
  rw [truncatedDivisorBlockKernel_eq_sourceEndpoint_add_upperHalfPrimePackets
    N l (r % clock l) (r / clock l) x hlN hN]
  simp only [hrep, upperHalfSourceEndpointKernel]
  ring

theorem upperHalfSourceRemainder_physical_fibre_energy_le
    (N l : ℕ) (hlN : l < N) (hN : N ≤ 2 * (l + 1)) :
    (∑ r ∈ range (clock (l + 1)),
        (∫ x in (0 : ℝ)..1,
          truncatedDivisorBlockKernel N l (r % clock l) (r / clock l) x -
            upperHalfSourceEndpointKernel N (l + 1) r x) ^ 2 /
          cellMeasure.real (historyFibre (l + 1) r)) ≤
      2 * (N : ℝ) ^ 2 / (clock (l + 1) : ℝ) := by
  calc
    _ = ∑ r ∈ range (clock (l + 1)),
          (∫ x in (0 : ℝ)..1,
            ∑ p ∈ (Icc (l + 2) N).filter Nat.Prime,
              upperHalfPrimePacketKernel N (l + 1) p r x) ^ 2 /
            cellMeasure.real (historyFibre (l + 1) r) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      exact truncatedDivisorBlockKernel_sub_sourceEndpoint_eq_upperHalfPrimePackets
        N l r x hlN hN
    _ ≤ _ := upperHalfPhysicalPrimeWindow_fibre_energy_le N (l + 1)
      (Nat.succ_le_of_lt hlN) hN

end RHTower.DeletionPrimeWindowPhase
