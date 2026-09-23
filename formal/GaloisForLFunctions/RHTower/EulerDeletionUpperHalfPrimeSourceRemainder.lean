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

open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionPrimeWindowPhase
open DeletionResidueMartingale

theorem upperHalfSourceRemainder_physical_fibre_energy_tendsto_zero
    (N : ℕ → ℕ) (hlo : ∀ l, l + 1 ≤ N l)
    (hhi : ∀ l, N l ≤ 2 * (l + 1)) :
    Tendsto
      (fun l : ℕ =>
        ∑ r ∈ range (clock (l + 1)),
          (∫ x in (0 : ℝ)..1,
            truncatedDivisorBlockKernel (N l) l (r % clock l) (r / clock l) x -
              upperHalfSourceEndpointKernel (N l) (l + 1) r x) ^ 2 /
            cellMeasure.real (historyFibre (l + 1) r))
      atTop (𝓝 0) := by
  have hshift : Tendsto
      (fun l : ℕ => (((l + 1 : ℕ) : ℝ) ^ 2 / (clock (l + 1) : ℝ)))
      atTop (𝓝 0) :=
    DeletionResidueMartingale.tendsto_sq_div_clock_zero.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun l : ℕ => 8 * (((l + 1 : ℕ) : ℝ) ^ 2 / (clock (l + 1) : ℝ)))
      atTop (𝓝 0) := by
    simpa using hshift.const_mul (8 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun l => by
      apply Finset.sum_nonneg
      intro r hr
      have hm := historyFibre_mass_pos (l + 1) r (Finset.mem_range.mp hr)
      exact div_nonneg (sq_nonneg _) hm.le
  · exact Filter.Eventually.of_forall fun l => by
      have hlN : l < N l := by have h := hlo l; omega
      have hE := upperHalfSourceRemainder_physical_fibre_energy_le (N l) l hlN (hhi l)
      have hNreal : (N l : ℝ) ≤ 2 * ((l + 1 : ℕ) : ℝ) := by
        exact_mod_cast hhi l
      have hsq : (N l : ℝ) ^ 2 ≤ (2 * ((l + 1 : ℕ) : ℝ)) ^ 2 :=
        (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) (N l)) (by positivity)).mpr hNreal
      have hC : (0 : ℝ) ≤ clock (l + 1) := Nat.cast_nonneg _
      calc
        _ ≤ 2 * (N l : ℝ) ^ 2 / (clock (l + 1) : ℝ) := hE
        _ ≤ 2 * (2 * ((l + 1 : ℕ) : ℝ)) ^ 2 / (clock (l + 1) : ℝ) := by
          apply div_le_div_of_nonneg_right _ hC
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ = 8 * (((l + 1 : ℕ) : ℝ) ^ 2 / (clock (l + 1) : ℝ)) := by ring

end RHTower.DeletionPrimeWindowPhase
