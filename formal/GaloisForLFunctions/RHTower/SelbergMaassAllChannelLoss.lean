import GaloisForLFunctions.RHTower.SelbergMaassPhaseStress

/-!
# Complete-channel collapse of the finite inversion loss

The finite inversion loss is selective in its input and output residues.  This file
proves that summing every pair of residues removes that selectivity exactly: transfer
energy is conserved, and the summed loss is a scalar multiple of the ambient Hermitian
metric.  Thus all-channel averaging cannot orient the selective mixed phase term in
the Selberg boundary identity.
-/

open Complex
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseStress

open SelbergMaassCongruenceTrace SelbergMaassCharacterFourier SelbergMaassCharacterProjection
  SelbergMaassMixedLoss SelbergMaassUnipotentBlocks

noncomputable section

variable (N : ℕ)

private theorem allChannel_transfer_norm_sq_sum (v : EuclideanSpace ℂ (Deck N)) :
    (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1),
      ‖inversionTransfer N r s v‖ ^ 2) = ‖v‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [inversionTransfer_energy_sum]
  exact sum_characterProjection_norm_sq N (upperBlock N) v

/-- Summing the physical loss over every input and output character removes the transfer. -/
theorem allChannel_lossEnergy_sum (v : EuclideanSpace ℂ (Deck N)) :
    (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1), lossEnergy N r s v) =
      (((N + 1 : ℕ) : ℝ) ^ 2 - 1) * ‖v‖ ^ 2 := by
  unfold lossEnergy
  calc
    _ = (((N + 1 : ℕ) : ℝ) ^ 2) * ‖v‖ ^ 2 -
        ∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1),
          ‖inversionTransfer N r s v‖ ^ 2 := by
      simp_rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      push_cast
      ring
    _ = _ := by rw [allChannel_transfer_norm_sq_sum]; ring

/-- The all-channel mixed loss is only the scalar ambient real inner product. -/
theorem allChannel_lossPair_sum (v w : EuclideanSpace ℂ (Deck N)) :
    (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1), lossPair N r s v w) =
      (((N + 1 : ℕ) : ℝ) ^ 2 - 1) * (inner ℂ v w).re := by
  have hadd :
      (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1), lossEnergy N r s (v + w)) =
        (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1), lossEnergy N r s v) +
          (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1), lossEnergy N r s w) +
            2 * (∑ r : ZMod (N + 1), ∑ s : ZMod (N + 1), lossPair N r s v w) := by
    simp_rw [lossEnergy_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [allChannel_lossEnergy_sum, allChannel_lossEnergy_sum,
    allChannel_lossEnergy_sum] at hadd
  have hnorm : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + 2 * (inner ℂ v w).re + ‖w‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) v w
  rw [hnorm] at hadd
  linear_combination -hadd / 2

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseStress
