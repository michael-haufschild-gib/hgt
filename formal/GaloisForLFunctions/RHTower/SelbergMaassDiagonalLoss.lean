import GaloisForLFunctions.RHTower.SelbergMaassInversionPhaseEnergy

/-!
# Source-attached diagonal inversion loss

The finite diagonal inversion channels cannot all preserve the source vector:
their total loss dominates `N` times the literal congruence-trace density.
At a positive-density point in positive level, one channel is strictly lossy.
This is finite source algebra only; it does not supply the signed core-boundary
comparison required for Selberg's quarter bound.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassDiagonalLoss
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassInversionPhaseEnergy SelbergMaassCharacterFourier
open GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Full diagonal inversion loss dominates source density at every point. -/
theorem diagonal_source_loss_sum_lower (z : ℍ) :
    (N : ℝ) * density N f z ≤
      ∑ r : ZMod (N + 1),
        (‖sourceVector N f z‖ ^ 2 - ‖inversionTransfer N r r (sourceVector N f z)‖ ^ 2) := by
  simpa only [sourceVector_norm_sq] using
    diagonal_transfer_loss_sum_lower N (sourceVector N f z)

/-- At a positive-density point in positive level, some diagonal channel loses norm. -/
theorem exists_diagonal_source_loss_pos {z : ℍ}
    (hN : 0 < N) (hz : 0 < density N f z) :
    ∃ r : ZMod (N + 1),
      0 < ‖sourceVector N f z‖ ^ 2 - ‖inversionTransfer N r r (sourceVector N f z)‖ ^ 2 := by
  have hsum := diagonal_source_loss_sum_lower N f z
  have hprod : 0 < (N : ℝ) * density N f z :=
    mul_pos (by exact_mod_cast hN) hz
  have hpos : 0 < ∑ r : ZMod (N + 1),
      (‖sourceVector N f z‖ ^ 2 - ‖inversionTransfer N r r (sourceVector N f z)‖ ^ 2) :=
    lt_of_lt_of_le hprod hsum
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (Finset.sum_nonpos fun r _ => hn r)) hpos

/-- Every positive-level source has a point with a strictly lossy diagonal channel. -/
theorem exists_source_diagonal_loss_pos (hN : 0 < N) :
    ∃ z : ℍ, ∃ r : ZMod (N + 1),
      0 < ‖sourceVector N f z‖ ^ 2 - ‖inversionTransfer N r r (sourceVector N f z)‖ ^ 2 := by
  obtain ⟨z, hz⟩ := density_pos_somewhere N f
  exact ⟨z, exists_diagonal_source_loss_pos N f hN hz⟩

end
end GaloisForLFunctions.RHTower.SelbergMaassDiagonalLoss
