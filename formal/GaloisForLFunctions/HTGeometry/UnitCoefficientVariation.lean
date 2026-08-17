import GaloisForLFunctions.HTGeometry.InverseSquareTailWitness

/-!
# Unit coefficient variation

The spectral coefficients of two unit vectors have total variation at most one, by discrete
Cauchy--Schwarz against the two Parseval sums.  Raising that to any power keeps it at most one, so
every replica layer of the multinomial expansion also has total variation at most one.

This is the bound that makes a replica coefficient family a signed probability distribution over
spectral actions, with no dependence on the Hamiltonian, its spectrum, or the replica order.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

section Variation

variable {n : Type*} [Fintype n]

/-- **Unit total variation.**  The spectral overlap coefficients of two unit vectors sum in modulus
to at most one. -/
theorem sum_norm_mul_le_one (z χ : n → ℂ) (hz : ∑ j, ‖z j‖ ^ 2 = 1)
    (hχ : ∑ j, ‖χ j‖ ^ 2 = 1) :
    ∑ j, ‖z j‖ * ‖χ j‖ ≤ 1 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) (fun j => ‖z j‖) fun j => ‖χ j‖
  rw [hz, hχ, mul_one] at hcs
  have hnn : (0 : ℝ) ≤ ∑ j, ‖z j‖ * ‖χ j‖ :=
    Finset.sum_nonneg fun j _ => by positivity
  nlinarith [hcs, hnn]

/-- **The replica layer inherits the bound.**  Any power of a quantity in `[0,1]` stays in `[0,1]`,
so a total variation of one at a single copy gives total variation at most one at every replica
order. -/
theorem pow_le_one_of_variation {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (k : ℕ) :
    v ^ k ≤ 1 :=
  pow_le_one₀ hv0 hv1

/-- **`(9)`**: the total variation of the paired replica coefficients is at most one. -/
theorem replica_variation_le_one (z χ : n → ℂ) (hz : ∑ j, ‖z j‖ ^ 2 = 1)
    (hχ : ∑ j, ‖χ j‖ ^ 2 = 1) (r : ℕ) :
    (∑ j, ‖z j‖ * ‖χ j‖) ^ (2 * r) ≤ 1 := by
  refine pow_le_one_of_variation ?_ (sum_norm_mul_le_one z χ hz hχ) _
  exact Finset.sum_nonneg fun j _ => by positivity

end Variation

end GaloisForLFunctions.HTGeometry
