import GaloisForLFunctions.HTGeometry.OccupationEulerProduct
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaFreeEnergy

/-!
# The free energy in moment form

Raising an occupation monomial to a power is the occupation monomial of the powered nomes, so the
Euler product evaluates every occupation moment as an infinite product over the nomes.

Every occupation moment is therefore an infinite product over the nomes, which is the coefficient
series the free energy is expanded in.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

theorem nomeMonomial_pow {ι : Type*} (p : ι → ℂ) (k : ℕ) (ν : ι →₀ ℕ) :
    (nomeMonomial p ν) ^ k = nomeMonomial (fun a => p a ^ k) ν := by
  classical
  rw [nomeMonomial, nomeMonomial, Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem summable_norm_pow_of_le {ι : Type*} {p : ι → ℂ} (hp_lt : ∀ a, ‖p a‖ < 1)
    {g k : ℕ} (hk : g + 1 ≤ k) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    Summable (fun a => ‖p a‖ ^ k) :=
  Summable.of_nonneg_of_le (fun a => by positivity)
    (fun a => pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (hp_lt a)) hk) hsum

/-- **Occupation moments are nome Euler products.** -/
theorem tsum_nomeMonomial_pow {ι : Type*} (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    {k : ℕ} (hk : 1 ≤ k) (hsum : Summable (fun a => ‖p a‖ ^ k)) :
    (∑' ν : ι →₀ ℕ, (nomeMonomial p ν) ^ k) = ∏' a, (1 - p a ^ k)⁻¹ := by
  have hu_lt : ∀ a, ‖p a ^ k‖ < 1 := by
    intro a
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hp_lt a) (by omega)
  have hu_sum : Summable (fun a => ‖p a ^ k‖) := by
    simpa only [norm_pow] using hsum
  have heuler := tsum_nomeMonomial_eq_tprod (fun a => p a ^ k) hu_lt hu_sum
  rw [← heuler]
  exact tsum_congr fun ν => nomeMonomial_pow p k ν

end HTGeometry
