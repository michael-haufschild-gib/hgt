import GaloisForLFunctions.RHTower.Sieve.FinRowSum

/-!
# Swapping the order of an off-diagonal double sum

`∑_m ∑_{n ≠ m} g m n = ∑_n ∑_{m ≠ n} g m n`.

The off-diagonal index set is symmetric, so the two iterated sums agree.  Rewriting each inner sum
over `univ.erase m` as a sum over all of `univ` with the diagonal term replaced by zero puts both
sides in a shape where `Finset.sum_comm` applies directly.

This is what lets the two halves of `∑_m ∑_{n ≠ m} (|a_m|² + |a_n|²) K(m,n)` be recognised as equal
for a symmetric kernel `K`, which is the decoupling step of the Dirichlet mean value theorem.
-/

namespace RHTower.Sieve

open Finset

/-- An erased sum is a full sum with the diagonal term zeroed. -/
theorem sum_erase_eq_sum_ite {N : ℕ} (f : Fin N → ℝ) (m : Fin N) :
    ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, f n
      = ∑ n : Fin N, if n = m then 0 else f n := by
  classical
  rw [← Finset.filter_ne' (Finset.univ : Finset (Fin N)) m, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n = m
  · simp [h]
  · simp [h]

/-- **The off-diagonal double sum is symmetric in its order of summation.** -/
theorem sum_erase_swap {N : ℕ} (g : Fin N → Fin N → ℝ) :
    ∑ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, g m n
      = ∑ n : Fin N, ∑ m ∈ (Finset.univ : Finset (Fin N)).erase n, g m n := by
  classical
  have h1 : ∀ m : Fin N, ∑ n ∈ (Finset.univ : Finset (Fin N)).erase m, g m n
      = ∑ n : Fin N, if n = m then 0 else g m n := fun m => sum_erase_eq_sum_ite (g m) m
  have h2 : ∀ n : Fin N, ∑ m ∈ (Finset.univ : Finset (Fin N)).erase n, g m n
      = ∑ m : Fin N, if m = n then 0 else g m n :=
    fun n => sum_erase_eq_sum_ite (fun m => g m n) n
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_congr rfl (fun n _ => h2 n),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : m = n
  · simp [h]
  · simp [h, Ne.symm h]

end RHTower.Sieve
