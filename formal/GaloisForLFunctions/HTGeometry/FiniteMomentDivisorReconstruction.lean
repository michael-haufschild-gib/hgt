import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve
import GaloisForLFunctions.HTGeometry.PowerSumTorelli

/-!
# Finitely many power moments reconstruct a divisor

A multiset of `n` complex numbers is determined by its power sums of order at most `n`.  This is
the multiset form of the sharp finite Newton inversion, obtained by enumerating each multiset as a
family indexed by `Fin n`.
-/

namespace GaloisForLFunctions

open Finset

noncomputable section

/-- **Finitely many power moments determine a divisor.** -/
theorem multiset_eq_of_powerSum_eq_le {M N : Multiset ℂ}
    (hcard : Multiset.card M = Multiset.card N)
    (h : ∀ k ≤ Multiset.card M,
      (M.map (fun x => x ^ k)).sum = (N.map (fun x => x ^ k)).sum) :
    M = N := by
  classical
  obtain ⟨n, f, hf⟩ := multiset_eq_map_univ_val M
  obtain ⟨n', g, hg⟩ := multiset_eq_map_univ_val N
  have hn : Multiset.card M = n := by
    rw [← hf, Multiset.card_map]; simp
  have hn' : Multiset.card N = n' := by
    rw [← hg, Multiset.card_map]; simp
  have hnn : n = n' := by omega
  subst hnn
  have hmapM : ∀ j : ℕ, (Finset.univ.val.map fun i => f i ^ j) = M.map (fun x => x ^ j) := by
    intro j; rw [← hf, Multiset.map_map]; rfl
  have hmapN : ∀ j : ℕ, (Finset.univ.val.map fun i => g i ^ j) = N.map (fun x => x ^ j) := by
    intro j; rw [← hg, Multiset.map_map]; rfl
  have hp : ∀ k, k ≤ n → (Finset.univ.val.map (fun i => f i ^ k)).sum
      = (Finset.univ.val.map (fun i => g i ^ k)).sum := by
    intro k hk
    rw [hmapM k, hmapN k]
    exact h k (by omega)
  have := powerSum_torelli_finite f g hp
  rw [hf, hg] at this
  exact this

end

end GaloisForLFunctions
