import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableNet

/-!
# Normalized limits from bounded prefix comparisons

Two families of integer prefix invariants that differ by a fixed constant at every level and every
time have the same normalized limit vector: the difference of the increments is a bounded
correction, which disappears after dividing by `n`.

This turns the uniform prefix comparison of a pair of commensurable lattices into equality of the
two normalized Cartan vectors.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The prefix sums of an increment vector telescope. -/
theorem finiteVectorPrefixSum_increments {s : ℕ} (σ : ℕ → ℝ) (k : ℕ) :
    finiteVectorPrefixSum (fun i : Fin s => σ ((i : ℕ) + 1) - σ (i : ℕ)) k
      = σ (min k s) - σ 0 := by
  classical
  induction k with
  | zero => simp [finiteVectorPrefixSum]
  | succ k ih =>
    by_cases hk : k < s
    · have hmin : min (k + 1) s = k + 1 := by omega
      have hmink : min k s = k := by omega
      have hstep := finiteVectorPrefixSum_succ
        (fun i : Fin s => σ ((i : ℕ) + 1) - σ (i : ℕ)) ⟨k, hk⟩
      rw [hmin]
      have hk1 : ((⟨k, hk⟩ : Fin s) : ℕ) + 1 = k + 1 := rfl
      rw [hk1] at hstep
      rw [hstep, ih, hmink]
      ring
    · have hmin : min (k + 1) s = s := by omega
      have hmink : min k s = s := by omega
      have hfilter : (Finset.univ.filter fun j : Fin s => (j : ℕ) < k + 1)
          = Finset.univ.filter fun j : Fin s => (j : ℕ) < k := by
        refine Finset.filter_congr fun j _ => ?_
        have hj := j.isLt
        constructor
        · intro _
          omega
        · intro _
          omega
      rw [finiteVectorPrefixSum, hfilter, ← finiteVectorPrefixSum, ih, hmin, hmink]

/-- **Equality of normalized Cartan vectors.**  Two families of prefix invariants differing by a
fixed constant have the same normalized limit. -/
theorem tendsto_normalized_increments_of_prefix_bound {s : ℕ} (σ τ : ℕ → ℕ → ℤ) (C : ℝ)
    (hσ0 : ∀ n, σ n 0 = 0) (hτ0 : ∀ n, τ n 0 = 0)
    (hC : ∀ n k, |((σ n k : ℝ)) - ((τ n k : ℝ))| ≤ C) {L : Fin s → ℝ}
    (hlim : Tendsto (fun (n : ℕ) (i : Fin s) =>
      ((σ n ((i : ℕ) + 1) : ℝ) - (σ n (i : ℕ) : ℝ)) / n) atTop (nhds L)) :
    Tendsto (fun (n : ℕ) (i : Fin s) =>
      ((τ n ((i : ℕ) + 1) : ℝ) - (τ n (i : ℕ) : ℝ)) / n) atTop (nhds L) := by
  refine tendsto_normalized_finiteVector_of_bounded_prefix
    (fun n i => (σ n ((i : ℕ) + 1) : ℝ) - (σ n (i : ℕ) : ℝ))
    (fun n i => (τ n ((i : ℕ) + 1) : ℝ) - (τ n (i : ℕ) : ℝ)) (fun _ => C) L ?_ hlim
  intro n k
  have hσ := finiteVectorPrefixSum_increments (s := s) (fun m => (σ n m : ℝ)) k
  have hτ := finiteVectorPrefixSum_increments (s := s) (fun m => (τ n m : ℝ)) k
  rw [hσ, hτ, hσ0 n, hτ0 n]
  simpa using hC n (min k s)

end

end GaloisForLFunctions.HTGeometry
