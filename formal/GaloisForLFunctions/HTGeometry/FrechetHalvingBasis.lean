import GaloisForLFunctions.HTGeometry.FrechetOpenMappingBaire

/-!
# A halving neighbourhood basis of the origin

A first-countable topological vector space has a countable basis of balanced neighbourhoods of the
origin, each containing the sum of two copies of its successor.  This is the scaffold for the series
argument that removes the closure in the open mapping theorem.

* `exists_halvingBasis` : **the basis.**
-/

namespace GaloisForLFunctions

open Filter Set Pointwise Topology

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]

/-- A balanced half-neighbourhood inside a prescribed pair of neighbourhoods. -/
theorem exists_balanced_half {S R : Set E} (hS : S ∈ 𝓝 (0 : E)) (hR : R ∈ 𝓝 (0 : E)) :
    ∃ T : Set E, T ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 T ∧ T + T ⊆ S ∧ T ⊆ R := by
  obtain ⟨W, hW, hWS⟩ := exists_nhds_zero_half (Filter.inter_mem hS hR)
  refine ⟨balancedCore 𝕜 W, balancedCore_mem_nhds_zero hW, balancedCore_balanced W, ?_, ?_⟩
  · rintro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
    exact (hWS a (balancedCore_subset W ha) b (balancedCore_subset W hb)).1
  · intro z hz
    have hzW : z ∈ W := balancedCore_subset W hz
    have h0 : (0 : E) ∈ W := mem_of_mem_nhds hW
    have := (hWS z hzW 0 h0).2
    simpa using this

/-- **A halving basis of balanced neighbourhoods of the origin.** -/
theorem exists_halvingBasis [FirstCountableTopology E] :
    ∃ C : ℕ → Set E, (∀ n, C n ∈ 𝓝 (0 : E)) ∧ (∀ n, Balanced 𝕜 (C n))
      ∧ (∀ n, C (n + 1) + C (n + 1) ⊆ C n)
      ∧ (𝓝 (0 : E)).HasBasis (fun _ : ℕ => True) C := by
  classical
  obtain ⟨B, hB⟩ := (𝓝 (0 : E)).exists_antitone_basis
  -- a total selector for the halving step
  have hsel : ∀ (S : Set E) (n : ℕ), ∃ T : Set E, S ∈ 𝓝 (0 : E) →
      (T ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 T ∧ T + T ⊆ S ∧ T ⊆ B (n + 1)) := by
    intro S n
    by_cases hS : S ∈ 𝓝 (0 : E)
    · obtain ⟨T, h1, h2, h3, h4⟩ := exists_balanced_half (𝕜 := 𝕜) hS (hB.mem (n + 1))
      exact ⟨T, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨∅, fun h => absurd h hS⟩
  choose T hT using hsel
  refine ⟨fun n => Nat.rec (balancedCore 𝕜 (B 0)) (fun k prev => T prev k) n, ?_, ?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => exact balancedCore_mem_nhds_zero (hB.mem 0)
    | succ k ih => exact (hT _ k ih).1
  · intro n
    match n with
    | 0 => exact balancedCore_balanced (B 0)
    | (k + 1) =>
      have hmem : (Nat.rec (motive := fun _ => Set E) (balancedCore 𝕜 (B 0))
          (fun k prev => T prev k) k : Set E) ∈ 𝓝 (0 : E) := by
        induction k with
        | zero => exact balancedCore_mem_nhds_zero (hB.mem 0)
        | succ m ih => exact (hT _ m ih).1
      exact (hT _ k hmem).2.1
  · intro n
    have hmem : (Nat.rec (motive := fun _ => Set E) (balancedCore 𝕜 (B 0))
        (fun k prev => T prev k) n : Set E) ∈ 𝓝 (0 : E) := by
      induction n with
      | zero => exact balancedCore_mem_nhds_zero (hB.mem 0)
      | succ m ih => exact (hT _ m ih).1
    exact (hT _ n hmem).2.2.1
  · -- the sets are contained in the antitone basis, hence form a basis themselves
    have hsub : ∀ n, (Nat.rec (motive := fun _ => Set E) (balancedCore 𝕜 (B 0))
        (fun k prev => T prev k) n : Set E) ⊆ B n := by
      intro n
      match n with
      | 0 => exact balancedCore_subset (B 0)
      | (k + 1) =>
        have hmem : (Nat.rec (motive := fun _ => Set E) (balancedCore 𝕜 (B 0))
            (fun k prev => T prev k) k : Set E) ∈ 𝓝 (0 : E) := by
          induction k with
          | zero => exact balancedCore_mem_nhds_zero (hB.mem 0)
          | succ m ih => exact (hT _ m ih).1
        exact (hT _ k hmem).2.2.2
    have hmemall : ∀ n, (Nat.rec (motive := fun _ => Set E) (balancedCore 𝕜 (B 0))
        (fun k prev => T prev k) n : Set E) ∈ 𝓝 (0 : E) := by
      intro n
      induction n with
      | zero => exact balancedCore_mem_nhds_zero (hB.mem 0)
      | succ m ih => exact (hT _ m ih).1
    refine ⟨fun S => ⟨fun hS => ?_, fun ⟨n, _, hn⟩ => Filter.mem_of_superset (hmemall n) hn⟩⟩
    obtain ⟨n, _, hnS⟩ := hB.toHasBasis.mem_iff.1 hS
    exact ⟨n, trivial, fun z hz => hnS (hsub n hz)⟩

end GaloisForLFunctions
