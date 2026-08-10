import GaloisForLFunctions.HTGeometry.ShilovStableImage
import GaloisForLFunctions.HTGeometry.ShilovLocalBoundaryIdeal

/-!
# The local comparison, assembled

The pieces of the local envelope comparison are combined here.  For a tower of seminormed modules
with contractive bonds:

* the coherent families form a closed set (`isClosed_coherent`);
* density at each single stage already gives simultaneous approximation in finitely many stages,
  because earlier coordinates are contractive images of later ones;
* a closed set of coherent families that is stagewise dense therefore contains every coherent
  family (`coherent_mem_of_stagewise_dense`).

This is the generation half of the card's local comparison in its final form: what has to be
checked on a Shilov tower is only that each stage system is dense in its stage envelope, since
`exists_coherent_lift_at` supplies the coherent lifts and contractivity propagates the estimate
downward.
-/

namespace GaloisForLFunctions.HTGeometry

namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {M : ℕ → Type v} [∀ n, NormedAddCommGroup (M n)] [∀ n, Module 𝕜 (M n)]

/-- Contractive bonds are continuous. -/
theorem continuous_bond (bond : ∀ n, M (n + 1) →ₗ[𝕜] M n)
    (hcontr : ∀ n (x : M (n + 1)), ‖bond n x‖ ≤ ‖x‖) (n : ℕ) : Continuous (bond n) := by
  have hlip : LipschitzWith 1 (bond n) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    simpa using hcontr n (x - y)
  exact hlip.continuous

/-- The coherent families of a tower with contractive bonds form a closed set. -/
theorem isClosed_coherent (bond : ∀ n, M (n + 1) →ₗ[𝕜] M n)
    (hcontr : ∀ n (x : M (n + 1)), ‖bond n x‖ ≤ ‖x‖) :
    IsClosed {a : ∀ m, M m | ∀ m, bond m (a (m + 1)) = a m} := by
  have hset : {a : ∀ m, M m | ∀ m, bond m (a (m + 1)) = a m}
      = ⋂ m : ℕ, {a : ∀ k, M k | bond m (a (m + 1)) = a m} := by
    ext a
    simp [Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun m => ?_
  have hcont : Continuous fun a : ∀ k, M k => bond m (a (m + 1)) :=
    (continuous_bond bond hcontr m).comp (continuous_apply (m + 1))
  exact isClosed_eq hcont (continuous_apply m)

/-- **Stagewise density fills a closed set of coherent families.**  Density at each single stage
suffices: contractivity propagates the estimate to all earlier stages, and the projective topology
then delivers the limit. -/
theorem coherent_mem_of_stagewise_dense (bond : ∀ n, M (n + 1) →ₗ[𝕜] M n)
    (hcontr : ∀ n (x : M (n + 1)), ‖bond n x‖ ≤ ‖x‖) {C : Set (∀ m, M m)}
    (hCclosed : IsClosed C) (hCcoh : ∀ c ∈ C, ∀ m, bond m (c (m + 1)) = c m)
    {a : ∀ m, M m} (ha : ∀ m, bond m (a (m + 1)) = a m)
    (hdense : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ c ∈ C, ‖c n - a n‖ < ε) : a ∈ C :=
  ShilovLocal.mem_of_coordinatewise_approx hCclosed
    (simultaneous_approx_of_stagewise bond hcontr hCcoh ha hdense)

/-- The same conclusion for every coherent family at once. -/
theorem coherent_subset_of_stagewise_dense (bond : ∀ n, M (n + 1) →ₗ[𝕜] M n)
    (hcontr : ∀ n (x : M (n + 1)), ‖bond n x‖ ≤ ‖x‖) {C : Set (∀ m, M m)}
    (hCclosed : IsClosed C) (hCcoh : ∀ c ∈ C, ∀ m, bond m (c (m + 1)) = c m)
    (hdense : ∀ a : ∀ m, M m, (∀ m, bond m (a (m + 1)) = a m) →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ c ∈ C, ‖c n - a n‖ < ε) :
    {a : ∀ m, M m | ∀ m, bond m (a (m + 1)) = a m} ⊆ C :=
  fun a ha => coherent_mem_of_stagewise_dense bond hcontr hCclosed hCcoh ha (hdense a ha)

end BoundaryMigration

end GaloisForLFunctions.HTGeometry
