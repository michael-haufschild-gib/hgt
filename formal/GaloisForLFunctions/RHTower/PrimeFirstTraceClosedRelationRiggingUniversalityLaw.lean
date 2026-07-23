import GaloisForLFunctions.RHTower.PrimeFirstTraceExactGraphClosureUniversalityLaw
import GaloisForLFunctions.RHTower.ArithmeticSchurExactNormRiggingNoGo

/-!
# Prime first-trace closed-relation/rigging universality

The exact first-trace graph closure is the minimal closed relation containing the algebraic graph.
Its vertical multivalued part is the entire zero-vacuum Hardy hyperplane. Therefore every closed
linear relation extension contains that hyperplane and no such extension can be single-valued.
Exact arithmetic-Schur source and response norms preserve the same obstruction in arbitrary
complete riggings.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Every closed linear relation containing the actual-prime first-trace graph contains the full
vertical zero-vacuum Hardy hyperplane. -/
theorem primeFirstTraceClock_closedRelationExtension_contains_zeroVacuum
    (G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)))
    (hGclosed : IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))))
    (hgraph :
      realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock ≤ G)
    (y : PrimeHardy) (hy : y 0 = 0) :
    WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G := by
  have hclosure :
      ((realLinearGraphSubmodule primeHardyKernelMap
        primeFirstTraceClock).topologicalClosure :
          Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun w hw => hgraph hw) hGclosed
  apply hclosure
  exact (primeFirstTraceClock_pair_mem_graphClosure_iff 0 y).2 hy

/-- **Closed single-valued extension no-go.** No closed linear relation extending the
actual-prime first-trace graph can have trivial vertical fiber. -/
theorem primeFirstTraceClock_no_closed_singleValuedRelationExtension :
    ¬ ∃ G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))) ∧
      realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock ≤ G ∧
      ∀ y : PrimeHardy,
        WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G → y = 0 := by
  rintro ⟨G, hGclosed, hgraph, hsingle⟩
  let e₁ : PrimeHardy := lp.single 2 1 1
  have he₁zero : e₁ 0 = 0 := by
    simp [e₁]
  have he₁mem :=
    primeFirstTraceClock_closedRelationExtension_contains_zeroVacuum
      G hGclosed hgraph e₁ he₁zero
  exact primeHardy_basisOne_ne_zero (hsingle e₁ he₁mem)

/-- **Prime first-trace closed-relation/rigging universality law.** The minimal closed graph has
full source domain and exactly the zero-vacuum response fiber; every closed relation extension is
multivalued; and every exact-norm complete rigging remains sequentially nonclosable. -/
theorem primeFirstTraceClock_closedRelationRiggingUniversality
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (hsource : ∀ d, ‖j d‖ = ‖primeHardyKernelMap d‖)
    (hclock : ∀ d, ‖T d‖ = ‖primeFirstTraceClock d‖) :
    (∀ x y : PrimeHardy,
      WithLp.toLp 2 (x, y) ∈
          (realLinearGraphSubmodule primeHardyKernelMap
            primeFirstTraceClock).topologicalClosure ↔
        y 0 = 0) ∧
      (¬ ∃ G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)),
        IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))) ∧
        realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock ≤ G ∧
        ∀ y : PrimeHardy,
          WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G → y = 0) ∧
      ¬ IsSequentiallyClosableBetween T j := by
  exact ⟨primeFirstTraceClock_pair_mem_graphClosure_iff,
    primeFirstTraceClock_no_closed_singleValuedRelationExtension,
    arithmeticSchurExactNormRigging_not_closable j T hsource hclock⟩

end

end RHTower
