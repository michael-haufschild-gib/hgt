import GaloisForLFunctions.RHTower.PrimeFirstTraceClosedRelationRiggingUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeFirstTraceTopologicalNonlinearRiggingNoEscapeUniversalityLaw

/-!
# Prime first-trace complete no-escape universality

The actual-prime first-trace clock has one obstruction at every completion level.  Its exact graph
closure has the full zero-vacuum vertical fibre; every closed linear extension inherits that
fibre; arbitrary closed single-valued relations and nonlinear closed graphs fail; topology-
preserving source realizations have nonclosed graphs; and exact-norm complete riggings remain
nonclosable.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- **Prime first-trace complete no-escape universality law.**  Exact graph closure, hereditary
vertical multivaluedness of every closed linear extension, arbitrary closed-relation and nonlinear
graph failure, topological graph failure, and exact-norm rigging nonclosability all hold
simultaneously for the same first-trace clock. -/
theorem primeFirstTraceClock_completeNoEscapeUniversality
    {E K X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]
    [TopologicalSpace X]
    (j : (Nat.Primes →₀ ℝ) →ₗ[ℝ] E)
    (T : (Nat.Primes →₀ ℝ) →ₗ[ℝ] K)
    (hsourceNorm : ∀ d, ‖j d‖ = ‖primeHardyKernelMap d‖)
    (hclockNorm : ∀ d, ‖T d‖ = ‖primeFirstTraceClock d‖)
    (jTop : (Nat.Primes →₀ ℝ) → X)
    (F : X → PrimeHardy)
    (hsourceTopology :
      Tendsto (fun n => jTop (primeFirstTraceNullSequence n))
        atTop (𝓝 (jTop 0)))
    (hextendTop : ∀ d : Nat.Primes →₀ ℝ,
      F (jTop d) = primeFirstTraceClock d) :
    (∀ x y : PrimeHardy,
      WithLp.toLp 2 (x, y) ∈
          (realLinearGraphSubmodule primeHardyKernelMap
            primeFirstTraceClock).topologicalClosure ↔
        y 0 = 0) ∧
    (∀ G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))) →
      realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock ≤ G →
      ∀ y : PrimeHardy, y 0 = 0 →
        WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G) ∧
    (¬ ∃ G : Submodule ℝ (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))) ∧
      realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock ≤ G ∧
      ∀ y : PrimeHardy,
        WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G → y = 0) ∧
    (¬ ∃ G : Set (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed G ∧
      (realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock :
        Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G ∧
      ∀ x y z : PrimeHardy,
        WithLp.toLp 2 (x, y) ∈ G →
        WithLp.toLp 2 (x, z) ∈ G →
        y = z) ∧
    (¬ ∃ f : PrimeHardy → PrimeHardy,
      IsClosed
        {w : WithLp 2 (PrimeHardy × PrimeHardy) |
          w.ofLp.2 = f w.ofLp.1} ∧
      ∀ d : Nat.Primes →₀ ℝ,
        f (primeHardyKernelMap d) = primeFirstTraceClock d) ∧
    ¬ IsClosed {w : X × PrimeHardy | w.2 = F w.1} ∧
    ¬ IsSequentiallyClosableBetween T j := by
  have hlinear :=
    primeFirstTraceClock_closedRelationRiggingUniversality
      j T hsourceNorm hclockNorm
  have htopological :=
    primeFirstTraceClock_topologicalNonlinearRiggingNoEscapeUniversality
      j T hsourceNorm hclockNorm jTop F hsourceTopology hextendTop
  refine ⟨hlinear.1, ?_, hlinear.2.1,
    htopological.2.1,
    htopological.2.2.1,
    htopological.2.2.2.1,
    htopological.2.2.2.2⟩
  intro G hGclosed hgraph y hy
  exact primeFirstTraceClock_closedRelationExtension_contains_zeroVacuum
    G hGclosed hgraph y hy

end

end RHTower
