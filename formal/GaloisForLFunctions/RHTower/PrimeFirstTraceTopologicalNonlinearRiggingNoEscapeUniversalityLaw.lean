import GaloisForLFunctions.RHTower.PrimeFirstTraceExactGraphClosureUniversalityLaw
import GaloisForLFunctions.RHTower.ArithmeticSchurExactNormRiggingNoGo

/-!
# Prime first-trace topological, nonlinear, and rigging no-escape law

The same explicit graph-null sequence controls intrinsic closed relations, arbitrary nonlinear
closed graphs, topology-preserving source realizations, and exact-norm complete riggings.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- **Prime first-trace topological/nonlinear/rigging no-escape universality.** The exact graph
closure, all single-valued closed-relation failures, and exact-norm rigging nonclosability hold
simultaneously. -/
theorem primeFirstTraceClock_topologicalNonlinearRiggingNoEscapeUniversality
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
  have hrelation :
      ¬ ∃ G : Set (WithLp 2 (PrimeHardy × PrimeHardy)),
        IsClosed G ∧
        (realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock :
          Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G ∧
        ∀ x y z : PrimeHardy,
          WithLp.toLp 2 (x, y) ∈ G →
          WithLp.toLp 2 (x, z) ∈ G →
          y = z := by
    rintro ⟨G, hGclosed, hgraph, hsingle⟩
    let e₁ : PrimeHardy := lp.single 2 1 1
    have he₁zero : e₁ 0 = 0 := by
      simp [e₁]
    have hzero :
        WithLp.toLp 2 ((0 : PrimeHardy), (0 : PrimeHardy)) ∈ G := by
      exact hgraph ⟨0, by simp⟩
    have he₁ :
        WithLp.toLp 2 ((0 : PrimeHardy), e₁) ∈ G := by
      apply closure_minimal hgraph hGclosed
      rw [← Submodule.topologicalClosure_coe]
      exact (primeFirstTraceClock_pair_mem_graphClosure_iff 0 e₁).2 he₁zero
    exact primeHardy_basisOne_ne_zero (hsingle 0 0 e₁ hzero he₁).symm
  have hnonlinear :
      ¬ ∃ f : PrimeHardy → PrimeHardy,
        IsClosed
          {w : WithLp 2 (PrimeHardy × PrimeHardy) |
            w.ofLp.2 = f w.ofLp.1} ∧
        ∀ d : Nat.Primes →₀ ℝ,
          f (primeHardyKernelMap d) = primeFirstTraceClock d := by
    rintro ⟨f, hclosed, hextend⟩
    apply hrelation
    refine ⟨
      {w : WithLp 2 (PrimeHardy × PrimeHardy) |
        w.ofLp.2 = f w.ofLp.1},
      hclosed, ?_, ?_⟩
    · rintro w ⟨d, rfl⟩
      change primeFirstTraceClock d = f (primeHardyKernelMap d)
      exact (hextend d).symm
    · intro x y z hy hz
      change y = f x at hy
      change z = f x at hz
      exact hy.trans hz.symm
  have htopological :
      ¬ IsClosed {w : X × PrimeHardy | w.2 = F w.1} := by
    intro hclosed
    let e₁ : PrimeHardy := lp.single 2 1 1
    have hlimit :
        (jTop 0, e₁) ∈ {w : X × PrimeHardy | w.2 = F w.1} := by
      apply hclosed.mem_of_tendsto
        (hsourceTopology.prodMk_nhds tendsto_primeFirstTraceClock_nullSequence)
      exact Filter.Eventually.of_forall fun n => (hextendTop _).symm
    have hzero : F (jTop 0) = 0 := by
      simpa using hextendTop 0
    change e₁ = F (jTop 0) at hlimit
    rw [hzero] at hlimit
    exact primeHardy_basisOne_ne_zero hlimit
  exact ⟨primeFirstTraceClock_pair_mem_graphClosure_iff,
    hrelation,
    hnonlinear,
    htopological,
    arithmeticSchurExactNormRigging_not_closable
      j T hsourceNorm hclockNorm⟩

end

end RHTower
