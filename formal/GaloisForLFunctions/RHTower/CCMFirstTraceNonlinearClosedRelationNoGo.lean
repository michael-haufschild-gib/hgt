import GaloisForLFunctions.RHTower.PrimeFirstTraceExactGraphClosureUniversalityLaw

/-!
# CCM first trace has no nonlinear closed single-valued Hilbert transport

The exact graph closure of the actual-prime first-trace clock is already known: every source
vector is paired with every response whose vacuum coordinate vanishes.  Previous consequences in
the corpus treated linear submodules and linear partial maps.

This module removes linearity completely.  Any closed *set-valued* relation containing the
algebraic first-trace graph contains the whole vertical zero-vacuum Hardy hyperplane.  It therefore
cannot be single-valued.  In particular, no function -- linear or nonlinear, continuous or
discontinuous -- can both extend the algebraic CCM first-trace clock and have a closed graph in the
intrinsic product Hilbert topology.

Thus nonlinear renormalization does not evade first-trace nonclosability inside the original
arithmetic-Schur Hilbert completion.  A surviving CCM transport must change topology, become
genuinely multivalued, or discard the first-valuation response.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Graph of an arbitrary, possibly nonlinear map between topological spaces. -/
def nonlinearMapGraph
    {E K : Type*} (F : E → K) : Set (E × K) :=
  {w | w.2 = F w.1}

/-- **Closed-graph collision law.**  If source points converge to `x`, their prescribed
responses converge to `y`, and `y ≠ F x`, then no map interpolating those points has closed
graph.  No linear, metric, normed, or continuity structure is used. -/
theorem nonlinearMapGraph_not_closed_of_limitCollision
    {E K : Type*} [TopologicalSpace E] [TopologicalSpace K]
    (F : E → K) (x : ℕ → E) (y : ℕ → K) (xLim : E) (yLim : K)
    (hx : Tendsto x atTop (𝓝 xLim))
    (hy : Tendsto y atTop (𝓝 yLim))
    (hinterpolate : ∀ n, y n = F (x n))
    (hcollision : yLim ≠ F xLim) :
    ¬ IsClosed (nonlinearMapGraph F) := by
  intro hclosed
  have hlimit : (xLim, yLim) ∈ nonlinearMapGraph F := by
    apply hclosed.mem_of_tendsto (hx.prodMk_nhds hy)
    exact Filter.Eventually.of_forall fun n => hinterpolate n
  exact hcollision hlimit

/-- A relation in the product Hilbert space is single-valued over its first coordinate.  No
linearity, total-domain, or regularity assumption is included. -/
def IsSingleValuedHilbertRelation
    (G : Set (WithLp 2 (PrimeHardy × PrimeHardy))) : Prop :=
  ∀ x y z : PrimeHardy,
    WithLp.toLp 2 (x, y) ∈ G →
    WithLp.toLp 2 (x, z) ∈ G →
    y = z

/-- Every closed relation containing the actual-prime first-trace graph contains every vertical
zero-vacuum response.  This is the nonlinear/set-valued strengthening of the earlier closed
linear-relation theorem. -/
theorem primeFirstTraceClock_closedRelation_contains_zeroVacuum
    (G : Set (WithLp 2 (PrimeHardy × PrimeHardy)))
    (hGclosed : IsClosed G)
    (hgraph :
      (realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock :
        Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G)
    (y : PrimeHardy) (hy : y 0 = 0) :
    WithLp.toLp 2 ((0 : PrimeHardy), y) ∈ G := by
  apply closure_minimal hgraph hGclosed
  rw [← Submodule.topologicalClosure_coe]
  exact (primeFirstTraceClock_pair_mem_graphClosure_iff 0 y).2 hy

/-- **Nonlinear closed-relation no-go.**  No closed single-valued relation can contain the
actual-prime first-trace graph.  The contradiction uses the nonzero first Hardy basis vector in
the forced vertical zero-vacuum fiber. -/
theorem primeFirstTraceClock_no_closed_singleValuedHilbertRelation :
    ¬ ∃ G : Set (WithLp 2 (PrimeHardy × PrimeHardy)),
      IsClosed G ∧
      (realLinearGraphSubmodule primeHardyKernelMap primeFirstTraceClock :
        Set (WithLp 2 (PrimeHardy × PrimeHardy))) ⊆ G ∧
      IsSingleValuedHilbertRelation G := by
  rintro ⟨G, hGclosed, hgraph, hsingle⟩
  let e₁ : PrimeHardy := lp.single 2 1 1
  have he₁zero : e₁ 0 = 0 := by
    simp [e₁]
  have hzero :
      WithLp.toLp 2 ((0 : PrimeHardy), (0 : PrimeHardy)) ∈ G := by
    exact hgraph ⟨0, by simp⟩
  have he₁ :
      WithLp.toLp 2 ((0 : PrimeHardy), e₁) ∈ G :=
    primeFirstTraceClock_closedRelation_contains_zeroVacuum
      G hGclosed hgraph e₁ he₁zero
  exact primeHardy_basisOne_ne_zero (hsingle 0 0 e₁ hzero he₁).symm

/-- Graph of an arbitrary, possibly nonlinear, map between the intrinsic prime Hardy spaces. -/
def primeHardyNonlinearGraph (F : PrimeHardy → PrimeHardy) :
    Set (WithLp 2 (PrimeHardy × PrimeHardy)) :=
  {w | w.ofLp.2 = F w.ofLp.1}

theorem primeHardyNonlinearGraph_singleValued (F : PrimeHardy → PrimeHardy) :
    IsSingleValuedHilbertRelation (primeHardyNonlinearGraph F) := by
  intro x y z hy hz
  change y = F x at hy
  change z = F x at hz
  exact hy.trans hz.symm

/-- **No nonlinear closed-graph escape.**  There is no everywhere-defined map with closed graph
which agrees with the exact arithmetic first-trace clock on the algebraic prime source.  This
requires neither linearity nor continuity of the proposed map. -/
theorem primeFirstTraceClock_no_nonlinear_closedGraph_extension :
    ¬ ∃ F : PrimeHardy → PrimeHardy,
      IsClosed (primeHardyNonlinearGraph F) ∧
      ∀ d : Nat.Primes →₀ ℝ,
        F (primeHardyKernelMap d) = primeFirstTraceClock d := by
  rintro ⟨F, hclosed, hextend⟩
  apply primeFirstTraceClock_no_closed_singleValuedHilbertRelation
  refine ⟨primeHardyNonlinearGraph F, hclosed, ?_,
    primeHardyNonlinearGraph_singleValued F⟩
  rintro w ⟨d, rfl⟩
  change primeFirstTraceClock d = F (primeHardyKernelMap d)
  exact (hextend d).symm

/-- **Source-topology escape obstruction.**  Let `E` be any topological source realization and
`j` any realization of finite actual-prime packets.  If `j` preserves the explicit cofinal
source-null convergence, then no arbitrary map `F : E → PrimeHardy` can both interpolate the
exact CCM first trace and have closed graph.  Thus a closed nonlinear repair must change that
source convergence itself; changing normed coordinates, completeness, or Hilbert structure is
irrelevant. -/
theorem primeFirstTraceClock_no_sourceConvergencePreserving_closedGraph_transport
    {E : Type*} [TopologicalSpace E]
    (j : (Nat.Primes →₀ ℝ) → E)
    (F : E → PrimeHardy)
    (hsource :
      Tendsto (fun n => j (primeFirstTraceNullSequence n))
        atTop (𝓝 (j 0)))
    (hextend : ∀ d : Nat.Primes →₀ ℝ,
      F (j d) = primeFirstTraceClock d) :
    ¬ IsClosed (nonlinearMapGraph F) := by
  apply nonlinearMapGraph_not_closed_of_limitCollision
    F
    (fun n => j (primeFirstTraceNullSequence n))
    (fun n => primeFirstTraceClock (primeFirstTraceNullSequence n))
    (j 0)
    (lp.single 2 1 1)
    hsource
    tendsto_primeFirstTraceClock_nullSequence
    (fun n => (hextend _).symm)
  have hzero : F (j 0) = 0 := by
    simpa using hextend 0
  rw [hzero]
  exact primeHardy_basisOne_ne_zero

end

end RHTower
