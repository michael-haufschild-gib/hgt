import GaloisForLFunctions.RHTower.ArithmeticLogClockFiniteJetSaturation

/-!
# Bounded infinite-completion saturation of the arithmetic logarithmic clock

The finite-jet theorem proves that the actual-prime logarithmic clock has dense graph in its two
Hardy pivots after every finite trace subtraction.  This module closes the corresponding
infinite-target question for every bounded completion at once.

Let `C : H² → K` be any bounded Hilbert-space postprocessing.  It may retain infinitely many
Gamma jets, Sonin channels, shell labels, or other completed coordinates.  Postcomposing the
order-`m` prime clock with `C` cannot restore source/clock coupling: for every `x,y ∈ H²`,

`(x, C y) ∈ closure Graph(i, C A_m)`.

Thus every nonzero bounded completion leaves a nonzero vertical multivalue.  If `C` has dense
range, the completed graph again fills the whole product `H² ⊕ K`.  The proof is not a finite
truncation argument.  An annihilator `(u,v)` for the completed graph pulls back through the
Hilbert adjoint to an annihilator `(u,C* v)` for the original graph.  Actual-prime logarithmic
rigidity kills both pulled-back components, which yields the claimed decoupling.

Consequently a complete factorial Gamma conormal can repair the CCM scalarization only by
changing the source topology before the Hardy pivot or by using a genuinely unbounded
pre-scalarization graph.  No nonzero bounded all-depth sewing after a finite trace can do so.

No Xi zero, RH assumption, numerical computation, or nonstandard axiom is used.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The order-`m` actual-prime clock followed by an arbitrary bounded Hilbert completion. -/
def primeBoundedPostprocessedTraceClock
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (m : ℕ) (C : PrimeHardy →L[ℝ] K) :
    (Nat.Primes →₀ ℝ) →ₗ[ℝ] K :=
  C.toLinearMap.comp (primeFiniteTraceClock m)

@[simp] theorem primeBoundedPostprocessedTraceClock_apply
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (m : ℕ) (C : PrimeHardy →L[ℝ] K) (d : Nat.Primes →₀ ℝ) :
    primeBoundedPostprocessedTraceClock m C d =
      C (primeFiniteTraceClock m d) := rfl

/-- **Dense bounded-completion saturation.**  Every bounded infinite completion with dense range
still has maximally multivalued graph closure. -/
theorem primeBoundedPostprocessedTraceClock_graphClosure_eq_top
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (m : ℕ) (C : PrimeHardy →L[ℝ] K) (hC : DenseRange C) :
    (realLinearGraphSubmodule primeHardyKernelMap
      (primeBoundedPostprocessedTraceClock m C)).topologicalClosure = ⊤ := by
  apply realLinearGraphSubmodule_closure_eq_top_of_annihilator
  intro x z h
  have hrel : PrimeTailLogRelation m x (C.adjoint z) := by
    intro p
    have hp := h (Finsupp.single p 1)
    rw [primeBoundedPostprocessedTraceClock_apply,
      ← ContinuousLinearMap.adjoint_inner_right] at hp
    simpa [primeFiniteTraceClock_single, inner_smul_left] using hp
  obtain ⟨hx, hadj⟩ := primeTailLogRelation_eq_zero m hrel
  refine ⟨hx, ?_⟩
  have hzeroOn : (fun y : PrimeHardy => inner ℝ (C y) z) = fun _ => 0 := by
    funext y
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj]
    simp
  have hzero : (fun w : K => inner ℝ w z) = fun _ => 0 := by
    apply hC.equalizer (by fun_prop) continuous_const
    exact hzeroOn
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  exact congrFun hzero z

/-- **Source-decoupling law.**  No density assumption is required: every source vector can be
paired in the completed graph closure with every vector in the actual range of the bounded
postprocessor. -/
theorem primeBoundedPostprocessedTraceClock_pair_mem_graphClosure
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (m : ℕ) (C : PrimeHardy →L[ℝ] K) (x y : PrimeHardy) :
    WithLp.toLp 2 (x, C y) ∈
      (realLinearGraphSubmodule primeHardyKernelMap
        (primeBoundedPostprocessedTraceClock m C)).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  rw [Submodule.mem_orthogonal']
  intro z hz
  have hz' := (Submodule.mem_orthogonal
    (realLinearGraphSubmodule primeHardyKernelMap
      (primeBoundedPostprocessedTraceClock m C)) z).mp hz
  have hrel : PrimeTailLogRelation m z.ofLp.1 (C.adjoint z.ofLp.2) := by
    intro p
    have hp := hz' (WithLp.toLp 2
      (primeHardyKernelMap (Finsupp.single p 1),
        primeBoundedPostprocessedTraceClock m C (Finsupp.single p 1)))
      ⟨Finsupp.single p 1, rfl⟩
    rw [WithLp.prod_inner_apply,
      primeBoundedPostprocessedTraceClock_apply,
      ← ContinuousLinearMap.adjoint_inner_right] at hp
    simpa [WithLp.prod_inner_apply, primeFiniteTraceClock_single,
      inner_smul_left] using hp
  obtain ⟨hzx, hzad⟩ := primeTailLogRelation_eq_zero m hrel
  rw [WithLp.prod_inner_apply]
  change inner ℝ x z.ofLp.1 + inner ℝ (C y) z.ofLp.2 = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, hzx, hzad]
  simp

/-- Every nonzero bounded completion leaves a nonzero vertical multivalue in the closed graph. -/
theorem primeBoundedPostprocessedTraceClock_exists_nonzero_vertical
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (m : ℕ) (C : PrimeHardy →L[ℝ] K) (hC : ∃ y, C y ≠ 0) :
    ∃ z : K, z ≠ 0 ∧
      WithLp.toLp 2 ((0 : PrimeHardy), z) ∈
        (realLinearGraphSubmodule primeHardyKernelMap
          (primeBoundedPostprocessedTraceClock m C)).topologicalClosure := by
  obtain ⟨y, hy⟩ := hC
  exact ⟨C y, hy,
    primeBoundedPostprocessedTraceClock_pair_mem_graphClosure m C 0 y⟩

/-- **Universal failure of bounded source domination.**  A nonzero bounded completion admits no
global estimate by the Hardy source norm on actual-prime packets.  Such an estimate would put the
graph in a closed norm cone, while source decoupling puts a nonzero vertical vector in its closure.

This rules out every global linear contraction or finite-constant graph estimate obtained by
bounded Gamma/Sonin postprocessing after the Hardy pivot. -/
theorem primeBoundedPostprocessedTraceClock_no_global_source_bound
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (m : ℕ) (C : PrimeHardy →L[ℝ] K) (hC : ∃ y, C y ≠ 0) :
    ¬ ∃ M : ℝ, ∀ d : Nat.Primes →₀ ℝ,
      ‖primeBoundedPostprocessedTraceClock m C d‖ ≤
        M * ‖primeHardyKernelMap d‖ := by
  rintro ⟨M, hM⟩
  let G := realLinearGraphSubmodule primeHardyKernelMap
    (primeBoundedPostprocessedTraceClock m C)
  let S : Set (WithLp 2 (PrimeHardy × K)) :=
    {w | ‖w.ofLp.2‖ ≤ M * ‖w.ofLp.1‖}
  have hS : IsClosed S := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have hGS : (G : Set (WithLp 2 (PrimeHardy × K))) ⊆ S := by
    rintro w ⟨d, rfl⟩
    simpa [S] using hM d
  have hclosure :
      (G.topologicalClosure : Set (WithLp 2 (PrimeHardy × K))) ⊆ S := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal hGS hS
  obtain ⟨y, hy⟩ := hC
  have hv := primeBoundedPostprocessedTraceClock_pair_mem_graphClosure m C 0 y
  have hineq := hclosure hv
  change ‖C y‖ ≤ M * ‖(0 : PrimeHardy)‖ at hineq
  simp only [norm_zero, mul_zero] at hineq
  exact hy (norm_eq_zero.mp (le_antisymm hineq (norm_nonneg _)))

end

end RHTower
