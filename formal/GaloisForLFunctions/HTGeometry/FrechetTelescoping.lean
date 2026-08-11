import GaloisForLFunctions.HTGeometry.FrechetOpenMappingStep

/-!
# Telescoping sums along a halving basis

A finite sum whose `i`-th term lies in the `(m+1+i)`-th member of a halving basis lies in the
`m`-th member.  This is the estimate that makes the partial sums of the open mapping series both
Cauchy and confined to a fixed neighbourhood.

* `halvingBasis_antitone` : a halving basis is decreasing.
* `halvingBasis_sum_mem` : **the telescoping bound.**
-/

namespace GaloisForLFunctions

open Filter Set Pointwise Topology

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- A halving basis is decreasing. -/
theorem halvingBasis_antitone {C : ℕ → Set E} (hzero : ∀ n, (0 : E) ∈ C n)
    (hhalf : ∀ n, C (n + 1) + C (n + 1) ⊆ C n) (n : ℕ) : C (n + 1) ⊆ C n := by
  intro x hx
  refine hhalf n (Set.mem_add.2 ⟨x, hx, 0, hzero (n + 1), ?_⟩)
  simp

/-- **The telescoping bound.**  A sum whose `i`-th term lies in `C (m+1+i)` lies in `C m`. -/
theorem halvingBasis_sum_mem {C : ℕ → Set E} (hzero : ∀ n, (0 : E) ∈ C n)
    (hhalf : ∀ n, C (n + 1) + C (n + 1) ⊆ C n) :
    ∀ (j m : ℕ) (a : ℕ → E), (∀ i, i < j → a i ∈ C (m + 1 + i)) →
      (∑ i ∈ Finset.range j, a i) ∈ C m := by
  intro j
  induction j with
  | zero =>
    intro m a _
    simpa using hzero m
  | succ k ih =>
    intro m a ha
    rw [Finset.sum_range_succ']
    refine hhalf m (Set.mem_add.2 ⟨∑ i ∈ Finset.range k, a (i + 1), ?_, a 0, ?_, rfl⟩)
    · refine ih (m + 1) (fun i => a (i + 1)) fun i hi => ?_
      have hmem := ha (i + 1) (by omega)
      have hidx : m + 1 + (i + 1) = m + 1 + 1 + i := by omega
      rwa [hidx] at hmem
    · have hmem := ha 0 (by omega)
      simpa using hmem

/-- Consecutive partial sums differ by an element of the basis. -/
theorem halvingBasis_sum_sub_mem {C : ℕ → Set E} (hzero : ∀ n, (0 : E) ∈ C n)
    (hhalf : ∀ n, C (n + 1) + C (n + 1) ⊆ C n) (a : ℕ → E) (m : ℕ)
    (ha : ∀ i, a i ∈ C (m + 1 + i)) (p q : ℕ) (hpq : p ≤ q) :
    (∑ i ∈ Finset.range q, a i) - (∑ i ∈ Finset.range p, a i) ∈ C (m + p) := by
  have hsplit : (∑ i ∈ Finset.range q, a i) - (∑ i ∈ Finset.range p, a i)
      = ∑ i ∈ Finset.range (q - p), a (p + i) := by
    have hq : q = p + (q - p) := by omega
    rw [hq, Finset.sum_range_add]
    simp
  rw [hsplit]
  refine halvingBasis_sum_mem hzero hhalf (q - p) (m + p) (fun i => a (p + i)) fun i _ => ?_
  have hmem := ha (p + i)
  have hidx : m + 1 + (p + i) = m + p + 1 + i := by omega
  rwa [hidx] at hmem

end GaloisForLFunctions
