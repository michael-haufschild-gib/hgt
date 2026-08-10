import GaloisForLFunctions.RHTower.Sieve.GhsBlockPerronBound

/-!
# The outer polynomial decomposes over the blocks

The blocks of the geometric partition telescope: `(A_k, A_{k+1}]` for a monotone family `a`, whose
union is `(a 0, a K]`.  So the outer weight of the whole range is the pointwise sum of the block
weights, and — since all of them are finitely supported — the Dirichlet series adds too:

```text
L(ghsOuterBlock f N (a 0) (a K), s) = ∑_{k < K} L(ghsOuterBlock f N (a k) (a (k+1)), s) .
```

Combined with the triangle inequality this turns the vertical integral of the whole outer range
into the sum of the `K` per-block integrals, each of which `ghs_block_perron_bound` bounds.

There is no analysis here: a finitely supported Dirichlet series is a finite sum, and a partition
of its support partitions that sum.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **Two adjacent blocks add.** -/
theorem ghsOuterBlock_split (f : ℕ → ℂ) (N : ℕ) {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) (p : ℕ) :
    ghsOuterBlock f N A C p = ghsOuterBlock f N A B p + ghsOuterBlock f N B C p := by
  classical
  by_cases hp : Nat.Prime p
  · have hm : ∀ X Y : ℕ, (p ∈ Nat.primesLE Y \ Nat.primesLE X) ↔ (p ≤ Y ∧ X < p) := by
      intro X Y
      constructor
      · intro h
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at h
        refine ⟨h.1.1, ?_⟩
        by_contra hc
        exact h.2 ⟨by omega, hp⟩
      · intro h
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
        exact ⟨⟨h.1, hp⟩, by intro hc; omega⟩
    rcases le_or_gt p A with hpA | hpA
    · rw [ghsOuterBlock, ghsOuterBlock, ghsOuterBlock,
        if_neg (by simp only [hm]; omega), if_neg (by simp only [hm]; omega),
        if_neg (by simp only [hm]; omega)]
      ring
    rcases le_or_gt p B with hpB | hpB
    · rw [ghsOuterBlock, ghsOuterBlock, ghsOuterBlock,
        if_pos (by simp only [hm]; omega), if_pos (by simp only [hm]; omega),
        if_neg (by simp only [hm]; omega)]
      ring
    rcases le_or_gt p C with hpC | hpC
    · rw [ghsOuterBlock, ghsOuterBlock, ghsOuterBlock,
        if_pos (by simp only [hm]; omega), if_neg (by simp only [hm]; omega),
        if_pos (by simp only [hm]; omega)]
      ring
    · rw [ghsOuterBlock, ghsOuterBlock, ghsOuterBlock,
        if_neg (by simp only [hm]; omega), if_neg (by simp only [hm]; omega),
        if_neg (by simp only [hm]; omega)]
      ring
  · have hnot : ∀ X Y : ℕ, p ∉ Nat.primesLE Y \ Nat.primesLE X := by
      intro X Y h
      exact hp (prime_of_mem_block h)
    simp only [ghsOuterBlock, if_neg (hnot A C), if_neg (hnot A B), if_neg (hnot B C)]
    ring

/-- **The blocks telescope.** -/
theorem ghsOuterBlock_telescope (f : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ} (ha : Monotone a) (K : ℕ)
    (p : ℕ) :
    ghsOuterBlock f N (a 0) (a K) p
      = ∑ k ∈ Finset.range K, ghsOuterBlock f N (a k) (a (k + 1)) p := by
  classical
  induction K with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, ghsOuterBlock, if_neg (by simp)]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact ghsOuterBlock_split f N (ha (Nat.zero_le K)) (ha (Nat.le_succ K)) p

/-- The union of the blocks supports every block. -/
theorem block_subset_of_monotone {a : ℕ → ℕ} (ha : Monotone a) {K k : ℕ} (hk : k < K) :
    Nat.primesLE (a (k + 1)) \ Nat.primesLE (a k)
      ⊆ Nat.primesLE (a K) \ Nat.primesLE (a 0) := by
  intro q hq
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hq ⊢
  obtain ⟨⟨hq1, hqp⟩, hq2⟩ := hq
  refine ⟨⟨le_trans hq1 (ha (by omega)), hqp⟩, ?_⟩
  intro hc
  exact hq2 ⟨le_trans hc.1 (ha (Nat.zero_le k)), hqp⟩

/-- **The Dirichlet series of the whole outer range is the sum over the blocks.** -/
theorem LSeries_ghsOuterBlock_telescope (f : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ} (ha : Monotone a)
    (K : ℕ) (σ y : ℝ) :
    LSeries (ghsOuterBlock f N (a 0) (a K)) ((σ : ℂ) + (y : ℝ) * I)
      = ∑ k ∈ Finset.range K,
          LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I) := by
  classical
  set S : Finset ℕ := Nat.primesLE (a K) \ Nat.primesLE (a 0) with hS
  have hS0 : (0 : ℕ) ∉ S := zero_notMem_block (a 0) (a K)
  have hall : ∀ i : ℕ, ghsOuterBlock f N (a 0) (a K) i ≠ 0 → i ∈ S := fun i h =>
    ghsOuterBlock_supp h
  have hpart : ∀ k, k < K → ∀ i : ℕ, ghsOuterBlock f N (a k) (a (k + 1)) i ≠ 0 → i ∈ S :=
    fun k hk i h => block_subset_of_monotone ha hk (ghsOuterBlock_supp h)
  rw [LSeries_eq_logPoly_of_support hS0 hall σ y]
  have hrhs : ∀ k ∈ Finset.range K,
      LSeries (ghsOuterBlock f N (a k) (a (k + 1))) ((σ : ℂ) + (y : ℝ) * I)
        = logPoly (fun i => ghsOuterBlock f N (a k) (a (k + 1)) i
            * ((((i : ℝ) ^ (-σ) : ℝ)) : ℂ)) S (-y / (2 * Real.pi)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact LSeries_eq_logPoly_of_support hS0 (hpart k hk) σ y
  rw [Finset.sum_congr rfl hrhs]
  rw [logPoly]
  simp only [logPoly]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ghsOuterBlock_telescope f N ha K i, Finset.sum_mul, Finset.sum_mul]

end RHTower.Sieve

end
