import GaloisForLFunctions.HTGeometry.HausdorffCDDMeasureSource

/-!
# The Hausdorff quadrature weights

For a sequence `b` the level-`N` Hausdorff quadrature attaches to the node `k/N` the weight

`w(N,k) = C(N,k)·T(N,k)`,   `T(N,k) = (-1)^(N-k)·Δ^(N-k) b k`,

which is nonnegative exactly when `b` is completely monotone.  The whole construction rests on one
refinement identity: for `k ≤ N`,

`T(N,k) = T(N+1,k) + T(N+1,k+1)`,

which is the forward-difference recursion with its sign folded in.  Together with Pascal's rule it
makes the total mass independent of the level, so every level has mass `b 0`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The signed iterated difference attached to the node `k` at level `N`. -/
noncomputable def hausdorffCoeff (b : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (-1) ^ (N - k) * ((fwdDiff 1)^[N - k] b k)

/-- The level-`N` Hausdorff quadrature weight at the node `k`. -/
noncomputable def hausdorffWeight (b : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (N.choose k : ℝ) * hausdorffCoeff b N k

theorem hausdorffCoeff_nonneg {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b) (N k : ℕ) :
    0 ≤ hausdorffCoeff b N k := hb k (N - k)

theorem hausdorffWeight_nonneg {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b) (N k : ℕ) :
    0 ≤ hausdorffWeight b N k :=
  mul_nonneg (Nat.cast_nonneg _) (hausdorffCoeff_nonneg hb N k)

@[simp] theorem hausdorffCoeff_self (b : ℕ → ℝ) (N : ℕ) : hausdorffCoeff b N N = b N := by
  simp [hausdorffCoeff]

/-- One step of the forward-difference recursion. -/
theorem fwdDiff_iter_succ_apply (b : ℕ → ℝ) (j k : ℕ) :
    (fwdDiff 1)^[j + 1] b k = (fwdDiff 1)^[j] b (k + 1) - (fwdDiff 1)^[j] b k := by
  rw [Function.iterate_succ_apply']
  rfl

/-- **The refinement identity.**  Each level-`N` coefficient splits into the two coefficients
directly above it. -/
theorem hausdorffCoeff_refine (b : ℕ → ℝ) {N k : ℕ} (hk : k ≤ N) :
    hausdorffCoeff b N k = hausdorffCoeff b (N + 1) k + hausdorffCoeff b (N + 1) (k + 1) := by
  have h1 : N + 1 - k = (N - k) + 1 := by omega
  have h2 : N + 1 - (k + 1) = N - k := by omega
  rw [hausdorffCoeff, hausdorffCoeff, hausdorffCoeff, h1, h2,
    fwdDiff_iter_succ_apply b (N - k) k, pow_succ]
  ring

/-- **The total mass does not depend on the level.** -/
theorem sum_hausdorffWeight_succ (b : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range (N + 2), hausdorffWeight b (N + 1) k
      = ∑ k ∈ range (N + 1), hausdorffWeight b N k := by
  have hsplit : ∀ k ∈ range (N + 1), hausdorffWeight b N k
      = (N.choose k : ℝ) * hausdorffCoeff b (N + 1) k
        + (N.choose k : ℝ) * hausdorffCoeff b (N + 1) (k + 1) := by
    intro k hkmem
    have hk : k ≤ N := by
      have := Finset.mem_range.mp hkmem
      omega
    rw [hausdorffWeight, hausdorffCoeff_refine b hk]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- the first block loses its top term and gains the bottom one
  have hfirst : ∑ k ∈ range (N + 1), (N.choose k : ℝ) * hausdorffCoeff b (N + 1) k
      = hausdorffCoeff b (N + 1) 0
        + ∑ k ∈ range N, (N.choose (k + 1) : ℝ) * hausdorffCoeff b (N + 1) (k + 1) := by
    rw [Finset.sum_range_succ' (fun k => (N.choose k : ℝ) * hausdorffCoeff b (N + 1) k) N]
    simp [add_comm]
  have htop : ∑ k ∈ range (N + 1), (N.choose (k + 1) : ℝ) * hausdorffCoeff b (N + 1) (k + 1)
      = ∑ k ∈ range N, (N.choose (k + 1) : ℝ) * hausdorffCoeff b (N + 1) (k + 1) := by
    rw [Finset.sum_range_succ]
    have : N.choose (N + 1) = 0 := Nat.choose_succ_self N
    rw [this]
    simp
  have hgoal : ∑ k ∈ range (N + 2), hausdorffWeight b (N + 1) k
      = hausdorffCoeff b (N + 1) 0
        + (∑ k ∈ range (N + 1), (N.choose k : ℝ) * hausdorffCoeff b (N + 1) (k + 1)
          + ∑ k ∈ range (N + 1), (N.choose (k + 1) : ℝ) * hausdorffCoeff b (N + 1) (k + 1)) := by
    rw [Finset.sum_range_succ' (fun k => hausdorffWeight b (N + 1) k) (N + 1)]
    have hzero : hausdorffWeight b (N + 1) 0 = hausdorffCoeff b (N + 1) 0 := by
      simp [hausdorffWeight]
    rw [hzero, add_comm]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hausdorffWeight, Nat.choose_succ_succ]
    push_cast
    ring
  rw [hgoal, hfirst, htop]
  ring

/-- **Every level of the Hausdorff quadrature has total mass `b 0`.** -/
theorem sum_hausdorffWeight (b : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range (N + 1), hausdorffWeight b N k = b 0 := by
  induction N with
  | zero => simp [hausdorffWeight, hausdorffCoeff]
  | succ N ih => rw [sum_hausdorffWeight_succ b N, ih]

end GaloisForLFunctions.HTGeometry
