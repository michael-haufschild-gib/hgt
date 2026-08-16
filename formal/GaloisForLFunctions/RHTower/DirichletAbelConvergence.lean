import GaloisForLFunctions.RHTower.DirichletIncrementSummable

/-!
# Bounded coefficient sums give convergence in the right half-plane

Abel summation, assembled.  If the partial sums of the coefficients are bounded then the Dirichlet
series converges everywhere in `Re s > 0`:

```text
∑_{n<N} a_n (n+1)^{−s}
  = (N)^{−s} A_N − ∑_{i<N−1} ((i+2)^{−s} − (i+1)^{−s}) A_{i+1} ,
```

the boundary term vanishes because `N^{−Re s} → 0` while `A_N` stays bounded, and the sum converges
absolutely because the kernel increments do.

Note that the conclusion is convergence of the partial sums, not summability: a Dirichlet series
outside its half-plane of absolute convergence is only conditionally convergent, so the ordered
limit is the right statement.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **Bounded coefficient partial sums give convergence for `Re s > 0`.** -/
theorem tendsto_dirichlet_partialSum_of_bounded {a : ℕ → ℂ} {C : ℝ}
    (hC : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ C) {s : ℂ} (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      atTop (𝓝 L) := by
  classical
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hbdef
  set A : ℕ → ℂ := fun k => ∑ n ∈ Finset.range k, a n with hAdef
  have hbsucc : ∀ i : ℕ, b (i + 1) = (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
    intro i
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = (i : ℝ) + 2 := by push_cast; ring
    simp only [hbdef, hcast]
  have hincr : Summable (fun i : ℕ => ‖b (i + 1) - b i‖) := by
    refine (summable_norm_cpow_increment hs).congr fun i => ?_
    rw [hbsucc i, hbdef, norm_sub_rev]
  have hsummand : Summable (fun i : ℕ => (b (i + 1) - b i) * A (i + 1)) := by
    refine Summable.of_norm_bounded (g := fun i => ‖b (i + 1) - b i‖ * C)
      (hincr.mul_right C) fun i => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC (i + 1)) (norm_nonneg _)
  obtain ⟨T, hT⟩ := hsummand
  refine ⟨-T, ?_⟩
  -- the Abel identity
  have habel : ∀ N : ℕ, (∑ n ∈ Finset.range N, a n * b n)
      = b (N - 1) * A N - ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1) := by
    intro N
    have h := Finset.sum_range_by_parts b a N
    simp only [smul_eq_mul] at h
    rw [show (∑ n ∈ Finset.range N, a n * b n) = ∑ n ∈ Finset.range N, b n * a n from
      Finset.sum_congr rfl fun n _ => mul_comm _ _]
    exact h
  -- the sum converges
  have hTend1 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1))
      atTop (𝓝 T) :=
    hT.tendsto_sum_nat.comp (Filter.tendsto_sub_atTop_nat 1)
  -- the boundary term vanishes
  have hTend2 : Tendsto (fun N : ℕ => b (N - 1) * A N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (tendsto_rpow_neg_nat_atTop hs).mul_const C)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN]
        norm_num
      rw [this]
      ring
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (1 : ℕ) ≤ N := hN
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hbnorm : ‖b (N - 1)‖ = (N : ℝ) ^ (-s.re) := by
      rw [hbdef]
      simp only
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      congr 1
    rw [norm_mul, hbnorm]
    exact mul_le_mul_of_nonneg_left (hC N) (Real.rpow_nonneg hNpos.le _)
  -- combine
  have hcomb : Tendsto (fun N : ℕ => b (N - 1) * A N
      - ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1)) atTop (𝓝 (0 - T)) :=
    hTend2.sub hTend1
  have hfinal : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * b n) atTop (𝓝 (0 - T)) :=
    hcomb.congr fun N => (habel N).symm
  simp only [hbdef] at hfinal
  rw [zero_sub] at hfinal
  exact hfinal

end GaloisForLFunctions.RHTower

end
