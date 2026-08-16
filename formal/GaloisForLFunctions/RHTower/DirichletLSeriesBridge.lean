import GaloisForLFunctions.RHTower.DirichletUniqueness

/-!
# Bridge to the `LSeries` indexing

The conditional-convergence development here indexes a Dirichlet series from zero,

```text
∑_{n ≥ 0} a_n (n+1)^{−s} ,
```

while mathlib's `LSeries` and the corpus's Perron engine index from one through `LSeries.term`.  The
two conventions are related by a shift of the coefficient sequence, and the partial sums correspond
exactly:

```text
dirichletPartialSum (fun n => b (n+1)) N s  =  ∑_{n ∈ Icc 1 N} LSeries.term b s n .
```

This is what lets the abscissa theory, the coefficient estimates and the uniqueness theorem proved
here be applied to objects stated in the `LSeries` convention — in particular to the smoothed Perron
summation formula of `QuietCrossingRigidity`, which is stated for `LSeries`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The shifted kernel in the two conventions agree. -/
theorem term_succ_eq (b : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term b s (n + 1) = b (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
  congr 2
  push_cast
  ring

/-- **The partial sums agree under the shift of indexing.** -/
theorem dirichletPartialSum_eq_sum_term (b : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    dirichletPartialSum (fun n => b (n + 1)) N s
      = ∑ n ∈ Finset.Icc 1 N, LSeries.term b s n := by
  have himg : Finset.Icc 1 N
      = Finset.map ⟨fun n => n + 1, fun a b h => by simpa using h⟩ (Finset.range N) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨m - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_map, dirichletPartialSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact (term_succ_eq b s n).symm

/-- Convergence in the zero-indexed convention is convergence of the `LSeries` partial sums. -/
theorem convergesAt_iff_tendsto_sum_term (b : ℕ → ℂ) (s : ℂ) :
    DirichletConvergesAt (fun n => b (n + 1)) s
      ↔ ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term b s n) atTop (𝓝 L) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, hL.congr fun N => dirichletPartialSum_eq_sum_term b N s⟩
  · rintro ⟨L, hL⟩
    exact ⟨L, hL.congr fun N => (dirichletPartialSum_eq_sum_term b N s).symm⟩

/-- Uniform convergence transfers to the `LSeries` partial sums. -/
theorem tendstoUniformlyOn_sum_term_of_uniformlyConvergesOn {b : ℕ → ℂ} {x : ℝ}
    (h : DirichletUniformlyConvergesOn (fun n => b (n + 1)) x) :
    ∃ F : ℂ → ℂ, TendstoUniformlyOn
      (fun N s => ∑ n ∈ Finset.Icc 1 N, LSeries.term b s n) F atTop {s : ℂ | x ≤ s.re} := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F, hF.congr ?_⟩
  filter_upwards with N
  intro s _
  exact dirichletPartialSum_eq_sum_term b N s

end GaloisForLFunctions.RHTower

end
