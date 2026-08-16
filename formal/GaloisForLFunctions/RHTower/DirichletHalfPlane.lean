import GaloisForLFunctions.RHTower.DirichletAbelConvergence

/-!
# Convergence propagates to the right

If an ordinary Dirichlet series converges at `s₀` then it converges at every `s` with
`Re s > Re s₀`.  The proof is Abel summation applied to the shifted coefficients `a_n (n+1)^{−s₀}`,
whose partial sums are bounded precisely because the series converges at `s₀`; the remaining
exponent `s − s₀` has positive real part, which is the hypothesis of the Abel convergence theorem.

This is the half-plane property that makes an abscissa of convergence well defined, and it is the
step that separates conditional convergence from the absolute convergence mathlib develops: the
half-plane of absolute convergence can be strictly smaller.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **Convergence at `s₀` propagates to every `s` further right.** -/
theorem tendsto_dirichlet_partialSum_of_re_lt {a : ℕ → ℂ} {s₀ s : ℂ}
    (h₀ : ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
        a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s₀)) atTop (𝓝 L))
    (hs : s₀.re < s.re) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
        a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := h₀
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hL₀.cauchySeq.isBounded_range
  have hCb : ∀ N, ‖∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s₀)‖ ≤ C :=
    fun N => hC _ (Set.mem_range_self N)
  have hre : 0 < (s - s₀).re := by
    rw [Complex.sub_re]
    linarith
  obtain ⟨L, hL⟩ := tendsto_dirichlet_partialSum_of_bounded hCb hre
  refine ⟨L, hL.congr fun N => Finset.sum_congr rfl fun n _ => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
  rw [mul_assoc, ← Complex.cpow_add _ _ hne]
  congr 2
  ring

end GaloisForLFunctions.RHTower

end
