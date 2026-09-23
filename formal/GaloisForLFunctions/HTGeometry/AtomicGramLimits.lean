import GaloisForLFunctions.HTGeometry.TotalGramMatrix

/-!
# The atomic Gram entries converge

Both atomic estimates are a fixed finite constant times a power of the height, so both vanish as the
height does: the diagonal converges to the atom's coefficient and the off-diagonal to zero.

The constants are sums of coefficient moduli over atom separations, fixed once the atoms and
coefficients are, so the convergence is immediate from the convergence of the power.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Finset

noncomputable section

open scoped Classical

/-- The constant in the atomic diagonal estimate. -/
def atomicDiagConst {d : ℕ} (a c : Fin d → ℝ) (l : Fin d) : ℝ :=
  ∑ j ∈ univ.erase l, ‖(c j : ℂ)‖ / (a j - a l) ^ (2 : ℕ)

/-- The constant in the atomic off-diagonal estimate. -/
def atomicOffDiagConst {d : ℕ} (a c : Fin d → ℝ) (l m : Fin d) : ℝ :=
  ∑ j, ‖(c j : ℂ)‖ * offDiagWeight a l m j

/-- **The atomic diagonal converges to the coefficient.** -/
theorem tendsto_atomicGram_diagonal_sub {d : ℕ} (a c : Fin d → ℝ)
    (ha : Function.Injective a) (l : Fin d) :
    Tendsto (fun y : ℝ => atomicGram a c y l l - ((c l : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun y : ℝ => y ^ (2 : ℕ) * atomicDiagConst a c l) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    refine le_trans (norm_atomicGram_diagonal_sub_le a c ha hy l) (le_of_eq ?_)
    rw [atomicDiagConst, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · have h : Tendsto (fun y : ℝ => y ^ (2 : ℕ) * atomicDiagConst a c l) (𝓝[≠] 0) (𝓝 0) := by
      have hy2 : Tendsto (fun y : ℝ => y ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
        simpa using this
      simpa using hy2.mul_const (atomicDiagConst a c l)
    exact h

/-- **The atomic off-diagonal converges to zero.** -/
theorem tendsto_atomicGram_offdiag {d : ℕ} (a c : Fin d → ℝ)
    (ha : Function.Injective a) {l m : Fin d} (hlm : l ≠ m) :
    Tendsto (fun y : ℝ => atomicGram a c y l m) (𝓝[≠] 0) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun y : ℝ => |y| * atomicOffDiagConst a c l m) ?_ ?_
  · have habs1 : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), |y| ≤ 1 := by
      have hmem : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), |y| ≤ 1 := by
        refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) one_pos) ?_
        intro y hy
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
        exact hy.le
      exact hmem.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, habs1] with y hy hy1
    refine le_trans (norm_atomicGram_offdiag_le a c ha hy hy1 hlm) (le_of_eq ?_)
    rw [atomicOffDiagConst, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · have habs : Tendsto (fun y : ℝ => |y|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have := (continuous_abs.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
      simpa using this
    simpa using habs.mul_const (atomicOffDiagConst a c l m)

end

end GaloisForLFunctions.HTGeometry
