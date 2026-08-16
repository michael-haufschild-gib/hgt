import GaloisForLFunctions.RHTower.DirichletAbscissa

/-!
# Uniform convergence gives a bounded sum

Each partial sum of an ordinary Dirichlet series is bounded on a closed half-plane `Re s ≥ x`, by
the finite quantity `∑_{n<N} ‖a_n‖ (n+1)^{−x}`, simply because `(n+1)^{−Re s} ≤ (n+1)^{−x}` there.
A uniform limit of such functions is therefore bounded as well, so uniform convergence on a closed
half-plane produces a bounded sum function, and

```text
σ_bdd  ≤  σ_u .
```

This is the easy half of the comparison underlying Bohr's theorem.  The hard half — that a bounded
holomorphic *continuation* forces uniform convergence — is the classical theorem, and note that it
concerns a strictly stronger notion of boundedness than the one used here: `DirichletBoundedSumOn`
asks the series to converge on the half-plane, whereas Bohr's `σ_b` allows the bounded function to
be an analytic continuation beyond the region of convergence.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **Each partial sum is bounded on a closed half-plane.** -/
theorem norm_dirichletPartialSum_le (a : ℕ → ℂ) {x : ℝ} (N : ℕ) {s : ℂ} (hs : x ≤ s.re) :
    ‖dirichletPartialSum a N s‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ * ((n : ℝ) + 1) ^ (-x) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hexp : ((-s).re) ≤ -x := by
    rw [Complex.neg_re]
    linarith
  have hle : ((n : ℝ) + 1) ^ ((-s).re) ≤ ((n : ℝ) + 1) ^ (-x) :=
    Real.rpow_le_rpow_of_exponent_le hone hexp
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

/-- The series converges on the closed half-plane `Re s ≥ x` to a bounded function. -/
def DirichletBoundedSumOn (a : ℕ → ℂ) (x : ℝ) : Prop :=
  ∃ (F : ℂ → ℂ) (C : ℝ), (∀ s : ℂ, x ≤ s.re → ‖F s‖ ≤ C) ∧
    ∀ s : ℂ, x ≤ s.re → Tendsto (fun N => dirichletPartialSum a N s) atTop (𝓝 (F s))

/-- **Uniform convergence on a closed half-plane gives a bounded sum there.** -/
theorem DirichletUniformlyConvergesOn.boundedSumOn {a : ℕ → ℂ} {x : ℝ}
    (h : DirichletUniformlyConvergesOn a x) : DirichletBoundedSumOn a x := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop).1
    ((Metric.tendstoUniformlyOn_iff.1 hF) 1 zero_lt_one)
  refine ⟨F, 1 + ∑ n ∈ Finset.range N₀, ‖a n‖ * ((n : ℝ) + 1) ^ (-x), fun s hs => ?_,
    fun s hs => hF.tendsto_at hs⟩
  have hclose : dist (F s) (dirichletPartialSum a N₀ s) < 1 := hN₀ N₀ le_rfl s hs
  have hpart := norm_dirichletPartialSum_le a (x := x) N₀ hs
  have htri : ‖F s‖ ≤ dist (F s) (dirichletPartialSum a N₀ s)
      + ‖dirichletPartialSum a N₀ s‖ := by
    rw [dist_eq_norm]
    have h := norm_le_norm_add_norm_sub' (F s) (dirichletPartialSum a N₀ s)
    linarith
  linarith

/-- **The abscissa of bounded summation.** -/
noncomputable def abscissaOfBddSum (a : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | DirichletBoundedSumOn a x}

/-- **The easy half of Bohr's comparison.** -/
theorem abscissaOfBddSum_le_abscissaOfUnifConv (a : ℕ → ℂ) :
    abscissaOfBddSum a ≤ abscissaOfUnifConv a := by
  refine sInf_le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.boundedSumOn, rfl⟩

end GaloisForLFunctions.RHTower

end
