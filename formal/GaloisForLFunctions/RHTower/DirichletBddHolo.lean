import GaloisForLFunctions.RHTower.DirichletBoundedSum

/-!
# The abscissa of bounded holomorphy

The invariant Bohr's theorem is about: the infimum of the `x` for which the Dirichlet series admits
a bounded holomorphic function on the open half-plane `Re s > x` agreeing with the sum wherever the
series converges.  Unlike the convergent-sum abscissa, this allows the bounded function to be an
analytic continuation, defined where the series need not converge.

Uniform convergence on the closed half-plane gives such a function — the partial sums are entire,
their uniform limit is holomorphic on the open half-plane, and it is bounded by the previous
section — so

```text
σ_b  ≤  σ_u .
```

That is the easy half of Bohr's theorem.  The hard half, `σ_u ≤ σ_b`, is the classical result.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **Every partial sum is entire.**  Each term is `a_n` times a constant to the power `−s` with a
nonzero constant base. -/
theorem differentiable_dirichletPartialSum (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (dirichletPartialSum a N) := by
  have hrw : dirichletPartialSum a N
      = fun s => ∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := rfl
  rw [hrw]
  have hterm : ∀ n : ℕ, Differentiable ℂ
      (fun s : ℂ => a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) := by
    intro n s
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
    exact (DifferentiableAt.const_cpow (differentiable_id.neg s) (Or.inl hne)).const_mul (a n)
  have hsum := Differentiable.sum (u := Finset.range N) fun n _ => hterm n
  have heq : (∑ n ∈ Finset.range N, fun s : ℂ => a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      = fun s : ℂ => ∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
    funext s
    simp [Finset.sum_apply]
  rwa [heq] at hsum

/-- The series has a bounded holomorphic function on `Re s > x` agreeing with its sum. -/
def DirichletBddHoloOn (a : ℕ → ℂ) (x : ℝ) : Prop :=
  ∃ (F : ℂ → ℂ) (C : ℝ), DifferentiableOn ℂ F {s : ℂ | x < s.re} ∧
    (∀ s : ℂ, x < s.re → ‖F s‖ ≤ C) ∧
    (∀ s : ℂ, x < s.re → DirichletConvergesAt a s →
      Tendsto (fun N => dirichletPartialSum a N s) atTop (𝓝 (F s)))

/-- **The abscissa of bounded holomorphy.** -/
noncomputable def abscissaOfBddHolo (a : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | DirichletBddHoloOn a x}

/-- **Uniform convergence on a closed half-plane gives a bounded holomorphic sum on the open
one.** -/
theorem DirichletUniformlyConvergesOn.bddHoloOn {a : ℕ → ℂ} {x : ℝ}
    (h : DirichletUniformlyConvergesOn a x) : DirichletBddHoloOn a x := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop).1
    ((Metric.tendstoUniformlyOn_iff.1 hF) 1 zero_lt_one)
  have hopen : IsOpen {s : ℂ | x < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsub : {s : ℂ | x < s.re} ⊆ {s : ℂ | x ≤ s.re} := fun s hs => le_of_lt (Set.mem_setOf.1 hs)
  have hloc : TendstoLocallyUniformlyOn (dirichletPartialSum a) F atTop {s : ℂ | x < s.re} :=
    (hF.mono hsub).tendstoLocallyUniformlyOn
  refine ⟨F, 1 + ∑ n ∈ Finset.range N₀, ‖a n‖ * ((n : ℝ) + 1) ^ (-x), ?_, ?_, ?_⟩
  · exact hloc.differentiableOn (Filter.Eventually.of_forall fun N =>
      (differentiable_dirichletPartialSum a N).differentiableOn) hopen
  · intro s hs
    have hclose : dist (F s) (dirichletPartialSum a N₀ s) < 1 := hN₀ N₀ le_rfl s (le_of_lt hs)
    have hpart := norm_dirichletPartialSum_le a (x := x) N₀ (le_of_lt hs)
    have htri := norm_le_norm_add_norm_sub' (F s) (dirichletPartialSum a N₀ s)
    rw [dist_eq_norm] at hclose
    linarith
  · exact fun s hs _ => hF.tendsto_at (le_of_lt hs)

/-- **The easy half of Bohr's theorem.** -/
theorem abscissaOfBddHolo_le_abscissaOfUnifConv (a : ℕ → ℂ) :
    abscissaOfBddHolo a ≤ abscissaOfUnifConv a := by
  refine sInf_le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.bddHoloOn, rfl⟩

end GaloisForLFunctions.RHTower

end
