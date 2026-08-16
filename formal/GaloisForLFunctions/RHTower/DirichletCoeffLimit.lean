import GaloisForLFunctions.RHTower.DirichletBddHolo

/-!
# The value at `+∞` is the first coefficient

A Dirichlet series converging uniformly on a half-plane tends to its first coefficient along the
real axis:

```text
F(σ) → a₀        as σ → +∞ .
```

Only finitely many terms matter: past any cut the uniform error is small, and the finitely many
remaining terms with index `n ≥ 1` decay like `(n+1)^{−σ}`, while the term `n = 0` is the constant
`a₀` because `1^{−s} = 1`.

This is the engine behind uniqueness of Dirichlet coefficients, and the first of Bohr's coefficient
estimates: a series bounded by `C` on a half-plane has `‖a₀‖ ≤ C`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- A base above one decays to zero along negative exponents. -/
theorem tendsto_rpow_neg_of_one_lt {b : ℝ} (hb : 1 < b) :
    Tendsto (fun σ : ℝ => b ^ (-σ)) atTop (𝓝 0) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hlog : 0 < Real.log b := Real.log_pos hb
  have hrw : ∀ σ : ℝ, b ^ (-σ) = Real.exp (Real.log b * (-σ)) := fun σ =>
    Real.rpow_def_of_pos hb0 (-σ)
  simp only [hrw]
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun σ : ℝ => Real.log b * σ) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hlog tendsto_id
  have h2 : Tendsto (fun σ : ℝ => -(Real.log b * σ)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h1
  simpa [mul_neg] using h2

/-- Every partial sum tends to its first coefficient along the real axis. -/
theorem tendsto_dirichletPartialSum_ofReal_atTop (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun σ : ℝ => dirichletPartialSum a N ((σ : ℝ) : ℂ)) atTop (𝓝 (a 0)) := by
  have hterm : ∀ n ∈ Finset.range N,
      Tendsto (fun σ : ℝ => a n * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-((σ : ℝ) : ℂ))) atTop
        (𝓝 (if n = 0 then a 0 else 0)) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hone : ∀ σ : ℝ, a 0 * (((((0 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-((σ : ℝ) : ℂ)) = a 0 := by
        intro σ
        norm_num
      simp only [hone]
      exact tendsto_const_nhds
    · have hbase : (1 : ℝ) < (n : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hnorm : ∀ σ : ℝ,
          ‖a n * ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-((σ : ℝ) : ℂ))‖ = ‖a n‖ * ((n : ℝ) + 1) ^ (-σ) := by
        intro σ
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        congr 2
      rw [if_neg hn.ne']
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      simp only [hnorm]
      simpa using (tendsto_rpow_neg_of_one_lt hbase).const_mul ‖a n‖
  have hsum := tendsto_finsetSum (Finset.range N) hterm
  have hval : (∑ n ∈ Finset.range N, if n = 0 then a 0 else 0) = a 0 := by
    rw [Finset.sum_ite_eq' (Finset.range N) 0 (fun _ => a 0), if_pos (Finset.mem_range.2 hN)]
  rw [hval] at hsum
  exact hsum

/-- **The value at `+∞` is the first coefficient.** -/
theorem tendsto_dirichletSum_ofReal_atTop {a : ℕ → ℂ} {x : ℝ} {F : ℂ → ℂ}
    (hF : TendstoUniformlyOn (dirichletPartialSum a) F atTop {s : ℂ | x ≤ s.re}) :
    Tendsto (fun σ : ℝ => F ((σ : ℝ) : ℂ)) atTop (𝓝 (a 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop).1
    ((Metric.tendstoUniformlyOn_iff.1 hF) (ε / 2) (by linarith))
  set N : ℕ := max N₀ 1 with hNdef
  have hpart := tendsto_dirichletPartialSum_ofReal_atTop a (N := N) (le_max_right _ _)
  obtain ⟨σ₀, hσ₀⟩ := (Metric.tendsto_atTop.1 hpart) (ε / 2) (by linarith)
  refine ⟨max σ₀ x, fun σ hσ => ?_⟩
  have hσx : x ≤ σ := le_trans (le_max_right σ₀ x) hσ
  have hσσ : σ₀ ≤ σ := le_trans (le_max_left σ₀ x) hσ
  have hmem : ((σ : ℝ) : ℂ) ∈ {s : ℂ | x ≤ s.re} := by
    simpa using hσx
  have h1 : dist (F ((σ : ℝ) : ℂ)) (dirichletPartialSum a N ((σ : ℝ) : ℂ)) < ε / 2 :=
    hN₀ N (le_max_left _ _) _ hmem
  have h2 : dist (dirichletPartialSum a N ((σ : ℝ) : ℂ)) (a 0) < ε / 2 := hσ₀ σ hσσ
  calc dist (F ((σ : ℝ) : ℂ)) (a 0)
      ≤ dist (F ((σ : ℝ) : ℂ)) (dirichletPartialSum a N ((σ : ℝ) : ℂ))
        + dist (dirichletPartialSum a N ((σ : ℝ) : ℂ)) (a 0) := dist_triangle _ _ _
    _ < ε := by linarith

/-- **Bohr's first coefficient estimate.**  A series uniformly convergent on a half-plane where its
sum is bounded by `C` has first coefficient bounded by `C`. -/
theorem norm_coeff_zero_le {a : ℕ → ℂ} {x C : ℝ} {F : ℂ → ℂ}
    (hF : TendstoUniformlyOn (dirichletPartialSum a) F atTop {s : ℂ | x ≤ s.re})
    (hC : ∀ s : ℂ, x ≤ s.re → ‖F s‖ ≤ C) : ‖a 0‖ ≤ C := by
  have hlim := (tendsto_dirichletSum_ofReal_atTop hF).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop x] with σ hσ
  exact hC _ (by simpa using hσ)

end GaloisForLFunctions.RHTower

end
