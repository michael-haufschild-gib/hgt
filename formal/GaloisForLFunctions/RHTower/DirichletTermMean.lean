import GaloisForLFunctions.RHTower.VerticalMeanCharacter

/-!
# A Dirichlet term against a conjugate kernel is a character

The product that appears when extracting the `n`-th coefficient of a Dirichlet series,

```text
b^{−s} · c^{s} ,        s = σ + it ,
```

separates into a constant depending on `σ` and the character `e^{iθt}` with
`θ = log c − log b`.  The frequency vanishes exactly when `b = c`, so distinct indices give
nontrivial characters, whose vertical means vanish.

Together with `tendsto_vertical_mean_cexp` this is what kills the off-diagonal terms in the
coefficient formula

```text
a_n = lim_T (1/2T) ∫_{−T}^{T} F(σ+it) (n+1)^{σ+it} dt .
```
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **The conjugate kernel separates into a real factor and a character.** -/
theorem cpow_neg_mul_cpow_eq {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (σ t : ℝ) :
    ((b : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
        * ((c : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.exp (σ * (Real.log c - Real.log b)) : ℝ) : ℂ)
        * Complex.exp ((((Real.log c - Real.log b : ℝ)) : ℂ) * Complex.I * (t : ℂ)) := by
  have hbne : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hb)
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hc)
  rw [Complex.cpow_def_of_ne_zero hbne, Complex.cpow_def_of_ne_zero hcne,
    ← Complex.exp_add, ← Complex.ofReal_log hb.le, ← Complex.ofReal_log hc.le]
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Distinct indices give a nonzero frequency. -/
theorem log_sub_log_ne_zero {m n : ℕ} (hmn : m ≠ n) :
    Real.log ((n : ℝ) + 1) - Real.log ((m : ℝ) + 1) ≠ 0 := by
  intro h
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have heq : Real.log ((n : ℝ) + 1) = Real.log ((m : ℝ) + 1) := by linarith
  have := Real.log_injOn_pos (Set.mem_Ioi.2 hn) (Set.mem_Ioi.2 hm) heq
  have hcast : (n : ℝ) = (m : ℝ) := by linarith
  exact hmn (by exact_mod_cast hcast.symm)

/-- **The vertical mean of an off-diagonal Dirichlet term vanishes.** -/
theorem tendsto_vertical_mean_term {m n : ℕ} (hmn : m ≠ n) (σ : ℝ) (c : ℂ) :
    Tendsto (fun T : ℝ => (1 / (2 * T)) *
      ‖∫ t in (-T)..T, c * (((((m : ℝ) + 1 : ℝ)) : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
        * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop (𝓝 0) := by
  set θ : ℝ := Real.log ((n : ℝ) + 1) - Real.log ((m : ℝ) + 1) with hθdef
  have hθ : θ ≠ 0 := log_sub_log_ne_zero hmn
  set K : ℂ := c * ((Real.exp (σ * θ) : ℝ) : ℂ) with hKdef
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hint : ∀ T : ℝ,
      (∫ t in (-T)..T, c * (((((m : ℝ) + 1 : ℝ)) : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
        * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = K * ∫ t in (-T)..T, Complex.exp (((θ : ℂ) * Complex.I) * (t : ℂ)) := by
    intro T
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_assoc, cpow_neg_mul_cpow_eq hm hn σ t, hKdef, ← hθdef]
    ring
  simp only [hint, norm_mul]
  have hmaj := tendsto_vertical_mean_cexp hθ
  have hscaled := hmaj.const_mul ‖K‖
  have hzero : ‖K‖ * (0 : ℝ) = 0 := by ring
  rw [hzero] at hscaled
  refine hscaled.congr fun T => ?_
  ring

end GaloisForLFunctions.RHTower

end
