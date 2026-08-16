import GaloisForLFunctions.RHTower.DirichletTermMean
import GaloisForLFunctions.RHTower.DirichletCoeffLimit

/-!
# The coefficient formula for a finite Dirichlet sum

For a finite Dirichlet sum the vertical mean against the conjugate kernel extracts a coefficient
exactly, with no interchange of limits:

```text
lim_T (1/2T) ∫_{−T}^{T} S_N(σ+it) (n+1)^{σ+it} dt  =  a_n        (n < N) .
```

The diagonal term is the constant `a_n`, because `b^{−s} b^{s} = 1`; every other term is a
nontrivial character whose vertical mean vanishes.  The sum being finite, the integral and the sum
commute for free.

This is the finite half of Bohr's coefficient estimate; combined with uniform convergence it gives
`‖a_n‖ ≤ C (n+1)^σ` for a series bounded by `C` on `Re s ≥ σ`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The diagonal kernel is trivial. -/
theorem cpow_neg_mul_cpow_self {b : ℝ} (hb : 0 < b) (σ t : ℝ) :
    ((b : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      * ((b : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) = 1 := by
  rw [cpow_neg_mul_cpow_eq hb hb σ t]
  simp

/-- Each conjugate-kernel term is continuous in the vertical variable. -/
theorem continuous_kernel_term (c : ℂ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (σ : ℝ) :
    Continuous fun t : ℝ => c * ((b : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      * ((d : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hrw : (fun t : ℝ => c * ((b : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      * ((d : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => (c * ((Real.exp (σ * (Real.log d - Real.log b)) : ℝ) : ℂ))
        * Complex.exp ((((Real.log d - Real.log b : ℝ)) : ℂ) * Complex.I * (t : ℂ)) := by
    funext t
    rw [mul_assoc, cpow_neg_mul_cpow_eq hb hd σ t]
    ring
  rw [hrw]
  exact continuous_const.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))

/-- **The diagonal term contributes its coefficient.** -/
theorem tendsto_vertical_mean_diagonal (c : ℂ) {b : ℝ} (hb : 0 < b) (σ : ℝ) :
    Tendsto (fun T : ℝ => (1 / (2 * T)) • ∫ t in (-T)..T,
      c * ((b : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
        * ((b : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 c) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hcongr : (∫ t in (-T)..T, c * ((b : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      * ((b : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) = ∫ _t in (-T)..T, c := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_assoc, cpow_neg_mul_cpow_self hb σ t, mul_one]
  rw [hcongr, intervalIntegral.integral_const]
  have hlen : T - -T = 2 * T := by ring
  rw [hlen, smul_smul]
  have : (1 / (2 * T)) * (2 * T) = 1 := by field_simp
  rw [this, one_smul]

/-- **Off-diagonal terms contribute nothing.** -/
theorem tendsto_vertical_mean_term_zero {m n : ℕ} (hmn : m ≠ n) (σ : ℝ) (c : ℂ) :
    Tendsto (fun T : ℝ => (1 / (2 * T)) • ∫ t in (-T)..T,
      c * (((((m : ℝ) + 1 : ℝ)) : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
        * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  refine (tendsto_vertical_mean_term hmn σ c).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **The coefficient formula for a finite Dirichlet sum.** -/
theorem tendsto_vertical_mean_partialSum (a : ℕ → ℂ) {N n : ℕ} (hn : n < N) (σ : ℝ) :
    Tendsto (fun T : ℝ => (1 / (2 * T)) • ∫ t in (-T)..T,
      dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 (a n)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsplit : ∀ T : ℝ, (1 / (2 * T)) • ∫ t in (-T)..T,
      dirichletPartialSum a N ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ∑ m ∈ Finset.range N, (1 / (2 * T)) • ∫ t in (-T)..T,
          a m * (((((m : ℝ) + 1 : ℝ)) : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
            * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro T
    rw [← Finset.smul_sum]
    congr 1
    rw [← intervalIntegral.integral_finsetSum]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      rw [dirichletPartialSum, Finset.sum_mul]
    · intro m _
      have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      exact (continuous_kernel_term (a m) hmpos hnpos σ).intervalIntegrable _ _
  simp only [hsplit]
  have hterm : ∀ m ∈ Finset.range N, Tendsto (fun T : ℝ => (1 / (2 * T)) • ∫ t in (-T)..T,
      a m * (((((m : ℝ) + 1 : ℝ)) : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
        * (((((n : ℝ) + 1 : ℝ)) : ℂ)) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (𝓝 (if m = n then a n else 0)) := by
    intro m _
    rcases eq_or_ne m n with rfl | hmn
    · rw [if_pos rfl]
      exact tendsto_vertical_mean_diagonal (a m) hnpos σ
    · rw [if_neg hmn]
      exact tendsto_vertical_mean_term_zero hmn σ (a m)
  have hsum := tendsto_finsetSum (Finset.range N) hterm
  have hval : (∑ m ∈ Finset.range N, if m = n then a n else 0) = a n := by
    rw [Finset.sum_ite_eq' (Finset.range N) n (fun _ => a n), if_pos (Finset.mem_range.2 hn)]
  rwa [hval] at hsum

end GaloisForLFunctions.RHTower

end
