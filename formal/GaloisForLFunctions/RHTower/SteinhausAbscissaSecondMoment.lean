import GaloisForLFunctions.RHTower.SteinhausModel

/-!
# The second moment of the Steinhaus Dirichlet polynomial diverges up to the half line

The model second-moment identity `E‖Σ aₙ Xₙ‖² = Σ aₙ²` applied to the coefficients `aₙ = n^(−σ)`
gives, for the truncated Steinhaus Dirichlet series,

```text
E ‖ Σ_{n ≤ N} n^(−σ) X_n ‖²  =  Σ_{n ≤ N} n^(−2σ) ,
```

and for `σ ≤ 1/2` the right side dominates the harmonic sum, hence diverges.  This is the
quantitative content of "the abscissa of convergence of the random Dirichlet series is at least
`1/2` almost surely": the `L²` norms of the partial sums are unbounded, so the partial sums cannot
converge in `L²` anywhere strictly left of the half line.
-/

noncomputable section

open MeasureTheory Filter

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- The truncated Steinhaus Dirichlet series. -/
def steinhausDirichletPoly (σ : ℝ) (N : ℕ) (ω : Omega) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * X n ω

/-- **The second moment of the truncated Steinhaus Dirichlet series.** -/
theorem integral_normSq_steinhausDirichletPoly (σ : ℝ) (N : ℕ) :
    ∫ ω, ‖steinhausDirichletPoly σ N ω‖ ^ 2 ∂steinhausMeasure
      = ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(2 * σ))) := by
  have hs : ∀ n ∈ Finset.Icc 1 N, n ≠ 0 := by
    intro n hn
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    omega
  have h := integral_normSq_dpoly (fun n => ((n : ℝ) ^ (-σ))) (Finset.Icc 1 N) hs
  have hpoly : ∀ ω : Omega, steinhausDirichletPoly σ N ω
      = ∑ n ∈ Finset.Icc 1 N, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * X n ω := fun _ => rfl
  simp only [hpoly]
  rw [h]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < (n : ℝ) := by
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  rw [sq, ← Real.rpow_add hn0]
  congr 1
  ring

/-- The harmonic comparison: past the half line the coefficients dominate `1/n`. -/
theorem one_div_le_rpow_neg_two_mul {σ : ℝ} (hσ : σ ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ (n : ℝ) ^ (-(2 * σ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hle : (-1 : ℝ) ≤ -(2 * σ) := by linarith
  have hmono : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-(2 * σ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hle
  have hval : (n : ℝ) ^ (-1 : ℝ) = 1 / (n : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  rwa [hval] at hmono

/-- **The second moment diverges up to the half line.** -/
theorem tendsto_sum_rpow_neg_two_mul_atTop {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ (-(2 * σ)))) atTop atTop := by
  have hharm : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) atTop atTop := by
    simpa using Real.tendsto_sum_range_one_div_nat_succ_atTop
  refine tendsto_atTop_mono (fun N => ?_) hharm
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hlen : N + 1 - 1 = N := by omega
  rw [hlen]
  refine Finset.sum_le_sum fun i _ => ?_
  have hcast : ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have h := one_div_le_rpow_neg_two_mul hσ (n := 1 + i) (by omega)
  rw [hcast] at h
  rw [hcast]
  exact h

/-- **The truncated Steinhaus Dirichlet series has unbounded `L²` norm up to the half line.** -/
theorem tendsto_integral_normSq_steinhausDirichletPoly_atTop {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    Tendsto (fun N : ℕ => ∫ ω, ‖steinhausDirichletPoly σ N ω‖ ^ 2 ∂steinhausMeasure)
      atTop atTop := by
  refine (tendsto_sum_rpow_neg_two_mul_atTop hσ).congr fun N => ?_
  exact (integral_normSq_steinhausDirichletPoly σ N).symm

end GaloisForLFunctions.RHTower

end
