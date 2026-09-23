import GaloisForLFunctions.RHTower.Sieve.AmGmIntegral

/-!
# The large sieve with the sharp constant

For a trigonometric polynomial `S(t) = ∑_{n < N} c_n e(nt)` and points `λ_0 < … < λ_R` inside one
period with consecutive gaps at least `δ`,

`∑_{r ≤ R} |S(λ_r)|² ≤ (δ^{-1} + 4πN) ∑_{n < N} |c_n|²`.

The constant has the sharp shape `N + δ^{-1}`: no logarithm.  Gallagher's argument reaches it by
never forming a sum of reciprocal separations — the local bounds at the points are absorbed into a
single integral over the period by disjointness, and the two resulting energies are evaluated by
Parseval.  The obstruction `sum_inv_abs_dist_le` identifies for absolute-value arguments is thereby
bypassed rather than defeated.

The balancing parameter of `AmGmIntegral.lean` is taken to be `2πN`, which equalises the two
contributions of the mixed term.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- Gallagher's bound with both integrals over a full period. -/
theorem gallagher_period (N : ℕ) (c : Fin N → ℂ) {lam : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ 1) :
    ∑ r ∈ Finset.range (R + 1), ‖expSum N c (lam r)‖ ^ (2 : ℕ)
      ≤ (1 / δ) * (∫ t in (0 : ℝ)..1, ‖expSum N c t‖ ^ (2 : ℕ))
        + (∫ t in (0 : ℝ)..1, 2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) := by
  have hcont1 : Continuous (fun t : ℝ => ‖expSum N c t‖ ^ (2 : ℕ)) :=
    ((continuous_expSum N c).norm).pow 2
  have hcont2 : Continuous (fun t : ℝ =>
      2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖) :=
    (continuous_const.mul (continuous_expSum N c).norm).mul
      (continuous_expSum N (derivCoeff N c)).norm
  have hA : (0 : ℝ) ≤ lam 0 - δ / 2 := by linarith
  have hmono : lam 0 ≤ lam R := by
    have h := le_of_gap hgap 0 R (Nat.zero_le R)
    simp only [Nat.cast_zero, sub_zero] at h
    have hR : (0 : ℝ) ≤ (R : ℝ) * δ := by positivity
    linarith
  have hright : (0 : ℝ) ≤ lam R + δ / 2 := by linarith
  have hbase := gallagher_sum N c hδ hgap hA R
  -- enlarge both integrals to the full period
  have hext1 : (∫ t in (0 : ℝ)..(lam R + δ / 2), ‖expSum N c t‖ ^ (2 : ℕ))
      ≤ ∫ t in (0 : ℝ)..1, ‖expSum N c t‖ ^ (2 : ℕ) :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hcont1.intervalIntegrable _ _)
  have hext2 : (∫ t in (0 : ℝ)..(lam R + δ / 2),
        2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖)
      ≤ ∫ t in (0 : ℝ)..1, 2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖ :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Filter.Eventually.of_forall (fun t => by positivity))
      (hcont2.intervalIntegrable _ _)
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have h1 := mul_le_mul_of_nonneg_left hext1 hδinv
  linarith

/-- **The large sieve with the sharp constant.** -/
theorem largeSieve_gallagher (N : ℕ) (hN : 0 < N) (c : Fin N → ℂ) {lam : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ 1) :
    ∑ r ∈ Finset.range (R + 1), ‖expSum N c (lam r)‖ ^ (2 : ℕ)
      ≤ (1 / δ + 4 * Real.pi * (N : ℝ)) * ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set ε : ℝ := 2 * Real.pi * (N : ℝ) with hεdef
  have hε : (0 : ℝ) < ε := by rw [hεdef]; positivity
  set E₀ : ℝ := ∑ n : Fin N, ‖c n‖ ^ (2 : ℕ) with hE₀
  -- the two energies
  have hpar : (∫ t in (0 : ℝ)..1, ‖expSum N c t‖ ^ (2 : ℕ)) = E₀ := integral_normSq_expSum N c
  have hpar' : (∫ t in (0 : ℝ)..1, ‖expSum N (derivCoeff N c) t‖ ^ (2 : ℕ))
      = ∑ n : Fin N, (2 * Real.pi * ((n : ℕ) : ℝ)) ^ (2 : ℕ) * ‖c n‖ ^ (2 : ℕ) :=
    integral_normSq_derivCoeff N c
  have hE₁ : ∑ n : Fin N, (2 * Real.pi * ((n : ℕ) : ℝ)) ^ (2 : ℕ) * ‖c n‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) * E₀ := by
    rw [hE₀, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have hn : ((n : ℕ) : ℝ) ≤ (N : ℝ) := by
      have := n.isLt
      exact_mod_cast le_of_lt this
    have hnn : (0 : ℝ) ≤ 2 * Real.pi * ((n : ℕ) : ℝ) := by positivity
    have hle : 2 * Real.pi * ((n : ℕ) : ℝ) ≤ ε := by
      rw [hεdef]
      nlinarith [hpi, hn]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hle 2) (sq_nonneg _)
  -- Gallagher over a period, with the mixed term split
  have hbase := gallagher_period N c hδ hgap hlow R hhigh
  have hmix := integral_mixed_le N c (A := (0 : ℝ)) (B := (1 : ℝ)) (by norm_num) hε
  rw [hpar, hpar'] at hmix
  have hεinv : (0 : ℝ) < 1 / ε := by positivity
  have hstep : (1 / ε) * (∑ n : Fin N, (2 * Real.pi * ((n : ℕ) : ℝ)) ^ (2 : ℕ) * ‖c n‖ ^ (2 : ℕ))
      ≤ (1 / ε) * (ε ^ (2 : ℕ) * E₀) := mul_le_mul_of_nonneg_left hE₁ (le_of_lt hεinv)
  have hval : (1 / ε) * (ε ^ (2 : ℕ) * E₀) = ε * E₀ := by
    field_simp
  rw [hval] at hstep
  have hfinal : (1 / δ + 4 * Real.pi * (N : ℝ)) * E₀ = (1 / δ) * E₀ + ε * E₀ + ε * E₀ := by
    rw [hεdef]
    ring
  rw [hpar] at hbase
  rw [hfinal]
  linarith

end RHTower.Sieve
