import GaloisForLFunctions.RHTower.Sieve.CesaroFiniteSum
import GaloisForLFunctions.RHTower.Sieve.CesaroKernelVertical
import GaloisForLFunctions.RHTower.Sieve.GhsPerronSum

/-!
# The logarithmically weighted partial sum, through the Cesàro kernel

Both halves of the Cesàro route meet here.  The arithmetic half is the truncated Cesàro Perron formula
for a Dirichlet polynomial whose support lies below the cutoff; the analytic half is the vertical bound

`∫_{|t| ≤ T} ‖L(g,σ+it)x^s/s²‖ ≤ V·x^σ·π/σ`,

which needs only a pointwise bound `V` on the series.  Together, for a bounded `f` truncated at `N`:

`‖∑_{n ≤ N} f(n)·log(x/n)‖ ≤ ∑_{n ≤ N} E(σ,T,x/n) + (1/2π)·V·x^σ·π/σ`   for every `x ≥ N`.

Nothing here is a mean square, a dyadic split, or a sieve: the second-order decay of the kernel is
absolutely integrable, and the truncation error of the second-order kernel carries no factor `N`.  With
`V = dampedSize σ δ z N ≍ (log N)e^{−δ²}` and `σ = 1 + A/log N` the analytic term is `≍ N(log N)e^{−δ²}`,
which at `δ² ≍ log log N` is `≍ N` — the strength of Halász's theorem for the logarithmic average.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The logarithmically weighted partial sum against the Cesàro kernel.**  The arithmetic half is the
truncated Cesàro Perron formula, the analytic half the integrable second-order decay. -/
theorem norm_sum_Icc_mul_log_div_le_cesaro {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {V σ T x : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hV : 0 ≤ V)
    (hxN : (N : ℝ) ≤ x)
    (hgV : ∀ t : ℝ, |t| ≤ T → ‖LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
        + (1 / (2 * Real.pi)) * (V * x ^ σ * (Real.pi / σ)) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  set c : ℕ → ℂ := truncSeq f N with hc
  -- the Dirichlet polynomial is the series
  have hbridge : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 N, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        = LSeries c ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2) := by
    intro t
    rw [sum_mul_cpow_neg_eq_LSeries hs0 hsupp]
  -- the arithmetic half
  have harith := norm_sum_Icc_mul_log_div_sub_cesaro_le (c := c) (M := N) (x := x) hx hxN hσ1 hσ2 hT
  -- the analytic half
  have hTle : -T ≤ T := by linarith
  have hnormint : ‖∫ t in (-T)..T, LSeries c ((σ : ℂ) + (t : ℝ) * I)
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖
      ≤ ∫ t in (-T)..T, ‖LSeries c ((σ : ℂ) + (t : ℝ) * I)
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTle
  have hanalytic := integral_symm_norm_cesaro_le (g := c) (sg := Finset.Icc 1 N) hs0 hsupp
    hσ0 hx hV hT0.le hgV
  have hscale : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖
      ≤ (1 / (2 * Real.pi)) * (V * x ^ σ * (Real.pi / σ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left (le_trans hnormint hanalytic) (by positivity)
  -- assemble
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => LSeries c ((σ : ℂ) + (t : ℝ) * I)
      * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2))
    (fun t _ => hbridge t)] at harith
  have htri : ‖∑ n ∈ Finset.Icc 1 N, c n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, c n * ((Real.log (x / n) : ℝ) : ℂ))
            - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
              LSeries c ((σ : ℂ) + (t : ℝ) * I)
                * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖
          + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
              LSeries c ((σ : ℂ) + (t : ℝ) * I)
                * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 N, c n * ((Real.log (x / n) : ℝ) : ℂ))
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          LSeries c ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2))
    simpa using this
  have hcoeff : (∑ n ∈ Finset.Icc 1 N, ‖c n‖ * cesaroError σ T (x / n))
      ≤ ∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      linarith
    have hEnn : (0 : ℝ) ≤ cesaroError σ T (x / n) := by
      rw [cesaroError]
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hyσ : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
      have h1T : (1 : ℝ) < 1 + 1 / T := by
        have : (0 : ℝ) < 1 / T := by positivity
        linarith
      have hinvT1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; linarith
      have hmon : Real.log (Real.log (1 + 1 / T)) ≤ Real.log (Real.log 2) :=
        Real.log_le_log (Real.log_pos h1T) (Real.log_le_log (by linarith) (by linarith))
      have hP2 : (0 : ℝ) ≤ (4 / (Real.pi * T))
          * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T))) :=
        mul_nonneg (by positivity) (by linarith)
      have hTσ0 : (0 : ℝ) ≤ T / σ := by positivity
      have hlogT : (0 : ℝ) ≤ Real.log (1 + T / σ) := Real.log_nonneg (by linarith)
      have hP1 : (0 : ℝ) ≤ (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T := by positivity
      have hP3 : (0 : ℝ) ≤ (x / n) ^ σ / (Real.pi * T * σ * Real.log 2) := by positivity
      have hP4 : (0 : ℝ) ≤ 1 / (Real.pi * T) := by positivity
      linarith
    calc ‖c n‖ * cesaroError σ T (x / n)
        ≤ 1 * cesaroError σ T (x / n) :=
          mul_le_mul_of_nonneg_right (norm_truncSeq_le hbdd N n) hEnn
      _ = cesaroError σ T (x / n) := one_mul _
  linarith [htri, harith, hscale, hcoeff]

end RHTower.Sieve
end
