import GaloisForLFunctions.RHTower.Sieve.CesaroLogWeightBound
import GaloisForLFunctions.RHTower.Sieve.AffineMeanSquareL1

/-!
# The Cesàro route with a first-moment analytic input

The arithmetic half of the Cesàro route is independent of how the vertical integral is estimated, so
the assembly holds with the analytic side as a parameter:

`‖∑_{n ≤ N} f(n)log(x/n)‖ ≤ ∑_{n ≤ N} E(σ,T,x/n) + (1/2π)·A`   whenever
`‖∫_{|t| ≤ T} L(f_{≤N},σ+it)x^s/s² dt‖ ≤ A`.

Taking `A` from the pointwise bound gives `A = V·x^σ·π/σ` with `V` the damped size; taking it from the
first moment gives `A = (x^σ/σ²)·√(2T(Q₁ + Q₀T))`, since `‖s‖ ≥ σ` on the line.  For `|f| ≤ 1`
truncated at `N` the second is `≍ x^σ√(log N)` where the first is `≍ x^σ log N`: the analytic term of
the Cesàro chain loses a whole square root of the mass, with no distance hypothesis at all.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The Cesàro assembly with the analytic side as a parameter.** -/
theorem norm_sum_Icc_mul_log_div_le_cesaro_of_integral {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {A σ T x : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hxN : (N : ℝ) ≤ x)
    (hA : ‖∫ t in (-T)..T, LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖ ≤ A) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n)) + (1 / (2 * Real.pi)) * A := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  set c : ℕ → ℂ := truncSeq f N with hc
  have hbridge : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 N, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        = LSeries c ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2) := by
    intro t
    rw [sum_mul_cpow_neg_eq_LSeries hs0 hsupp]
  have harith := norm_sum_Icc_mul_log_div_sub_cesaro_le (c := c) (M := N) (x := x) hx hxN hσ1 hσ2 hT
  have hscale : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖
      ≤ (1 / (2 * Real.pi)) * A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
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
    have h := norm_add_le ((∑ n ∈ Finset.Icc 1 N, c n * ((Real.log (x / n) : ℝ) : ℂ))
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          LSeries c ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries c ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2))
    simpa using h
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

/-- **The vertical Cesàro integral from a first moment.**  On the line `‖s‖ ≥ σ`, so the kernel is
bounded by `x^σ/σ²` and only the first moment of the series is needed. -/
theorem integral_symm_norm_cesaro_le_of_l1 {g : ℕ → ℂ} {sg : Finset ℕ} (hg0 : 0 ∉ sg)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ sg) {σ x J T : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hT : 0 ≤ T)
    (hJ : (∫ t in Set.Icc (-T) T, ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖) ≤ J) :
    (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      ≤ (x ^ σ / σ ^ 2) * J := by
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hTle : -T ≤ T := by linarith
  have hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hg0 hgsupp σ
  have hσle : ∀ t : ℝ, σ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    intro t
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    have h := Complex.abs_re_le_norm ((σ : ℂ) + (t : ℝ) * I)
    rw [hre, abs_of_pos hσ] at h
    exact h
  have hker : ∀ t : ℝ, x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 ≤ x ^ σ / σ ^ 2 := by
    intro t
    refine div_le_div_of_nonneg_left hxσ (by positivity) ?_
    exact pow_le_pow_left₀ hσ.le (hσle t) 2
  have hpt : ∀ t ∈ Set.Icc (-T) T,
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
        ≤ (x ^ σ / σ ^ 2) * ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ := by
    intro t _
    have h := mul_le_mul_of_nonneg_left (hker t) (norm_nonneg (LSeries g ((σ : ℂ) + (t : ℝ) * I)))
    calc ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
        ≤ ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / σ ^ 2) := h
      _ = (x ^ σ / σ ^ 2) * ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ := by ring
  have hKc : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
    have hKeq : (fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
        = fun t : ℝ => x ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
      funext t
      rw [mul_one_div]
    rw [hKeq]
    exact continuous_const.mul (continuous_inv_normSq_line hσ)
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2))
    (fun t _ => norm_cesaro_integrand hx _ σ t)]
  have hstep := intervalIntegral.integral_mono_on hTle
    ((hgc.norm.mul hKc).intervalIntegrable (μ := volume) _ _)
    ((continuous_const.mul hgc.norm).intervalIntegrable (μ := volume) _ _) hpt
  simp only [Pi.mul_apply] at hstep
  rw [intervalIntegral.integral_const_mul] at hstep
  have hIcc : (∫ t in (-T)..T, ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖)
      = ∫ t in Set.Icc (-T) T, ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ := by
    rw [intervalIntegral.integral_of_le hTle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc] at hstep
  have hmul := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ x ^ σ / σ ^ 2)
  linarith [hstep, hmul]

/-- **The Cesàro chain with a first-moment analytic term.**  Unconditional, distance-free: the
analytic side of the log-weighted partial sum is `≍ x^σ√(log N)` where the pointwise route gives
`≍ x^σ log N`. -/
theorem norm_sum_Icc_mul_log_div_le_cesaro_l1 {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {σ T x : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hxN : (N : ℝ) ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
        + (1 / (2 * Real.pi))
          * ((x ^ σ / σ ^ 2)
            * Real.sqrt (2 * T * (5 * Real.pi * Real.exp 1 * (1 + Real.log N)
                + 5 * Real.pi * T))) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hTle : -T ≤ T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  have hl1 := integral_Icc_norm_LSeries_truncSeq_le hbdd N hσ1 hT
  have hker := integral_symm_norm_cesaro_le_of_l1 hs0 hsupp hσ0 hx hT0.le hl1
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)
      * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)) hTle
  exact norm_sum_Icc_mul_log_div_le_cesaro_of_integral hbdd hN hσ1 hσ2 hT hxN
    (le_trans hnorm hker)

end RHTower.Sieve
end
