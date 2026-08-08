import GaloisForLFunctions.RHTower.Sieve.CesaroPerronExplicit
import GaloisForLFunctions.RHTower.Sieve.PerronFiniteSum

/-!
# The Cesàro Perron formula for a finite Dirichlet polynomial

When the support lies below the cutoff — the case the single-factor Cesàro route needs, since there the
polynomial is `L(f_{≤N})` and the cutoff is `N` — every term of the Dirichlet polynomial contributes a
Cesàro kernel at `y = x/n ≥ 1`, and there is no vanishing case to treat:

`‖∑_{n ≤ M} c_n log(x/n) − (1/2π)∫_{|t| ≤ T} L(c,σ+it)·x^s/s² dt‖ ≤ ∑_{n ≤ M} ‖c_n‖·E(σ,T,x/n)`,

with `E` the explicit error of the truncated Cesàro Perron formula.  Summed against a uniform coefficient
bound the total is `≍ B(M/σ + x^σ(1 + log M)/(σT))`: no factor `N`, no `1/log(x/n)`, and no near-diagonal
analysis, because the logarithmic average of the sharp-cutoff error is finite where its pointwise value is
not.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The truncated Cesàro Perron integral: the vertical integral of `y^s/s²`. -/
def cesaroVertical (σ T y : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) ^ 2

/-- The explicit error of the truncated Cesàro Perron formula. -/
def cesaroError (σ T y : ℝ) : ℝ :=
  (4 * (1 + Real.log (T / σ)) / Real.pi + 1) / T
    + (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T)))
    + y ^ σ / (Real.pi * T * σ * Real.log 2)
    + 1 / (Real.pi * T)

/-- The Cesàro kernel is continuous on the line. -/
theorem continuous_cesaro_kernel {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ =>
      ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) ^ 2 := by
  have hden : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hnum : Continuous fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hslit : ((y : ℝ) : ℂ) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
      simpa using hy
    exact (continuous_const (y := ((y : ℝ) : ℂ))).continuousAt.cpow hden.continuousAt hslit
  exact hnum.div (hden.pow 2) fun t => pow_ne_zero 2 (line_ne_zero hσ t)

/-- A scalar multiple of the Cesàro kernel is continuous. -/
theorem continuous_cesaroTerm {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 0 < σ) (a : ℂ) :
    Continuous fun t : ℝ =>
      a * (((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) ^ 2) :=
  continuous_const.mul (continuous_cesaro_kernel hy hσ)

/-- The scalar factors out of the truncated Cesàro integral. -/
theorem integral_cesaroTerm_eq {y σ T : ℝ} (a : ℂ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        a * (((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
      = a * cesaroVertical σ T y := by
  rw [intervalIntegral.integral_const_mul, cesaroVertical]
  ring

/-- **The truncated Cesàro Perron formula at one frequency.**  The explicit error, obtained from the
averaged form by adding back the pure second-order pole. -/
theorem norm_cesaroVertical_sub_log_le {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 2 ≤ T)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖cesaroVertical σ T y - ((Real.log y : ℝ) : ℂ)‖ ≤ cesaroError σ T y := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
      volume (-T) T := (continuous_cesaro_kernel hy0 hσ0).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable (fun t : ℝ => 1 / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
      volume (-T) T := (continuous_inv_sq_line hσ0).intervalIntegrable _ _
  have hsplit : (∫ t in (-T)..T,
        (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
      = (∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        - ∫ t in (-T)..T, 1 / ((σ : ℂ) + (t : ℝ) * I) ^ 2 := by
    rw [← intervalIntegral.integral_sub hInt1 hInt2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [sub_div]
  have hid : cesaroVertical σ T y - ((Real.log y : ℝ) : ℂ)
      = (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t in (-T)..T,
            (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) - 1) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
          - ((Real.log y : ℝ) : ℂ))
        + ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T, 1 / ((σ : ℂ) + (t : ℝ) * I) ^ 2 := by
    rw [hsplit, cesaroVertical]
    ring
  have hpole : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)
      * ∫ t in (-T)..T, 1 / ((σ : ℂ) + (t : ℝ) * I) ^ 2‖ ≤ 1 / (Real.pi * T) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    have hstep := norm_integral_inv_sq_line_le hσ0 hT0
    have hval : (1 / (2 * Real.pi)) * (2 / T) = 1 / (Real.pi * T) := by
      field_simp
    calc (1 / (2 * Real.pi)) * ‖∫ t in (-T)..T, 1 / ((σ : ℂ) + (t : ℝ) * I) ^ 2‖
        ≤ (1 / (2 * Real.pi)) * (2 / T) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 1 / (Real.pi * T) := hval
  rw [hid, cesaroError]
  refine le_trans (norm_add_le _ _) ?_
  have hmain := norm_perron_cesaro_sub_log_le_explicit hσ1 hσ2 hT hy
  linarith

/-- **The Cesàro Perron formula for a finite Dirichlet polynomial with support below the cutoff.** -/
theorem norm_sum_Icc_mul_log_div_sub_cesaro_le {c : ℕ → ℂ} {M : ℕ} {x : ℝ} (hx : 0 < x)
    (hxM : (M : ℝ) ≤ x) {σ T : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 2 ≤ T) :
    ‖(∑ n ∈ Finset.Icc 1 M, c n * ((Real.log (x / n) : ℝ) : ℂ))
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            (∑ n ∈ Finset.Icc 1 M, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖
      ≤ ∑ n ∈ Finset.Icc 1 M, ‖c n‖ * cesaroError σ T (x / n) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hnpos : ∀ n ∈ Finset.Icc 1 M, (0 : ℝ) < (n : ℝ) := by
    intro n hn
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hnle : ∀ n ∈ Finset.Icc 1 M, (n : ℝ) ≤ x := by
    intro n hn
    have h2 : n ≤ M := (Finset.mem_Icc.1 hn).2
    have : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
    linarith
  have hpt : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 M, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        = ∑ n ∈ Finset.Icc 1 M, c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
            / ((σ : ℂ) + (t : ℝ) * I) ^ 2) := by
    intro t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ofReal_div_cpow_eq_mul_cpow_neg hx (hnpos n hn)]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun t =>
      ∑ n ∈ Finset.Icc 1 M, c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
        / ((σ : ℂ) + (t : ℝ) * I) ^ 2)) (fun t _ => hpt t)]
  rw [intervalIntegral.integral_finsetSum (fun n hn =>
    (continuous_cesaroTerm (div_pos hx (hnpos n hn)) hσ0 (c n)).intervalIntegrable _ _)]
  rw [Finset.mul_sum]
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
            / ((σ : ℂ) + (t : ℝ) * I) ^ 2)
        = c n * cesaroVertical σ T (x / n) := fun n _ => integral_cesaroTerm_eq (c n)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < (n : ℝ) := hnpos n hn
  have hy1 : 1 ≤ x / n := (one_le_div hn0).2 (hnle n hn)
  have hstep : ‖c n * ((Real.log (x / n) : ℝ) : ℂ) - c n * cesaroVertical σ T (x / n)‖
      = ‖c n‖ * ‖cesaroVertical σ T (x / n) - ((Real.log (x / n) : ℝ) : ℂ)‖ := by
    rw [show c n * ((Real.log (x / n) : ℝ) : ℂ) - c n * cesaroVertical σ T (x / n)
        = -(c n * (cesaroVertical σ T (x / n) - ((Real.log (x / n) : ℝ) : ℂ))) by ring,
      norm_neg, norm_mul]
  rw [hstep]
  exact mul_le_mul_of_nonneg_left (norm_cesaroVertical_sub_log_le hσ1 hσ2 hT hy1) (norm_nonneg _)

end RHTower.Sieve
end
