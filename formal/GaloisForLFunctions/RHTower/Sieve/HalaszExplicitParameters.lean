import GaloisForLFunctions.RHTower.Sieve.HalaszGhsMasterBound
import GaloisForLFunctions.RHTower.Sieve.SieveMeanSquareZetaSums
import GaloisForLFunctions.RHTower.Sieve.LogSqZetaCap
/-!
# The master bound with every quantity explicit

The two zeta caps substituted into the split of the Selberg majorant give a closed majorant of the sieve
mean square of a prime weight with `‖a_n‖ ≤ A log n`:

`sieveBound A σ z Y = (4 sinh δ/log Y)·A²·(16/(2σ−2)²)(1 + 2/(2σ−2))
                        + (2/log Y + E + z)·A²·(16/(2σ−1)²)(1 + 2/(2σ−1))`.

Substituting it for both prime weights — `A = 1/log 2` outside, `A = 1` inside — the master bound becomes an
inequality whose right-hand side is an explicit function of the parameters `N, H, σ, z, Y` and nothing else:

`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion errors) + (H+1)(log⌊N+H⌋)⁴/(log 2)³
    + (1/2π)(1 + 1/(σ−1))e^{7/2}·C·√(25π²·sieveBound (1/log 2) σ z Y)·√(25π²·sieveBound 1 σ z Y)`.

Nothing in the statement is an unevaluated sum or an assumed estimate.  Whether the bound beats the trivial
`N log N` is now a question about the parameters alone.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The cap of the linear part of the sieve majorant, at `σ > 1`. -/
def sieveCapLinear (σ : ℝ) : ℝ := (16 / (2 * σ - 2) ^ 2) * (1 + 2 / (2 * σ - 2))

/-- The cap of the constant part of the sieve majorant, at `σ > 1`. -/
def sieveCapConst (σ : ℝ) : ℝ := (16 / (2 * σ - 1) ^ 2) * (1 + 2 / (2 * σ - 1))

/-- The explicit majorant of the sieve mean square of a prime weight with `‖a_n‖ ≤ A log n`. -/
def sieveBound (A σ : ℝ) (z Y : ℕ) : ℝ :=
  (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
      * (A ^ 2 * sieveCapLinear σ)
    + (2 / Real.log Y + selbergFibreError z Y + (z : ℝ)) * (A ^ 2 * sieveCapConst σ)

theorem sieveCapLinear_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ sieveCapLinear σ := by
  have h : 0 < 2 * σ - 2 := by linarith
  rw [sieveCapLinear]
  positivity

theorem sieveCapConst_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ sieveCapConst σ := by
  have h : 0 < 2 * σ - 1 := by linarith
  rw [sieveCapConst]
  positivity

/-- **The sieve mean square of a prime weight, explicitly.**  The two zeta caps substituted into the split
of the Selberg majorant. -/
theorem sieveMeanSquare_le_sieveBound {a : ℕ → ℂ} {A : ℝ}
    (haB : ∀ n : ℕ, ‖a n‖ ≤ A * Real.log n) (M : ℕ) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    sieveMeanSquare a (Finset.Icc 1 M) σ z Y ≤ sieveBound A σ z Y := by
  have hS0 : 0 ≤ 2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))))
      / Real.log Y := by
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    have h := Real.exp_le_exp.2 (show -(1 / (2 * Real.pi)) ≤ 1 / (2 * Real.pi) by linarith)
    exact div_nonneg (by linarith) hlogY.le
  have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hc2 : (0 : ℝ) ≤ 2 / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
    have : (0 : ℝ) ≤ 2 / Real.log Y := by positivity
    have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
    linarith
  refine le_trans (sieveMeanSquare_le_of_norm_le_log haB (Finset.Icc 1 M)
    (fun n hn => (Finset.mem_Icc.1 hn).1) σ z Y hz hlogY) ?_
  rw [sieveBound]
  have h1 := sum_Icc_logSq_rpow_one_sub_two_mul_le hσ M
  have h2 := sum_Icc_logSq_rpow_neg_two_mul_le hσ M
  have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have hstep1 : (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))))
        / Real.log Y)
        * (A ^ 2 * ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
      ≤ (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) / Real.log Y)
        * (A ^ 2 * sieveCapLinear σ) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA2) hS0
    rw [sieveCapLinear]
    exact h1
  have hstep2 : (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
        * (A ^ 2 * ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2)
      ≤ (2 / Real.log Y + selbergFibreError z Y + (z : ℝ)) * (A ^ 2 * sieveCapConst σ) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA2) hc2
    rw [sieveCapConst]
    exact h2
  linarith [hstep1, hstep2]

theorem sieveBound_nonneg {A σ : ℝ} (hσ : 1 < σ) {z Y : ℕ} (hz : 2 ≤ z)
    (hlogY : 0 < Real.log Y) : 0 ≤ sieveBound A σ z Y := by
  have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have hS : Real.exp (-(1 / (2 * Real.pi))) ≤ Real.exp (1 / (2 * Real.pi)) :=
    Real.exp_le_exp.2 (by linarith)
  have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
  have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hlin := sieveCapLinear_nonneg hσ
  have hcst := sieveCapConst_nonneg hσ
  have h1 : (0 : ℝ) ≤ 2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))))
      / Real.log Y := div_nonneg (by linarith) hlogY.le
  have h2 : (0 : ℝ) ≤ 2 / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
    have : (0 : ℝ) ≤ 2 / Real.log Y := by positivity
    linarith
  rw [sieveBound]
  have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have ht1 : (0 : ℝ) ≤ (2 * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi))))
      / Real.log Y) * (A ^ 2 * sieveCapLinear σ) := mul_nonneg h1 (mul_nonneg hA2 hlin)
  have ht2 : (0 : ℝ) ≤ (2 / Real.log Y + selbergFibreError z Y + (z : ℝ))
      * (A ^ 2 * sieveCapConst σ) := mul_nonneg h2 (mul_nonneg hA2 hcst)
  linarith

/-- **The master bound with every quantity explicit.**  For totally multiplicative `f` with `f(1) = 1` and
`‖f‖ ≤ 1`, the partial sum obeys a bound whose right-hand side is an explicit function of the parameters
`N, H, σ, z, Y` alone: the recursion errors, the smoothing error, and the analytic term with both sieve mean
squares replaced by their zeta caps. -/
theorem exists_norm_sum_Icc_mul_log_le_sieveBound {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
          + (1 / (2 * Real.pi))
              * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
                  * (Real.sqrt (25 * Real.pi ^ 2 * sieveBound (1 / Real.log 2) σ z Y)
                      * Real.sqrt (25 * Real.pi ^ 2 * sieveBound 1 σ z Y))) := by
  obtain ⟨C, hC0, hmain⟩ :=
    exists_norm_sum_Icc_mul_log_le hf1 hfmul hbdd N hN hH hσ z Y hY hYz hz hlogY
  refine ⟨C, hC0, hmain.trans ?_⟩
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hout := sieveMeanSquare_le_sieveBound (norm_ghsOuter_le hbdd N) N hσ z Y hz hlogY
  have hin := sieveMeanSquare_le_sieveBound (A := 1)
    (by simpa using norm_ghsInner_le hbdd N) N hσ z Y hz hlogY
  have hsq : Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y)
        * Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y)
      ≤ Real.sqrt (25 * Real.pi ^ 2 * sieveBound (1 / Real.log 2) σ z Y)
        * Real.sqrt (25 * Real.pi ^ 2 * sieveBound 1 σ z Y) := by
    refine mul_le_mul (Real.sqrt_le_sqrt (by nlinarith [hout, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_le_sqrt (by nlinarith [hin, sq_nonneg Real.pi, Real.pi_pos]))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmul0 : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C) := by
    have h1 : 0 < σ - 1 := by linarith
    have : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by positivity
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    exact mul_nonneg hpi.le (mul_nonneg this hC0)
  have hstep := mul_le_mul_of_nonneg_left hsq hmul0
  nlinarith [hstep]

end RHTower.Sieve
end
