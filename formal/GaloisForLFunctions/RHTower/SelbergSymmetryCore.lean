import GaloisForLFunctions.RHTower.PsiDefectSqrtBound
import GaloisForLFunctions.RHTower.SelbergWeightSqrtSumBound
import Mathlib.NumberTheory.Chebyshev

/-!
# The Tatuzawa–Iseki core bound for the `ψ` defect

Instantiating the Tatuzawa–Iseki identity at `F₀ = ψ − id + 2γ` and
dominating the Möbius-weighted left side termwise —
`|μ(n)| ≤ 1`, `|∑_{d} F₀(⌊k/d⌋)| ≤ 24√k`, and the weight bound
`∑_n (log N − log n)√⌊N/n⌋ ≤ 16N` — gives

`|F₀(N)·log N + ∑_{k ≤ N} Λ(k)·F₀(⌊N/k⌋)| ≤ 384·N`,

the core estimate from which Selberg's symmetry formula follows by
unfolding `F₀`.  Also records that the ℕ-indexed `chebyshevPsi` is
mathlib's `Chebyshev.psi` at integer arguments.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `chebyshevPsi` is mathlib's `Chebyshev.psi` at integer arguments. -/
theorem chebyshevPsi_eq_psi (k : ℕ) : chebyshevPsi k = Chebyshev.psi k := by
  unfold chebyshevPsi Chebyshev.psi
  rw [Nat.floor_natCast]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  rw [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **Tatuzawa–Iseki core bound**:
`|F₀(N)log N + ∑_{k≤N} Λ(k)F₀(⌊N/k⌋)| ≤ 384N` for `F₀ = ψ − id + 2γ`. -/
theorem abs_psiDefect_selberg_core (N : ℕ) (hN : 1 ≤ N) :
    |psiDefect N * Real.log N
        + ∑ k ∈ Finset.Icc 1 N, vonMangoldt k * psiDefect (N / k)|
      ≤ 384 * N := by
  rw [← tatuzawa_iseki psiDefect N hN]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      |((moebius n : ℤ) : ℝ) * (Real.log N - Real.log n)
          * floorSummatory psiDefect (N / n)|
        ≤ 24 * ((Real.log N - Real.log n)
            * Real.sqrt ((N / n : ℕ) : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hNn1 : 1 ≤ N / n :=
      (Nat.le_div_iff_mul_le (by omega : 0 < n)).2 (by omega)
    have hw : 0 ≤ Real.log N - Real.log n := by
      have := Real.log_le_log hn0 (show (n : ℝ) ≤ N by exact_mod_cast hn.2)
      linarith
    have hμ : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hS := abs_floorSummatory_psiDefect_le (N / n) hNn1
    calc |((moebius n : ℤ) : ℝ) * (Real.log N - Real.log n)
          * floorSummatory psiDefect (N / n)|
        = |((moebius n : ℤ) : ℝ)| * (Real.log N - Real.log n)
          * |floorSummatory psiDefect (N / n)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hw]
      _ ≤ 1 * (Real.log N - Real.log n)
          * (24 * Real.sqrt ((N / n : ℕ) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hμ hw) hS (abs_nonneg _)
            (by rw [one_mul]; exact hw)
      _ = 24 * ((Real.log N - Real.log n)
          * Real.sqrt ((N / n : ℕ) : ℝ)) := by ring
  calc |∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ)
        * (Real.log N - Real.log n) * floorSummatory psiDefect (N / n)|
      ≤ ∑ n ∈ Finset.Icc 1 N, |((moebius n : ℤ) : ℝ)
        * (Real.log N - Real.log n) * floorSummatory psiDefect (N / n)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          24 * ((Real.log N - Real.log n) * Real.sqrt ((N / n : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 24 * ∑ n ∈ Finset.Icc 1 N,
          (Real.log N - Real.log n) * Real.sqrt ((N / n : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ 24 * (16 * N) :=
        mul_le_mul_of_nonneg_left (sum_log_weight_sqrt_floor_le N hN)
          (by norm_num)
    _ = 384 * N := by ring

end RHTower
