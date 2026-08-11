import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal

/-!
# Quantitative Perron truncation for one dyadic Heath--Brown box

Combining the exact support geometry, the `n^ε log n` coefficient theorem, and the sharp
near-diagonal Perron kernel gives a uniform truncation theorem for every signed box.  For a box
whose lower edge reaches the cutoff, its full Dirichlet polynomial has support at most
`2^(2j)` times that cutoff; no artificial `X^j` length remains.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set

/-- A positive-degree box surviving through `N` has full support through `2^(2j) N`. -/
theorem upperSupported_heathBrownDyadicTermBox_of_lower_le
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q N : ℕ)
    (hdegree : 1 ≤ k - m)
    (hlower : heathBrownDyadicCoreLower (k - m) a b q ≤ N) :
    UpperSupported (heathBrownDyadicTermBox L X k m a b q)
      (2 ^ (2 * (k - m)) * N) := by
  intro n hn
  have hmem := upperSupported_heathBrownDyadicTermBox L X k m a b q n hn
  have hupper := heathBrownDyadicCoreUpper_le_of_lower_le hdegree a b q hlower
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmem).1,
    (Finset.mem_Icc.mp hmem).2.trans hupper⟩

/-- **Near-diagonal Perron error for every fixed signed dyadic box.**  Constant is independent of
factor cutoffs and dyadic indices. -/
theorem exists_heathBrownDyadicTermBox_perron_error_le
    {ε : ℝ} (hε : 0 < ε) (k m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L X : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
        (q N : ℕ) (σ T : ℝ), 1 ≤ σ → 0 < T →
      let M := heathBrownDyadicCoreUpper (k - m) a b q
      let c := complexCoeff (heathBrownDyadicTermBox L X k m a b q)
      ‖(∑ n ∈ Finset.Icc 1 (min M N), c n)
          - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
              (∑ n ∈ Finset.Icc 1 M,
                  c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                    / ((σ : ℂ) + (t : ℝ) * I))‖
        ≤ ((k.choose m : ℝ) * C * (M : ℝ) ^ ε * Real.log (M : ℝ))
            * ((N : ℝ) + 1 / 2) ^ σ
            * (5 * (1 + Real.log M) + 4 * (1 + Real.log N)) /
              (Real.pi * T) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_norm_complexCoeff_heathBrownDyadicTermBox_le_prefix_rpow_mul_log hε k m
  refine ⟨C, hC, ?_⟩
  intro L X a b q N σ T hσ hT
  dsimp only
  let M := heathBrownDyadicCoreUpper (k - m) a b q
  let F := heathBrownDyadicTermBox L X k m a b q
  have hM : 1 ≤ M := by
    dsimp [M, heathBrownDyadicCoreUpper]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsupp : UpperSupported F M := by
    simpa [F, M] using upperSupported_heathBrownDyadicTermBox L X k m a b q
  have hB0 : 0 ≤ (k.choose m : ℝ) * C * (M : ℝ) ^ ε * Real.log (M : ℝ) := by
    have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    positivity
  have hbound : ∀ n, ‖complexCoeff F n‖ ≤
      (k.choose m : ℝ) * C * (M : ℝ) ^ ε * Real.log (M : ℝ) := by
    intro n
    by_cases hn : F n = 0
    · rw [complexCoeff_apply, hn, Complex.ofReal_zero, norm_zero]
      exact hB0
    · have hnmem := hsupp n hn
      simpa [F] using hcoeff L X a b q M n
        (Finset.mem_Icc.mp hnmem).1 (Finset.mem_Icc.mp hnmem).2
  simpa [F, M] using
    (norm_sum_Icc_sub_perron_integral_near_le
      (c := complexCoeff F) (M := M) (N := N) hbound hσ hT)

end RHTower.Sieve
