import GaloisForLFunctions.RHTower.Sieve.CesaroDyadicMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LiouvilleChain

/-!
# The Liouville Cesàro bound without the zero-free region

`exists_norm_sum_Icc_liouvilleC_mul_log_div_le_cesaro` routes the analytic side of the Cesàro chain
through `dampedSize σ δ z L`, whose damping factor `e^{-δ²}` is supplied by the zero-free strip.  That
input is inert here.  Writing `A = (σ − 1)log L` and `δ² = c·logLog L`, the two parts of `dampedSize` are

`(1 + 1/(σ−1))e^{7/2 + 2(σ−1)(log z + log 4) − δ²} ≍ (log L/A)·(log L)^{−c}e^{2A}`,
`L^{1−σ}/(σ − 1) ≍ (log L/A)·e^{−A}`,

and the second does not see `δ` at all.  Balancing them at `A ≍ (c/3)logLog L` gives
`≍ (log L)^{1 − c/3}/logLog L`, which even at the largest possible `c = 1` is `≍ (log L)^{2/3}`.

The unconditional dyadic mean-square bound gives `≍ x^σ√(log L)` for the same analytic term
(`norm_sum_Icc_mul_log_div_le_cesaro_dyadic`), and `(log L)^{1/2} < (log L)^{2/3}`.  So the zero-free
region contributes nothing to this chain: the Liouville instance below is both unconditional and
stronger.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The Liouville logarithmically weighted partial sum, unconditionally.**  No distance, no zero-free
strip, no sieve level: the analytic side is the height-free dyadic mean-square bound. -/
theorem norm_sum_Icc_liouvilleC_mul_log_div_le_cesaro_dyadic {N : ℕ} (hN : 1 ≤ N) {σ T x : ℝ}
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hxN : (N : ℝ) ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq liouvilleC N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
        + (1 / (2 * Real.pi))
          * (8 * x ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N))
            + 12 * x ^ σ * Real.sqrt (5 * Real.pi)) :=
  norm_sum_Icc_mul_log_div_le_cesaro_dyadic norm_liouvilleC_le hN hσ1 hσ2 hT hxN

end RHTower.Sieve
end
