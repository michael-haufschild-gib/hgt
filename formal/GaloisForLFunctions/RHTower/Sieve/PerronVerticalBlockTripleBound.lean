import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound
import GaloisForLFunctions.RHTower.Sieve.BlockAffineMeanSquare

/-!
# The vertical Perron integral of a triple product, at one sieve level per dyadic block

The affine form of the triple-product estimate does not care where its two mean squares come from, so
the block sieve substitutes for the single-level sieve without touching the analysis.  What changes is
only the size of the constants: a global level is capped by the sieve's own error
(`selbergFibreError z Y = Y²e^{4c}(log z)^(4 : ℕ)` must stay under a count that is `O(1)` per prime pair), while
block by block the count is `≍ 2^j` and the level may grow with the block.

`∫_{|t| ≤ t₀2^M} ‖L(A)L(B)L(f)x^s/s‖ ≤ 2·perronVerticalAffineProductBound σ x t₀ V Q_A κ_A Q_B κ_B M
                                          + (Vx^σ/σ)√(Q_A + κ_At₀)√(Q_B + κ_Bt₀)`

with `Q, κ` the block-sieve coefficients `blockAffineConst`, `blockAffineRate`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The triple Perron integral over a symmetric range, at per-block sieve levels.**  The affine law
instantiated at the block-sieve mean squares. -/
theorem integral_symm_norm_perron_triple_block_le {A B f : ℕ → ℂ} {MA MB : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hAprime : ∀ n ∈ Finset.Icc 1 MA, A n ≠ 0 → n.Prime)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hBprime : ∀ n ∈ Finset.Icc 1 MB, B n ≠ 0 → n.Prime)
    {σ x t₀ V : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (ZA YlA ZB YlB : ℕ → ℕ)
    (hYA : ∀ j, 1 ≤ YlA j) (hYzA : ∀ j, YlA j ≤ ZA j) (hzA : ∀ j, 2 ≤ ZA j)
    (hlogA : ∀ j, 0 < Real.log (YlA j))
    (hYB : ∀ j, 1 ≤ YlB j) (hYzB : ∀ j, YlB j ≤ ZB j) (hzB : ∀ j, 2 ≤ ZB j)
    (hlogB : ∀ j, 0 < Real.log (YlB j)) (M : ℕ)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ 2 * perronVerticalAffineProductBound σ x t₀ V (blockAffineConst A MA σ ZA YlA)
              (blockAffineRate A MA σ ZA YlA) (blockAffineConst B MB σ ZB YlB)
              (blockAffineRate B MB σ ZB YlB) M
          + (V * x ^ σ / σ)
              * (Real.sqrt (blockAffineConst A MA σ ZA YlA + blockAffineRate A MA σ ZA YlA * t₀)
                  * Real.sqrt
                    (blockAffineConst B MB σ ZB YlB + blockAffineRate B MB σ ZB YlB * t₀)) := by
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 MA := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 MB := by simp
  exact integral_symm_norm_perron_triple_affine_le hA0 hAsupp hB0 hBsupp hσ hx ht₀ hV
    (blockAffineConst_nonneg A MA σ ZA YlA) (blockAffineRate_nonneg A MA σ ZA YlA)
    (blockAffineConst_nonneg B MB σ ZB YlB) (blockAffineRate_nonneg B MB σ ZB YlB) hFc
    (fun U hU => integral_Icc_normSq_LSeries_le_blockAffine hAsupp hAprime σ ZA YlA hYA hYzA hzA
      hlogA hU)
    (fun U hU => integral_Icc_normSq_LSeries_le_blockAffine hBsupp hBprime σ ZB YlB hYB hYzB hzB
      hlogB hU)
    M hFbound

/-- **The triple Perron integral with the low range charged pointwise, at per-block sieve levels.** -/
theorem integral_symm_norm_perron_triple_l1_low_block_le {A B f : ℕ → ℂ} {MA MB : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hAprime : ∀ n ∈ Finset.Icc 1 MA, A n ≠ 0 → n.Prime)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hBprime : ∀ n ∈ Finset.Icc 1 MB, B n ≠ 0 → n.Prime)
    {σ x t₀ V VA VB : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hVA : 0 ≤ VA) (hVB : 0 ≤ VB)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (ZA YlA ZB YlB : ℕ → ℕ)
    (hYA : ∀ j, 1 ≤ YlA j) (hYzA : ∀ j, YlA j ≤ ZA j) (hzA : ∀ j, 2 ≤ ZA j)
    (hlogA : ∀ j, 0 < Real.log (YlA j))
    (hYB : ∀ j, 1 ≤ YlB j) (hYzB : ∀ j, YlB j ≤ ZB j) (hzB : ∀ j, 2 ≤ ZB j)
    (hlogB : ∀ j, 0 < Real.log (YlB j)) (M : ℕ)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (hAb : ∀ t : ℝ, |t| ≤ t₀ → ‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VA)
    (hBb : ∀ t : ℝ, |t| ≤ t₀ → ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VB) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ 2 * perronVerticalAffineProductBound σ x t₀ V (blockAffineConst A MA σ ZA YlA)
              (blockAffineRate A MA σ ZA YlA) (blockAffineConst B MB σ ZB YlB)
              (blockAffineRate B MB σ ZB YlB) M
          + (2 * t₀) * (VA * VB * (V * x ^ σ / σ)) := by
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 MA := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 MB := by simp
  exact integral_symm_norm_perron_triple_l1_low_affine_le hA0 hAsupp hB0 hBsupp hσ hx ht₀ hV
    hVA hVB
    (blockAffineConst_nonneg A MA σ ZA YlA) (blockAffineRate_nonneg A MA σ ZA YlA)
    (blockAffineConst_nonneg B MB σ ZB YlB) (blockAffineRate_nonneg B MB σ ZB YlB) hFc
    (fun U hU => integral_Icc_normSq_LSeries_le_blockAffine hAsupp hAprime σ ZA YlA hYA hYzA hzA
      hlogA hU)
    (fun U hU => integral_Icc_normSq_LSeries_le_blockAffine hBsupp hBprime σ ZB YlB hYB hYzB hzB
      hlogB hU)
    M hFbound hAb hBb

end RHTower.Sieve
end
