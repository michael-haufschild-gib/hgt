# The quarter law of residue flips

- **ID:** quarter-law-residue-flips
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Trans-Horizon Incidence Mechanics (§5 "the parity pair": the `1/4` law)
- **Statement:** For every `q ≥ 1` and every `S ⊆ ZMod q`, the half-damped weight of the residue-class
  flip `f_{q,S}(d) d^{-1/2}` is paid iff `φ(q) < 4 #(S ∩ (ZMod q)ˣ)`.

## Why it matters

The `1/4` law of the flipped density becomes an exact theorem on the whole residue family. The
symmetric case (`the-quarter-law-of-symmetric-residue-flips.md`) had real character exponents. In
general the exponents `s_χ` are complex, and the arguments of the `L(·, χ)` enter. The new tool is the
Euler-logarithm bound `|log L(σ + it, χ)| ≤ 9 log log|t| + C` right of `Re s = 1`, together with its
boundedness on boxes. With it, `|L|^{s}` is at most a power of `log|t|` for every complex `s`.

## Paper proof

1. **Euler logarithm** (`RHTower/DirichletLEulerLogarithmRightOfTheOneLine`). `ℓ_χ(w) = Σ_p −log(1 − χ(p)p^{-w})`
   is holomorphic on `Re w > 1` with `e^{ℓ_χ} = L` and `ℓ_χ' = L'/L`. Along `[σ, 2] + it`:
   `|ℓ_χ(σ + it)| ≤ (3/2)Σ_p p^{-2} + ∫_σ^2 |L'/L(x + it)| dx`. For `|t| ≥ 9`, `|L'/L| ≤ log⁹|t|/(2a)` on
   the strip `x ≤ 1 + a/log⁹|t|` and `|L'/L(x + it)| ≤ Σ Λ(n) n^{-x} ≤ 1/(x − 1) + B` beyond, so
   `|ℓ_χ| ≤ 1/2 + log(log⁹|t|/a) + B + O(1)`. For `χ ≠ 1` and `|t| ≤ 9`, `L'/L` is continuous on the
   closed box, so `|ℓ_χ|` is bounded.
2. **Prime sums.** `|Σ_p χ(p)p^{-w} − ℓ_χ(w)| ≤ Σ_p p^{-2}`.
3. **Euler bound.** With the decomposition of `the-quarter-law-of-symmetric-residue-flips` and
   `−Re(s_χ P_χ) ≤ |s_χ|(|ℓ_χ| + S)`:
   `|F| ≤ e^B |ζ|^{1−2ρ} exp((2/φ) Σ_{χ≠1} |s_χ| |ℓ_χ|)`. The exponential is bounded on the box and
   `≤ C log^{⌈9c₀⌉}|t|` beyond, `c₀ = (2/φ) Σ |s_χ|`.
4. **Payment.** The generic strip bounds and the line-energy criterion of the symmetric case
   (`exists_norm_residueFlip_bounds_of`, `receiverBounded_residueFlip_half_of_bounds`) apply when
   `ρ > 1/4`. Necessity for `ρ ≤ 1/4` is `not_receiverBounded_residueFlip_half_of_le`.

## Lean

- `RHTower/DirichletLEulerLogarithmRightOfTheOneLine.lean`: `eulerLog`, `exp_eulerLog`,
  `hasDerivAt_eulerLog`, `norm_logDeriv_LFunction_le`, `exists_norm_logDeriv_zeta_le`,
  `norm_eulerLog_le_integral`, `exists_norm_eulerLog_le_large`, `exists_norm_eulerLog_le_box`.
- `TransHorizonIncidenceMechanics/TheQuarterLawOfResidueFlips.lean`: `norm_tsum_char_sub_eulerLog_le`,
  `exists_log_norm_residueFlip_le_general`, `exists_norm_residueFlip_le_exp`,
  `exists_exp_eulerLog_sum_le`, `receiverBounded_residueFlip_half_iff_general` (axioms `propext`,
  `Classical.choice`, `Quot.sound`).

## Gates
- [x] 0 → 1  in-progress (corpus: no bound on `log L` or `arg L` right of the one-line)
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized

## Log
- 2026-10-23 — created, formalized, wired into the THIM and RHTower umbrellas.
