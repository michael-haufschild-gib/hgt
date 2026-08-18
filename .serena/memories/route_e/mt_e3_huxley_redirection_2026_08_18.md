# MT all-interval E3 — Huxley redirection (2026-08-18)

## The finding

**Jutila's large-values estimate and Bourgain's zero-density estimate are both removable from the
Matomäki–Teräväinen all-interval E3 programme.  Huxley's large-values theorem alone suffices.**

Verified against the source (arXiv:2207.05038, local text at scratchpad `mt.txt`):

- Lemma 4.1's content is Jutila at `k = 7`:
  `|T| ≪ (NT)^{ε²/500}(GN/V² + (GN/V²)^{-1/k}·G³NT/V⁶ + (GN/V²)^{4k}·T/N^{2k})`,
  which at `G = N^{-1+o(1)}, V = N^{-σ}` is `N^{2σ} + T N^{(6-2/k)σ-2} + T N^{(8σ-2)k}` — matches the
  paper's display exactly.
- The middle term's **base `G³NT/V⁶` is Huxley's second term** (Kerr, arXiv:1909.12075, Lemma 15:
  `|A| ≪ N^{2+o(1)}/V² + T N^{4+o(1)}/V⁶` for `|a_n| ≤ 1`, `V ≥ N^{3/4+o(1)}`).
- Setting the Huxley base against `T^{2σ}` with `N ≥ T^{1-θ}` gives `σ ≤ (2θ-1)/(6θ-4)`; at the
  Harman value `θ = 2/11` that is **`σ ≤ 7/32 = 0.21875`**.  Remark 5.2 needs only `σ > 1/5 + 2ε`.
- Cost: `a > max(32/29, 88/79) = 88/79 ≈ 1.11392`, `c ≈ 2.114`, all-interval exponent
  `1 + a/2 ≈ 1.557` instead of `1.55`.  Both Route E cards retune `1.55 → 1.557`.
- **The §6.1 (Heath-Brown identity + Bourgain) detour is abandoned.**  It was adopted only to escape
  Jutila; and it does not even escape Watt/Deshouillers–Iwaniec, since its Type I sums are "handled
  as before" (§5.1).

## Landed Lean (all axiom-clean, all wired into `GaloisForLFunctions.RHTower`)

- `Sieve/HuxleySubdivision` — `card_le_of_window_bound` (combinatorial window subdivision, fibres of
  `r ↦ ⌊(λ_r−λ_0)/W⌋` are index intervals of spread `< W`), `huxley_global_large_values`.
- `Sieve/HuxleyClosedLargeValues` — `norm_dyadicDirRow`, `sq_le_of_large_value`,
  `huxley_large_values_closed` (Huxley's Lemma 15 with explicit constants; window `W = (V²/1284G)²`,
  resonance `U = 4πN/3`).
- `Sieve/HuxleyFinsetLargeValues` — `sepEnum` + `huxley_large_values_finset` (`S : Finset ℝ`).
- `Sieve/HuxleyDirichletLargeValues` — `blockCoeff`, `blockPoly`,
  `inner_dyadicDirRow_blockCoeff`, `norm_blockCoeff_sq`, `norm_blockCoeff_one_sq_le` (`≤ D²/N`),
  `huxley_block_large_values`.
- `Sieve/HuxleyExplicitLargeValues` — `card_le_of_separated` (`|S| ≤ Ttot/δ + 1`),
  `huxley_block_large_values_explicit`.

Mechanism of the subdivision: the corpus's `huxley_local_large_values` absorbs the second-derivative
envelope `B ≤ 214√W + 1536 N/√U` when `G·B ≤ V²/2`; taking `U = 4πN/3` makes the `U`-endpoint
absorbable exactly when `G√N ≲ V²` (= Huxley's `V ≥ N^{3/4}`), and the `√W` endpoint for
`W ≍ V⁴/G²`; the number of windows `Ttot/W` then produces `Ttot G³N/V⁶`.

## What remains

1. Lemma 4.1 = exponent arithmetic only (threshold `2256 D² ≤ N^{1/2−2σ}`; second term via
   `N ≤ T^{1−ε}`; first term via `N ≥ T^{9/11}` and `1 + (9/11)(6σ−2) − 2σ = (32/11)(σ − 7/32)`).
2. **The only remaining automorphic input is Lemma 3.5 (Watt / Deshouillers–Iwaniec)**, used in
   §5.1/§5.2 Type I.  Proven on paper this session: the plain MVT fails there by a full power of the
   amplifier (`MVT: (T/M₂² + M)M^{1/a−1}` vs `DI: (T/M₂²)M^{1/a−1}`), so the naive route is dead.
   Two live escapes: (i) restrict the Type I range (for `T ≤ M₂` the pointwise bound `≪ 1/|t|`
   suffices) and pay a larger `θ` — affordable because the Route E cards accept any fixed exponent;
   (ii) Heath-Brown's sparse mean value estimate (Lemma 3.4), which is hard but not automorphic.
3. Prop 2.2 (Harman's sieve decomposition) is untouched.

## Do not rebuild

`Sieve/JutilaLargeValues`, `Sieve/CriticalTruncationZeta`, `Sieve/GramEntryZetaBound`,
`Sieve/AbelIncreasingWeight`, `Sieve/GallagherSumGeneral`, `Sieve/PowerFibreDivisorBound`,
`Sieve/DivisorBound` all remain valid unconditional assets but are **off the critical path** now.
