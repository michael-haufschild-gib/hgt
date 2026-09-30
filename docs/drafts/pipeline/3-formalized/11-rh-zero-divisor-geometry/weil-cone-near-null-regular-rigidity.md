# Near-null regular rigidity: no regular witness of radical evaporation (partial answer to Q_ann)

- **ID:** MC-WEIL-NEAR-NULL-REGULAR
- **Stage:** 3-formalized (MC loop cycle 166)
- **Type:** THEOREM (Lean, unconditional)
- **Source.**
  - HF's sharp open problem Q_ann (`1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L164): "Is there a nonzero bounded `u` on `ℕ≥2` with `Ξ(t)²·Σu(n)cos(t log n) ≥ 0`?"
  - If the answer is NO, the full Weil cone is unique among `|lam − Λ| ≤ A√n`.
  - If the answer is YES, the witness is exactly "radical-level evaporation".
- **Statement.**
  - **Setting.** Let `u : ℕ → ℝ` be bounded with `u(0) = u(1) = 0`, and put `w = u√n`. Suppose the Dirichlet series of `w` continues to `E`, holomorphic on a neighbourhood of `½ ≤ Re s ≤ 7/4`, with:
    - `‖E(s)‖ ≤ C(1+|Im s|)`;
    - `E(½ − it) = conj E(½ + it)`;
    - `E = Σ w(n)n^{−s}` on `Re s = 7/4`.
  - **Conclusion.** If the null potential `ψ_u(y) = Σ u(n)(K(y+log n) + K(y−log n))` is positive definite up to sign (`±ψ_u` PD, equivalently `Ξ²·Σu cos` a measure of one sign), then `u = 0`.

## Meaning
- **A u-only hypothesis.** The theorem uses no Weil positivity of `Λ + w`. It is the "radical (E-PD) half" condition of HF's annihilation duality.
- **Shape of a YES witness.** A witness to Q_ann = YES must have a Dirichlet series that is singular on the critical line. In spectral terms, `Σu cos` must carry singular mass on the real zeros of `Ξ`, where the `Ξ²` weight cannot see it.
- **What is excluded.** Periodic, `ζP`, L-function-combination and every analytically continuable `u`.
- **Comparison with the corpus.**
  - `vonMangoldt_add_eq_zero_of_symbol` (MUST-507 lineage) excludes symbol-type `w` under `WeilPositive(Λ + w)`, which is positivity on pole-free tests and involves `Λ`'s zeros.
  - Near-null positivity is a different, `u`-only hypothesis: near-null tests `𝓕(Ξ²g)` have pole values `¼ĝ(±i/2) ≠ 0`. Neither theorem implies the other.
  - The corpus had no conclusion `u = 0` from positive-definiteness of the null potential alone.

## Paper proof
1. **Bochner.** `±ψ_u` is continuous and positive definite, so `−ψ_u = charFun σ` with `σ ≥ 0` finite. Continuity follows from boundedness of `u` and `K(y) ≤ C e^{−2|y|}`.
2. **Line representation.** Take `G = XiC(2π·)²`, which decays on `|Im| ≤ c₀ = 5/(8π)` by `xi_strip_decay` together with evenness and compactness. The representation lemma then gives `ψ_u(t) = ∫e^{2πiξt}Ξ(ξ)²·2Re E(½+2πiξ)dξ`.
3. **Sign.** Split the density `f = f⁺ − f⁻`. Then `σ + f⁻dx = f⁺dx` as finite measures (`Measure.ext_of_charFun`), so `f⁻ = 0`. The zeros of `Ξ` are isolated, hence `Re E ≤ 0` on the line.
4. **Annihilation.** Take `k = autoCorr(narrowG 0)`, supported in `[−½,½]`.
   - `k(±log n) = 0` for `n ≥ 2`, so by the line representation `∫|ĝ(−2πξ)|²·Re E(½+2πiξ)dξ = 0`.
   - The integrand is `≤ 0` and continuous, so it vanishes identically. Since `ĝ` is entire and nonzero, `Re E ≡ 0`.
5. **Vanishing.** Take `k = autoCorr(narrowG m)` at `y = log m`. The window vector isolates `n = m`, giving `u(m)·ρ(0) = 0`.
6. **Other sign.** Apply the result to `−w`.

## Lean
- **`RHTower/WeilNearNullRegularRigidity.lean`** (namespace `RHTower.WeilRegular`).
  - Capstones: `eq_zero_of_positiveDefinite_neg_nullPotential` and `eq_zero_of_positiveDefinite_nullPotential`.
  - Supporting lemmas:
    - `exists_norm_XiC_wide_le` (Ξ decay on `|Im| ≤ 5/4`);
    - `exists_norm_xiSq_le`;
    - `riemannAutocorr_eq_integral`;
    - `nullPotential`, `continuous_nullPotential`, `nullPotential_eq_integral`;
    - `lineDensity_nonpos`, `re_E_nonpos`, `re_E_eq_zero`;
    - `RegularDeviation.neg`.
- **Shared tools.** From `WeilDeviationLineRepresentation`: `tsum_deviation_mul_pair_eq`, with the shift widened to `2πc₀ = 5/4`, so absolute convergence holds on `Re s = 7/4` and bounded `u` is covered. From `WeilRegularDeviationRigidity`: `pairTransform`, `weilTest_eq_integral`.
- **Audit.** Wired into `RHTower.lean`. `#print axioms` shows only `propext, Classical.choice, Quot.sound`. The ilean sweep found no collisions, and lint is clean.

## Novelty audit
- **Verdict: SURVIVES.** It is a partial answer to a named corpus open problem, obtained with a new mechanism for the `u`-only near-null hypothesis: charFun uniqueness plus spectral-gap annihilation.
- **Corpus check.**
  - I grepped STATUS, the frontier map, and the P2 cards (`weil-cone-singular-deficit-law`, finite-type uniqueness) for `symbol`, `partial sum`, `regular perturbation`, `Q_ann`, `PositiveDefiniteOnReal`.
  - The only `PositiveDefiniteOnReal` uses in the Weil-cone lane are the near-null/translation-bound modules. Those derive PD from `WeilPositiveFull` and conclude via mean balance under CauchyBounded hypotheses, a different class.
- **Literature.** There is no literature notion of the Weil cone of completions.
- **Significance.** Moderate. The theorem narrows Q_ann to singular `u`. That is exactly the regime HF's heuristics address: natural candidates fail at `|t| < 14`, and the annihilator-norm growth problem remains.

## Log
- 2026-09-30 — created and formalized (MC cycle 166). The theorem was originally proved in cycle 165 as the sign route under `WeilPositiveFull`, then removed. It was recognized as answering Q_ann under the weaker `u`-only hypothesis and rebuilt in that form.
