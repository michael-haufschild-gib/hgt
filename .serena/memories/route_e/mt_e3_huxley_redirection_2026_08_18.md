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

## M4c CLOSED (same session)

Lemma 4.1 is now Lean-proved unconditionally, at `σ = 7/32 − 5ε` (Remark 5.2 needs only `σ > 1/5`).

- `Sieve/HuxleyDensityBound` — `huxley_threshold_of_rpow` (Huxley's `V ≥ N^{3/4}` becomes
  `2400 D² ≤ N^{1/2−2σ}`; only `π > 3` is used), `huxley_block_two_term`
  (`|S| ≤ (6594624·T·D⁶·N^{6σ−2} + 2D²N^{2σ})(1 + 12π(1+log(2T+1)))` — Huxley's two terms with
  explicit constants).
- `Sieve/HuxleyDensityHypothesis` — `lemma41_huxley`: `|S| ≤ T^{2σ−ε²/5}` for
  `T^{9/11} ≤ N ≤ T^{1−ε}`, `5ε ≤ σ ≤ 7/32 − 5ε`, given three largeness hypotheses.
- `Sieve/HuxleyDensityThreshold` — `exists_lemma41_largeness` (explicit `T₀ = max 1 (C^{1/z})`,
  `z = ε²/2`, `C = 6594624 + D⁶ + 1 + 12π + 12π·3^z/z`, using `Real.log_le_rpow_div`),
  `exists_lemma41_huxley` (the largeness hypotheses discharged).

Lean traps met: `set X := …` leaves a let-binding whose defeq blows up `linarith`/`nlinarith` —
`clear_value` after the `set` fixes it; `nlinarith` on rpow atoms times out, replace by
`mul_le_mul_of_nonneg_right` + `linarith`; `gcongr` discharges the whole multiplicative chain of a
five-factor product bound by itself.

Next Lean target: **M4d = Proposition 4.2** (Type II estimate) — the `T₁/T₂/T₃` partition, the
discrete mean value theorem for `M_j^{ℓ_j}`, Halász–Montgomery on `T₁`, Lemma 4.1 on `T₂`.

## Deduplication caught

`Sieve/SeparatedCount.card_le_of_separated` already existed in `RHTower.Sieve` (cell-index
injection, more general). The first version written here collided and would have broken the
umbrella; renamed to `card_le_of_pairwise_spread` and reproved as a wrapper. **Always run a
`grep -rn "theorem <name>\b" --include='*.lean'` collision scan over every new declaration name
before building the umbrella** — module-level `lake build` does not catch same-namespace clashes.

## Card-level status of the five Route E targets (2026-08-18)

Read the cards' own "Lean progress" sections before doing anything in this lane.

1. `route-e-forbidden-support-e3-stability` — the card states explicitly: "Every step this card
   *proves* is now in Lean."  Its only unformalized content is the **quoted** MT Theorem 1.2
   (`(FS4)`), plus `(FS7)`, which was closed earlier this session.  So the whole remaining debt is
   the MT programme.
2. `route-e-cofactor-amplified-e3-token-supply` — same: "What remains on this card: only `(6)`, the
   quantitative all-interval E₃ supply".  `(7)`, `(9)` closed earlier this session.
3. `route-e-coprime-square-root-mobius-product-sign-law` — its `(3)` and consequence are
   **already unconditional Lean** (`Sieve/RouteEMoebiusUnconditional.route_e_sign_density_unconditional`,
   `route_e_signClass_nonempty_unconditional`).  It stays Stage 2 only for the
   representation/multiplicity programme, whose gate is an **explicitly open question**: is
   `(#S)²/(X·balancedMomentConst y)` larger than the Brun–Titchmarsh count of the window?  Worked
   out here: with `#S ≍ h√x`, `X ≍ x`, `balancedMomentConst ≍ log x`, the bound is `≍ h²/log x`
   against `≍ h√x/log x`, so it needs `h ≳ √x` — the global Cauchy–Schwarz loses a factor `√x/h`.
   Closing it requires the second moment of the balanced divisor function **localised to the
   window**, i.e. an additive-divisor estimate.  Do not expect the existing global bound to work.
4. `route-e-reciprocal-marker-mobius-hall-law` and
5. `route-e-growing-reciprocal-marker-low-breadth-transport` — both need the **integer-start**
   Möbius mean square `DyadicTranslates.dyadicMeanSquare`, while the corpus proves the **fibre**
   normalisation `AveragedMeanSquare`.  **Do not try to close this through
   `dyadicMeanSquare_le_gallagher`**: that route needs a *sup* bound `M₁` on
   `‖logPoly μ (Icc 1 M) w‖²` for `|w| ≤ W`, and the arithmetic requirement works out to
   `M₁ ≪ x·ℓ`, i.e. square-root cancellation for the Möbius polynomial at low frequency — RH
   strength.  `CofactorLowFreqBound` only saves `exp(−c(log x)^{1/10})`, nowhere near.  The correct
   route is the L²-in-frequency Gallagher that `FibreWindowBridge` already runs, re-normalised.
   The qualitative half — both sign classes occupy the window — is now Lean
   (`Sieve/MoebiusSignInWindow`, this session).

## Concurrent-session hazard (2026-08-18, 17:50)

`Sieve/SpectralParameters.lean` has **uncommitted** changes (`ladderEta` exponent moved to
`γβ − β − 5/4`), which makes the committed `Sieve/RhoLimitPieces.eventually_ladderSteps_poly`
(asserting `2β + 1 − γβ`; the true value is now `2β + 5/4 − γβ`) **false and red**.  Everything
downstream — `Sieve/MoebiusMeanSquare`, `Sieve/RouteEMoebiusUnconditional`, and any new module
importing them — cannot be built, and `lake build` has already deleted the stale oleans.  Do not
repair it: the statement must be retuned together with its three consumers
(`Sieve/SlopeQuotientLimit`, `Sieve/RhoLimit`, `Sieve/ConstQuotientLimit`), and that is the other
session's refactor.  The Huxley/`Sieve/Huxley*` lane is unaffected and builds clean.
