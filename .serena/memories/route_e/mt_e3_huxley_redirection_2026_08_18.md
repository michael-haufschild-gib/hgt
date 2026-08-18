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

## RED LANE REPAIRED (2026-08-18, 18:30) — supersedes the hazard note above

The `ladderEta` propagation is done.  `Sieve/SpectralParameters` had moved `ladderEta` to
`(log x)^{γβ−β−5/4}` (commit `0794a9200`) without updating consumers, leaving
`Sieve/RhoLimitPieces.eventually_ladderSteps_poly` FALSE.  The forced retune `1 → 5/4` was propagated
across four files: `RhoLimitPieces` (the exponent), `RhoLimit` (`Lm` + six `rhoMajorant` exponents),
`SlopeQuotientLimit` (`eventually_steps_eta_sq_le`, `inv_ladderEta_eq`, `P1/P2/P3`, `slopeMajorant`),
`ConstQuotientLimit` (same three parameters, `discInner`, `constMajorant`).  Two structural side
effects: the product `MB·P1` becomes `(log x)^{−1/4}` instead of `1`, so the corresponding majorant
term gains a vanishing factor and needs `tendsto_rpow_log_of_neg`; and every negativity check in
`tendsto_rhoMajorant`/`tendsto_slopeMajorant` still holds with room because `β, γβ > 9/10`.
`lake build …Sieve.MoebiusMeanSquare` succeeds; the whole Möbius chain is axiom-clean again.

If `ladderEta` moves again, the same six exponent strings are the ones to bump, and the `MB·P1`
term is the only non-mechanical spot.

## The integer-start gate: three dead routes and the live one

Dead: (1) sup-bound Gallagher (`dyadicMeanSquare_le_gallagher`) needs `M₁ ≪ x·ℓ`, i.e. square-root
cancellation for `logPoly μ` at low frequency — RH strength; `CofactorLowFreqBound` saves only
`exp(−c(log x)^{1/10})`.  (2) fibre ⟹ fixed-length integer start: the fibre above `a` *is* an
integer-start window at `⌈x/a⌉` (and `a ↦ ⌈x/a⌉` is surjective onto `[⌈√x/2⌉, ⌈√x⌉]` since
`x/a² ≤ 1` for `a ≥ √x`), but its length varies in `[h/2, h]`, and peeling to a fixed length needs
the maximal window at the peeled start — circular.  (3) multiplicative ⟹ additive window: same
obstruction.

**Live route: make the card's step 1 accept a start-dependent length.**  Landed as
`Sieve/GoodStartVariableWindow` — `card_le_good_add_bad_var`, `card_le_good_add_meanSquare_var`, with
a uniform Markov threshold `δ ≤ (1/8)D·Lf t` (take `δ = (1/16)Dh`).  `card_moebius_sign_ge` was
already pointwise so it transfers verbatim.  What remains is instantiating at the fibre data and
re-running the squarefree input and marker supply at variable lengths — bookkeeping, not analysis.

## Hall-law card: step 1 unconditional at the fibre data (2026-08-18, 18:50)

Landed `Sieve/GoodStartVariableWindow`, `Sieve/GoodStartFibreWindow`, `Sieve/FibreStepOne`
(7 theorems, axiom-clean, wired, lake-build audited).  `eventually_fibre_step_one` has **no
mean-square hypothesis**: the exceptional budget `1024ε√x/D²` comes straight from
`averagedMeanSquare_moebius`, via `δ = (1/32)Dh` and `fibreLen ≥ h/4`.

The one hypothesis left in step 1 is the squarefree mass `h2`.  Discharge plan (all four ingredients
are existing corpus theorems, none length-restricted):
`SquarefreeTruncationDefect.squarefree_count_ge` (any `t, L`; take `D = 6/π²`, `R ≍ √L`)
+ `AveragedSquarefreeTail.sum_tail_divisor_count_le`
+ `FibreStartSeparation.sum_block_comp_start_le` (the `≤ 4` start-sharing aggregation, applied to the
tail at the maximal length `⌈h⌉`, using tail monotonicity in the window and `fibreLen ≤ ⌈h⌉`)
+ Markov to define `Bad₂`.
One module, no analytic input.  Then only the marker supply (already unconditional via Mertens) and
the "most fibres good ⟹ every `X`" passage remain.

## Squarefree-mass discharge: the working constants (2026-08-18, 19:05)

`Sieve/SquarefreeTailTruncate` landed (`card_filter_dvd_sq_eq_zero`, `tail_trunc_eq`,
`squarefree_count_ge_trunc`).  **Why it was needed**: `squarefree_count_ge` forces the divisor range
to `M ≥ t+L ≍ √x`, and `sum_tail_divisor_count_le` then pays `L·M ≍ L√x`, which is the size of the
whole start range — fatal.  Truncating at `M' ≍ x^{1/4}` drops it to `L·x^{1/4}`.

Choices that make the discharge close (worked out, not guessed): `R = 500`, Markov threshold
`θ = 3h/40`, `Lmax = ⌈h⌉+2`, `M' = ⌈√(x+h√x)⌉`.  Then `∑_a tail_a ≤ 4·Lmax((B+Lmax−A)/500 + M')`
and `#Bad₂ ≤ 0.054√x`, a small fraction of `#outerBlock ≍ √x`; and for `a ∉ Bad₂`,
`∑_{fibre} μ² ≥ ϱL − 500 − L/500 − θ ≥ (1/2)ϱL` once `L ≥ h/4` is large.  Do **not** try `R ≍ 27`
(the naive `R + L/R ≤ ϱL/4` choice) — it gives `#Bad₂ ≈ 3.9√x > #outerBlock`.

## Second duplication caught (2026-08-18, 19:20)

`Sieve/SquarefreeExceptional.card_large_le_of_sum_le` already IS the linear Markov inequality
(`#{t ∈ S : θ ≤ f t} ≤ (∑_S f)/θ`, `f ≥ 0`).  A copy written in
`Sieve/FibreSquarefreeIngredients` was a same-namespace collision and was removed.  **Run the
collision scan BEFORE installing, not after** — `lake build` of the new module alone does not see the
clash because it need not import the other file.

Landed instead: `windowTail`, `windowTail_nonneg`, `windowTail_mono`, `fibreLen_le` — the two facts
that let the per-fibre tail be replaced by the tail at the uniform length `⌈h⌉+1` so that
`sum_block_comp_start_le` can aggregate it.

## All four squarefree-discharge steps landed (2026-08-18, 19:40)

`Sieve/FibreTailAverage` (`sum_fibre_windowTail_le`, `sum_shift_windowTail_le`) and
`Sieve/FibreSquarefreeMass` (`fibreTailBudget`, `sum_fibre_windowTail_le_budget`,
`card_fibre_bad_le`, `fibre_squarefree_mass`).  Revised constants: `R = 500`, `θ = h/20`
(`3h/40` is too tight), `M' = ⌈√(x+h√x)⌉`, `M = ⌊x+h√x⌋`.

**The one brick left for hypothesis-free step 1: a numeric lower bound for `squarefreeDensity`.**
The corpus has only `squarefreeDensity_nonneg'` and `squarefreeDensity_le_one`.  Get it from
`SquarefreeCount.abs_sum_Icc_moebius_div_sq_sub_le` at `R = 4` (head `1 − 1/4 − 1/9 = 23/36`, error
`≤ 1/4`, so `ϱ ≥ 7/18`), or from `ϱ ≥ 2 − π²/6` via mathlib's Basel sum.  `ϱ ≥ 1/3` suffices with
`θ = h/40`.

## The density brick was already there (2026-08-18, 20:00)

`Sieve/SquarefreeCount.squarefreeDensity_eq : squarefreeDensity = 6/π²` already existed — so the
numeric bound is just `π ≤ 4`, landed as `Sieve/SquarefreeDensityBound.squarefreeDensity_ge : 3/8 ≤ ϱ`.
The `abs_sum_Icc_moebius_div_sq_sub_le` truncation route recorded earlier is unnecessary.
`squarefreeDensity_pos` was already owned by `Sieve/CoprimeSignDensity` (third duplication caught,
this time before installing).

`Sieve/FibreWindowTop` (`fibre_top_le_floor`, `fibre_top_lt_sq`) supplies the `hbig`/`hsq` side
conditions at `M = ⌊x+h√x⌋`, `M' = ⌈√(x+h√x)⌉`.

**Constants, final:** `R = 5000`, `θ = h/100`.  With only `ϱ ≥ 3/8` available, `(1/2)ϱ ≥ 3/16`, so
`θ = h/20 ≤ L/5` is too big — `h/100` gives `θ ≤ 0.04L` and closes at `L ≥ 33944`, with
`fibreTailBudget/θ ≈ 0.04√x`.

Left for hypothesis-free step 1: `hMM : ⌈√(x+h√x)⌉ ≤ ⌊x+h√x⌋` and `hgap`, then compose
`eventually_fibre_step_one` + `fibre_squarefree_mass` + `card_fibre_bad_le` at `D = squarefreeDensity`.

## CORRECTION: the integer-start Möbius mean square WAS already owned (2026-08-18, 20:20)

`Sieve/MoebiusMeanSquareRealForm.exists_sum_sq_real_moebius_Ico_le` ("the mean square in real form,
unconditionally") and `Sieve/Step1Moebius.exists_card_le_good_add_moebius` ("step 1 with the mean
square supplied ... with no analytic hypothesis") already give the Hall card's step 1 over
consecutive integer starts with fixed `L`.  Both axiom-clean.  **The Hall/growing-marker cards' stated
gap — "needs the integer-start form, blocked on the Ramaré cofactor low-frequency bound" — is stale.**

Consequence: the fibre route I built (variable-length step 1 → fibre windows → fibre mean square) was
unnecessary.  It is valid and stays, but it is not the shortest path, and the composition
`eventually_fibre_step_one` + `fibre_squarefree_mass` was NOT installed because `Step1Moebius`
occupies that slot.

**Lesson: run `scripts/formal_tools.py research` on the *gap the card names*, not only on the
declaration names you are about to write.**  A card's "Lean status" prose can lag the tree by weeks.

**The actual remaining work on the Hall card**: `exists_card_le_good_add_moebius` has no consumers.
Choose `L, Y, K, J, R, Md, ε, W` so its two exceptional terms are `< K/2`, then feed the good-start
count into `Sieve/MarkerBlockLower.card_markerBlockTargets_ge` and
`Sieve/MarkerSignFlip.card_markerBlockTargets_moebius` (with
`MobiusReciprocalMarkerPrimeCapacity.reciprocalMarker_target_sign_flip` and
`Sieve/SumCellMatching.exists_hall_injection_mertens`) to reach `(3)`.  Parameter selection against
`blockCost`, `Bd N`, `contourParam`, `smoothWidth` — not a missing theorem.

## CORRECTION TO THE PREVIOUS CORRECTION (2026-08-18, 20:40)

`Step1Moebius.exists_card_le_good_add_moebius` does NOT supersede the fibre route.  It is
unconditional and has the right *shape*, but its rate is useless: `blockCost`'s second term is
`M₂·2/(π²W)` with `M₂ = (⌊N⌋+1)² ≍ N²` (the trivial bound) and `W ≲ contourParam(N) ≍ exp((log N)^{1/10})`,
so it is `≍ N²exp(−(log N)^{1/10})` against a target `≍ L² = exp(2(log N)^{99/100})`.  That is why it has
no consumers.  **Always check the rate, not only the statement shape.**

**The fibre route is the critical path, and step 1 is now CLOSED**:
`Sieve/FibreStepOneClosed.eventually_fibre_step_one_closed` — no hypotheses, exceptional terms
`1024ε√x/ϱ²` (spectral Möbius fibre mean square) plus `fibreTailBudget x h 5000 ⌈√(x+h√x)⌉/(h/100)`
(squarefree tail).  Largeness `h ≥ 200000` (135776 is too tight by a hair).

**Next**: the marker join.  Markers are the LARGE primes `p > √X` (cofactor `a = n/p < √X`, and `p`
determines `a`, so distinctness is free); starts are `⌈X/p⌉`; `card_markerBlockTargets_ge` needs
`#C p ≥ (3/16)ϱL` for `#P ≍ √X/log X` markers, so the bad-start count must be `< #P/2 ≍ √X/(2 log X)`.
That is a comparison of the two exceptional terms above against `√x/log x`.

## Marker join: geometry done, one rate needed (2026-08-18, 21:00)

`Sieve/MarkerDominatesFibre.fibre_lt_marker` settles `hsmall` for
`MarkerBlockLower.card_markerBlockTargets_ge`: markers must be taken in the UPPER part of the outer
block (`p ≥ (3/2)√x`), else a marker just above `√x` has cofactors up to `√x + h` exceeding it.
With `P = (outerBlock).filter (Prime ∧ (3/2)√x ≤ ·)` and `C p = (innerFibre x h p).filter (μ · = σ')`,
`hprime`/`hpos`/`hsmall` are all discharged and `hc` is the good-fibre conclusion of
`FibreStepOneClosed.eventually_fibre_step_one_closed`.  `#P ≍ √x/log x`, each giving `≍ (3/16)ϱh`
targets, total `≍ ϱH/(6 log x)` = the card's `(3)`.

**The single remaining quantitative step**: the exceptional count must be `< #P/2 ≍ √x/(2 log x)`, but
the first exceptional term is `1024ε√x/ϱ²` with ε FIXED — bigger than `√x/log x` for every fixed ε.
So the join needs `averagedMeanSquare_moebius` **with a rate**: `budget/(h²√x) = o(1/log x)`, i.e.
`≤ (log x)^{-A}`, `A > 1`.  The rate is available in closed form from
`OmegaBudgetExplicit.omegaBudget_le_explicit` and `OmegaBudgetLadderTail.omegaBudget_le_ladder_final`
via `OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget`.  This is a strengthening of an
existing unconditional theorem, not a new estimate.

## The rate exists and is (log x)^{-1.1} (2026-08-18, 21:20)

`tendsto_normalised_omegaBudget` = `136·slope + 140·energy + 131·const + nonSpectral`.  Sizes after the
`ladderEta` retune: `rhoMajorant` binds at `(log x)^{5/4−β−γβ} ≤ (log x)^{-0.55}`; `slopeMajorant` and
`constMajorant` are dominated by `(budgetRhoBound·ladderSteps)² ≈ (log x)^{-1.1}`; every other term is
`exp(−(log x)^{99/100})`, `x^{-1/2}`, or `(log x)^{-2.25}`.  So the normalised budget is
`≍ (log x)^{-1.1}`, which **is** `o(1/log x)` — with only 0.1 of margin.

Three escapes from needing the rate were checked and all fail: shrinking `h` (the `h` cancels in
`V/δ²`), dropping marker primality (loses `card_markerBlockTargets` distinctness, back to the
sign-law card's Cauchy–Schwarz loss), restricting the mean square to primes (nonnegativity gives the
wrong direction).  `ε = 1/log x` is circular because the threshold in `∀ε, ∀ᶠ x` depends on `ε`.

**Remaining work on the Hall card**: give explicit `≤ (log x)^{-A}` forms to
`RhoLimit.tendsto_rhoMajorant`, `SlopeQuotientLimit.tendsto_slope_quotient`,
`ConstQuotientLimit.tendsto_const_quotient`, plus `EnergyQuotient` and `NonSpectralBudget`; then a
rate-carrying `averagedMeanSquare_moebius` lets `eventually_fibre_step_one_closed` run at
`ε = (log x)^{-1.05}`, giving exceptional count `o(√x/log x)` and closing the join.  No new estimate —
only propagation of rates through majorants already proved to vanish.

## Prop 4.2's T₂ case was already owned (2026-08-18, 21:40)

`Sieve/MatomakiTeravainenTypeIIAmplitudeCells` (ten declarations) formalizes the amplitude-cell
cancellation of MT Prop 4.2's `T₂` case abstractly and unconditionally.  Its `hcount` hypothesis
(`#(cells i) ≤ C·T^{2min(σ₁,σ₂)−δ}`) **is** Lemma 4.1's conclusion, i.e. this session's
`exists_lemma41_huxley` with `C = 1`, `δ = ε²/5`.  The two halves only need joining:
instantiate `α := ℝ`, `F_j t := ‖blockPoly M_j c_j 1 t‖`, cells = the dyadic amplitude cells; `hF₁/hF₂`
are definitional; `hcount` is Lemma 4.1 applied to the polynomial realising `min(σ₁,σ₂)` — for
`σ₁ ≤ σ₂` to `M₁^ℓ` (a range polynomial of width `2^ℓ`, hence
`HuxleyRangeLargeValues.huxley_range_large_values_uniform`), for `σ₂ < σ₁` to `M₂` (already dyadic).
Remaining in `T₂`: the case split and the `ℓ`-selection arithmetic.  No new analytic estimate.

Search the corpus with the *paper's lemma numbers and author names* too — `matomakiTeravainen` was a
declaration prefix nobody had told me about.
