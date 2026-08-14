# In-flight work: Euler tilt card (2026-08-14/15)

Companion to `nsk-toplevel-stage3-sweep`.

## halasz-reciprocal-coarea-optimality-law — PROMOTED to 3-formalized
Modules `RHTower/ReciprocalCoareaOptimality.lean` (certificate analysis: `coareaRatioCost`,
`coareaStationaryDefect`, derivative/sign lemmas, `exists_unique_coareaStationaryRatio` = (R13),
`coareaRatioCost_min`, `coareaMinCost_eq` = (R10), `log_le_card_mul_log_of_ratio_le` /
`card_ge_log_div_log` = (R8), `coareaPartitionCost` = (R9),
`coareaMinCost_mul_log_le_partitionCost` = (R11), `coareaPartitionCost_geometric_le` = (R12),
`coareaPartitionCost_geometric_optimal_le`) and `RHTower/ReciprocalCoareaEnergy.lean`
(`primeLogWindowMass`, `abs_primeLogWindowMass_sub_le` = (R2)/(R3) from the corpus Mertens layer,
`coareaOuterEnergy_le`, `coareaInnerEnergy_le` = (R5), `sqrt_coareaEnergy_product_le` = (R6),
`sqrt_coareaEnergy_product_geometric_le` = (R7)).  Both wired, axiom-clean.

## route-e-source-faithful-euler-tilt-unit-shell-law — (18)/(19)/(9) DONE, (10)–(14) REMAIN
Compiling, wired, axiom-clean:
- `RHTower/ThetaRelativeErrorMass.lean` — `∫_2^∞|θ(t)/t−1|dt/t < ∞` (`thetaRelMass`),
  `abs_integral_thetaError_mul_rpow_le` (uniform in δ ≥ 0), `exists_abs_thetaError_le`,
  `integrableOn_inv_mul_log_sq`, `exp_neg_le_inv_sq`.
- `RHTower/TiltedPrimeLogSum.lean` — `integral_rpow_sub_one_of_ne` (negative exponent),
  `integral_derivRpow_mul_theta_eq_of_ne`, `tiltedPrimeLogSum`, `tiltedPrimeLogSum_eq`,
  **`abs_tiltedPrimeLogSum_sub_le`**: |∑_{2<p≤Y}p^{-1-δ}log p − (1−Y^{-δ})/δ| ≤ 4log4+8+2·thetaRelMass
  for δ ∈ (0,1], Y ≥ 2.
- `RHTower/EulerTiltMeanEnergy.lean` — `logSquareTailConst` (= ∑ log n/n², via
  `Mertens.summable_log_div_rpow`), `eulerTiltMeanEnergy`, `tiltedPrimeLogSumLE`,
  `abs_eulerTiltMeanEnergy_sub_le` (Euler-denominator correction), `abs_exp_neg_sub_quadratic_le`
  (REUSES the corpus `expNegTruncError_le_pow_div_factorial` at P = 3 — do not re-derive Taylor
  bounds for exp; `SpurCumulantBounds.lean` has the general truncation bound),
  **`abs_eulerTiltMeanEnergy_sub_expansion_le`** = card (18).
- `RHTower/EulerTiltSaddle.lean` — `eulerTiltSaddleDefect`, strict monotonicity in the tilt
  (`eulerTiltMeanEnergy_strictAnti`, `eulerTiltSaddleDefect_strictAnti`,
  `eulerTiltSaddleDefect_injOn`), **`abs_saddle_sub_cofactor_le`** = card (19).
- `RHTower/EulerTiltSaddleAperture.lean` — `cofinalAperture L = 2L e^L`,
  `log_cofinalAperture` (= L + log L + log 2 exactly), continuity of the defect,
  `saddleDefect_le`/`le_saddleDefect`, `exists_unique_saddle_root`,
  `abs_saddle_root_sub_expansion_le`, the three aperture limits, and the capstone
  **`eventually_saddle_root_expansion`** = card (9) (unconditional: eventual in the aperture).
- `RHTower/MertensLogSquareSum.lean` (NEW, reusable) — `primeLogSqSumIoc`,
  `primeLogSqSumIoc_eq` (Abel against `log t/t`), `integral_one_sub_log_div_id`,
  `integral_abs_thetaError_div_le`, **`abs_primeLogSqSumIoc_sub_le`**:
  |∑_{2<p≤Y}(log p)²/p − (log Y)²/2| ≤ mertensLogSqConst·(1+log Y).

### NEXT STEPS for (10)–(14)
1. Weights `w_p = p^{-σ}/(1+p^{-σ})²`.  Since `w_p = p^{-σ}(1+O(p^{-σ}))`, all three sums reduce
   to tilted prime sums plus absolutely convergent corrections (same pattern as
   `abs_eulerTiltMeanEnergy_sub_le`, with `logSquareTailConst` for the log-weighted one and
   `∑ n^{-2}` for the unweighted one; for the (log p)²-weighted one use `∑ (log n)²/n²`, again via
   `Mertens.summable_log_div_rpow` after `log² n ≤ C n^{1/2}`).
2. `A = ∑ w_p = log ℓ + O(1)`: use corpus `Sieve.mertensS` + `abs_mertensS_sub_logLog_sub_const_le`
   (`logLog N = log(log N)`, and `log log Y = log ℓ`), plus the tilt correction
   `∑ p^{-1}(1−p^{-δ}) ≤ δ ∑ log p/p = O(δℓ)`.
3. `B = ∑ w_p log p = ℓ − log ℓ + O(1)`: from `abs_tiltedPrimeLogSum_sub_le` and (9).
4. `C = ∑ w_p (log p)² = ℓ²/2 + O(ℓ log ℓ)`: from `abs_primeLogSqSumIoc_sub_le` and
   `∑ p^{-1}(1−p^{-δ})(log p)² ≤ δ ℓ ∑ (log p)²/p = O(δℓ³)`.
5. Then (12) `t* = πB/C = 2π/ℓ + O(log ℓ/ℓ²)`, `D = π²(A − B²/C) = π² log ℓ + O(1)`, and (13)
   `t*E* = 2π + O(log ℓ/ℓ)` are algebra on 2–4.
6. (14) `|E e^{i(πN − t*E)}| = ℓ^{-2}e^{O(1)}` needs the oscillatory Mertens sum
   `∑_{p≤Y} p^{-σ} cos(t* log p) = log ℓ + O(1)` — the one genuinely new analytic estimate left
   (card (25)–(27); the convergence input is `∫_0^1 (cos 2πu − 1)/u du > −∞`).

## Discipline notes added this session
- Do not run full/umbrella builds; `lake env lean <file>` to check, `lake build <module>` only for
  the oleans a new file imports.
- Do not add hypotheses standing for analytic inputs; structural hypotheses that define an object
  (e.g. "δ solves the tilt equation") are fine when existence is also proved.
- Search the corpus before writing any new estimate (`../scripts/formal_tools.py research "..."`).
