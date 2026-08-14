# In-flight work: Halász coarea card + Euler tilt card (2026-08-14)

Companion to `nsk-toplevel-stage3-sweep`.

## halasz-reciprocal-coarea-optimality-law — analysis half DONE
`formal/GaloisForLFunctions/RHTower/ReciprocalCoareaOptimality.lean` compiles clean and is wired
into `RHTower.lean`:
- `coareaRatioCost r = √(r(r-1))/log r`, `coareaStationaryDefect r = log r - 2(r-1)/(2r-1)`;
- `hasDerivAt_coareaStationaryDefect` (derivative `(4r²-6r+1)/(r(2r-1)²)`), sign lemmas at the
  inner critical ratio `(3+√5)/4`, `strictAntiOn`/`strictMonoOn`, `tendsto_..._atTop`,
  **`exists_unique_coareaStationaryRatio`** (= card eq (R13));
- `hasDerivAt_coareaRatioCost` (`= (2r-1)·defect/(2√(r(r-1))(log r)²)`),
  **`coareaRatioCost_min`** (global minimality at the stationary ratio) and
  **`coareaMinCost_eq`** (the sInf is attained) (= (R10));
- `coareaMinCost_mul_log_le` (per-shell bound), **`coareaMinCost_mul_log_le_sum`** (= (R11)),
  `log_le_card_mul_log_of_ratio_le` / `card_ge_log_div_log` (= (R8)).

REMAINING for that card:
1. (R9) atom-corrected cost `C(P) = Σ √(r_j(r_j-1+1/u_j))` and the trivial extension of (R11) to
   it (termwise `Real.sqrt_le_sqrt`).
2. (R12) geometric partition upper bound `C(P) ≤ c(r)·log(U/u₀) + √(r/u₀)/(1-√(1/r))`
   (needs `√(a+b) ≤ √a+√b`, `Real.sqrt_pow`, `geom_sum_eq`).
3. (R5)–(R7) energy bounds. Plan: use `RHTower.mertensPrimeWeightSum` +
   `abs_mertensPrimeWeightSum_floor_sub_log_le` (in
   `RHTower/MertensPrimeWindowWeakConvergence.lean`, error `mertensPrimeWindowBound + 1`) to get
   an UNCONDITIONAL (R2)/(R3):
   `primeLogWindowMass A B := mertensPrimeWeightSum ⌊B⌋₊ - mertensPrimeWeightSum ⌊A⌋₊`, with
   `|primeLogWindowMass − (log B − log A)| ≤ 2(mertensPrimeWindowBound+1)` for `2 ≤ A ≤ B`.
   The cofactor shell `P[u,v] = {p : x e^{-v} ≤ p < x e^{-u}}` has `log B − log A = v − u`.
   Then `E_out ≤ (window mass)/u²` termwise (on the shell `log(x/p) ≥ u`), `E_in = L²·(mass up to
   e^v)`, and `√(E_out E_in) ≤ L√((v−u+C)(v+C))/u`, which at `v = ru` is `≤ L√(r(r−1)) + o(1)`.

## route-e-source-faithful-euler-tilt-unit-shell-law — step 1 done, step 2 written
- DONE, compiles: `RHTower/ThetaRelativeErrorMass.lean` (see the sweep ledger).
- WRITTEN BUT NOT YET COMPILED: `RHTower/TiltedPrimeLogSum.lean` —
  `integral_rpow_sub_one_of_ne` (negative-exponent power integral),
  `integral_derivRpow_mul_theta_eq_of_ne`, `tiltedPrimeLogSum δ Y = primeRpowLogSumIoc (-δ) Y`,
  `tiltedPrimeLogSum_eq` (Abel form) and
  `abs_tiltedPrimeLogSum_sub_le : |Σ_{2<p≤Y} p^{-1-δ}log p − (1−Y^{-δ})/δ| ≤ 4log4+8+2·thetaRelMass`
  for `0 < δ ≤ 1`, `2 ≤ Y`.  It is deliberately NOT wired into `RHTower.lean` until it compiles.
  Blocked only on `lake build GaloisForLFunctions.RHTower.ThetaRelativeErrorMass` finishing —
  the build lock is heavily contended by other concurrent sessions (each build takes >30 min of
  waiting).  Re-run that build, then `lake env lean` the tilted-sum file.
- Then continue with the ledger's steps 3–6 (Taylor of `(1−e^{-δℓ})/δ`, denominator correction,
  saddle solve for `σ_x`, weights A/B/C, `t*`, `D`, and the `(14)` amplitude).
