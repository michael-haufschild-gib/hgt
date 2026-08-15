# In-flight work: real-twist / zeta-deficit card (2026-08-15)

Companion to `nsk-toplevel-stage3-sweep`.

## CLOSED this session
- `halasz-reciprocal-coarea-optimality-law` → 3-formalized
  (`RHTower/ReciprocalCoareaOptimality.lean`, `RHTower/ReciprocalCoareaEnergy.lean`).
- `route-e-source-faithful-euler-tilt-unit-shell-law` → 3-formalized.  Final pieces:
  `RHTower/EulerTiltCharacteristic.lean` ((24) `eulerTiltCharacteristic_eq`, (25)
  `abs_two_log_norm_add_euler_le`, `primeRpowSum`, `abs_primeRpowSum_sub_logLog_le`),
  `RHTower/EulerTiltAmplitude.lean` (`quadraticHead_le`, `harmonicTail_le`,
  `abs_primeCosineDefect_le_const`, `exists_bound_primeCosineDefect`, **(14)**
  `exists_bound_log_norm_eulerTiltCharacteristic`), `RHTower/TerminalPrimeBand.lean` ((23)
  `terminalBandMass_le`, `tendsto_terminalBandMass`), `RHTower/RouteESaddleLowTilt.lean` ((20) for
  every σ ∈ (0,1)).

## IN PROGRESS: real-twist-zeta-deficit-transfer-law
Done (compiling, wired into RHTower.lean, axiom-clean):
- `RHTower/PretentiousDistance.lean` — `unitDiskDist`, `sqrt_unitDiskDist_triangle`,
  `sqrt_sum_le_of_sqrt_le` (Minkowski over a Finset), `pretentiousDistSq`,
  `sqrt_pretentiousDistSq_triangle`, `primeChar`, `pretentiousDistSq_primeChar`,
  `pretentiousDistSq_real_reflect` (Z9), `pretentiousDistSq_primeChar_le_four_mul` (**Z10**).
- `RHTower/ZetaEulerLogPrimeSum.lean` — `zetaLinePoint`, `log_norm_riemannZeta_eq_re_eulerLog`
  (via corpus `exp_canonicalEulerLogZeta_eq_riemannZeta`), `primeCosTsum`,
  `norm_log_one_sub_sub_self_le`, `abs_re_neg_log_one_sub_sub_re_le`,
  **`abs_re_eulerLog_sub_primeCosTsum_le`** (≤ invSquareTailConst).
- `RHTower/ZetaOneLineDeficit.lean` — `primeRpowCoeff`/`primeRpowLogCoeff`/`primeCosCoeff`,
  `tsum_primeRpowLogCoeff_le` (≤ 1/δ + C₀), `tsum_tail_primeRpowCoeff_le`,
  `abs_sum_primeCos_shift_le`, `primeClockEnergy`, `zetaDeficitConst`,
  **`abs_zeta_deficit_sub_primeClockEnergy_le` = (Z2a)**.
- `RHTower/RealTwistDeficitTransfer.lean` — `zetaLineDeficit`,
  `zetaLineDeficit_sub_le_primeClockEnergy`, `pretentiousDistSq_primeChar_eq_primeClockEnergy`,
  **`quarter_zetaLineDeficit_le_pretentiousDistSq` = (Z3)/(Z8)+(Z10)**.
- `RHTower/Sieve/DirichletPrefixLittlewood.lean` — the ENTIRE Littlewood chain re-derived with a
  free right endpoint `M ≤ 2^(topExponent t + 1)`: `dirichlet_tail_dyadic_prefix`,
  `norm_dirichlet_partial_two_regime_prefix`, `..._shape_prefix`, `..._endpoints_prefix`,
  `..._const_prefix`, `..._pow_two_prefix`, `..._exponent_prefix`, `..._assembled_prefix`,
  `..._canonical_prefix`, `..._capstone_prefix`, `..._explicit_prefix`, `..._balanced_prefix`,
  `littlewood_threshold_prefix`, `..._order_prefix`, **`..._rate_prefix`**.
  (Key: the corpus block bound `dirichlet_block_saving_of_small_factorial` already accepts a
  partial block `N ≤ M ≤ 2N+1`, so only the assembly needed redoing.)
- `RHTower/Sieve/ZetaShiftedLineRate.lean` — `cpow_shift_split`,
  `norm_dirichlet_shifted_prefix_le` (Abel via corpus `abel_block_bound`, weight `n^{-δ}`),
  **`norm_riemannZeta_shifted_line_rate`**: for `16π ≤ t`, the two order conditions, and
  `δ ∈ [0,1]`, `‖ζ(1+δ+it)‖ ≤ 33 + 2L/(orderLowerBound L − 4/3)`, `L = log(t/2π)`.  This is (Z2c)
  in raw form.

### NEXT STEPS
1. (Z2d): turn the shifted rate into `∃ C T, ∀ x ≥ T, ∀ 1 ≤ |τ| ≤ x^B,
   log log log x − C ≤ zetaLineDeficit τ x`.  Plan: conjugation for τ < 0 (`riemannZeta_conj`);
   an absolute bound on the compact range `1 ≤ |τ| ≤ T₀` from `norm_riemannZeta_le_partialSum`
   with a FIXED N; for `|τ| ≥ T₀` split on `L ≤ √ℓ` vs `L > √ℓ` (ℓ = log x) to avoid needing
   monotonicity of `u/(a log u + b)`; then `Δ ≥ log ℓ − log(C ℓ/log ℓ) = log log ℓ − log C`.
2. Then the card's power-law corollary and the polynomial-horizon antiscale frame.
3. The GHS cellwise transfer (Z11)–(Z13) needs the sharp GHS theorem in ENTROPY form
   (`ρ log(C/ρ)`); the corpus has ~60 `Sieve/Ghs*.lean` modules + `HalaszGhsMasterBound.lean`
   (`exists_norm_sum_Icc_mul_log_le`, in `sieveMeanSquare` form) — check
   `HalaszGhsSharpCutoff.lean` for the cutoff/entropy shape before building anything new.

## Discipline notes
- No full/umbrella builds; `lake env lean --json <file>` (with a python filter) for positions.
- Heartbeats are per declaration — split long theorems into lemmas.
- `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩` instead of `set ... with`.
- Never rewrite a hypothesis into an expanded form the other hypotheses do not share (linarith
  then sees different atoms) — rewrite the goal instead.
