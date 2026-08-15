# In-flight work: real-twist / zeta-deficit card (2026-08-15)

Companion to `nsk-toplevel-stage3-sweep`.

## CLOSED this session
- `halasz-reciprocal-coarea-optimality-law` → 3-formalized.
- `route-e-source-faithful-euler-tilt-unit-shell-law` → 3-formalized (modules
  EulerTiltCharacteristic / EulerTiltAmplitude / TerminalPrimeBand / RouteESaddleLowTilt).

## IN PROGRESS: real-twist-zeta-deficit-transfer-law
All of the following compile, are wired into `RHTower.lean`, and audit
`[propext, Classical.choice, Quot.sound]`:
- `RHTower/PretentiousDistance.lean` — **thin wrapper over the corpus distance layer**
  (`Sieve/DistanceTriangle.lean` has `mulDistSqPair`, `charFn`, `conj_charFn`;
  `Sieve/DistanceDiscTriangle.lean` has `sqrt_mulDistSqPair_triangle_disc`,
  `mulDistSqPair_nonneg_disc`, `sqrt_one_sub_re_triangle`, `sqrt_sum_sq_add_le`).
  New content only: `pretentiousDistSq_primeChar`, `pretentiousDistSq_real_reflect` (Z9),
  `pretentiousDistSq_primeChar_le_four_mul` (**Z10**).
- `RHTower/ZetaEulerLogPrimeSum.lean` — `zetaLinePoint`, `log_norm_riemannZeta_eq_re_eulerLog`,
  `primeCosTsum`, `abs_re_eulerLog_sub_primeCosTsum_le`.
- `RHTower/ZetaOneLineDeficit.lean` — `primeRpowCoeff`/`primeRpowLogCoeff`/`primeCosCoeff`,
  `tsum_primeRpowLogCoeff_le`, `tsum_tail_primeRpowCoeff_le`, `abs_sum_primeCos_shift_le`,
  `primeClockEnergy`, `zetaDeficitConst`, **`abs_zeta_deficit_sub_primeClockEnergy_le` = (Z2a)**.
- `RHTower/RealTwistDeficitTransfer.lean` — `zetaLineDeficit`,
  **`quarter_zetaLineDeficit_le_pretentiousDistSq` = (Z3)/(Z8)+(Z10)**.
- `RHTower/Sieve/DirichletPrefixLittlewood.lean` — the whole Littlewood chain re-derived with a
  free right endpoint (…_shape/endpoints/const/pow_two/exponent/assembled/canonical/capstone/
  explicit/balanced/threshold/order/**rate**`_prefix`).
- `RHTower/Sieve/ZetaShiftedLineRate.lean` — `cpow_shift_split`,
  `norm_dirichlet_shifted_prefix_le` (Abel with weight `n^{-δ}` via corpus `abel_block_bound`),
  **`norm_riemannZeta_shifted_line_rate`** = (Z2c) raw.
- `RHTower/ZetaLittlewoodDeficit.lean` — `littlewoodFreqThreshold`, `zetaHorizonLogThreshold`,
  `log_le_half`, `log_le_sqrt`, `littlewood_small_scale_le`, `littlewood_large_scale_le`,
  **`norm_riemannZeta_horizon_le`** (uniform `C_B log x/log log x` over `1 ≤ |τ| ≤ x^B`),
  **`zetaLineDeficit_ge` = (Z2d)**, **`quarter_littlewoodDeficit_le_pretentiousDistSq`**,
  `zetaLineDeficit_ge_of_power_law` = (Z14)⇒(Z15), `power_law_twist_gap` = (Z16).
- `RHTower/ZetaLineLowerBound.lean` — `zetaPoleFactor` (removable singularity), its continuity,
  `zetaLowRectangle` compactness, `exists_pos_le_norm_riemannZeta_low_freq`, `primeCosPlusSum`,
  `pretentiousDistSq_neg_one_eq` = (Z18c), `sum_norm_one_add_primeChar_sq`,
  `primeCosPlusSum_ge_low_freq` = (Z18d), **`exists_antiscale_frame` = (Z18b)**.

### REMAINING for this card
1. (Z11)–(Z13), (Z17), (Z18), (Z18a): the cellwise GHS transfer.  The corpus Halász bound
   `Sieve/HalaszGhsSharpCutoff.lean::norm_sum_Icc_mul_log_le_damped` is stated **in terms of
   `mulDistSqPair f (charFn t) (Nat.primesLE z)`** — i.e. exactly the distance my transfer lower
   bounds.  Start there; the entropy shape `ρ log(C/ρ)` may need assembling from `dampedSize`.
2. (Z19)/(Z19b)/(Z19c): finite-prime no-go — rational independence of prime logs (HTGeometry has
   it) + Kronecker/Dirichlet simultaneous approximation (check Mathlib coverage first).

## HARD-LEARNED: search the corpus for EVERY object before defining it
I re-derived the pretentious distance, its pointwise triangle inequality and Minkowski before
finding `Sieve/DistanceTriangle.lean` + `DistanceDiscTriangle.lean` + `MultiplicativeDistance.lean`
+ `FrequencySeparation.lean`.  The module was rewritten as a wrapper.  `formal_tools.py research`
missed it because I searched for "pretentious"; the corpus calls it **multiplicative distance**
(`mulDistSq`, `mulDistSqPair`, `charFn`, `distVec`).

## Discipline notes
- No full/umbrella builds; `lake env lean --json <file>` + python filter for error positions.
- Heartbeats are per declaration — split long theorems.
- `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩` instead of `set … with`.
- Never rewrite a hypothesis into a form the goal does not share (linarith needs common atoms);
  pass definitional equations as `h.le, h.ge` instead.
- `4 ≤ Real.log x` does NOT imply `0 < x` (Real.log is even); carry positivity explicitly.
