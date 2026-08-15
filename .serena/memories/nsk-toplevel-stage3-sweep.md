# Top-level new_scientific_knowledge stage-2 → stage-3 sweep ledger

Goal (session hook): formalize unconditionally every proven theorem of every TOP-LEVEL card in
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge (subfolders excluded — other agents),
move each card to 3-formalized. No premises standing for analytic inputs, no axioms, no
abstract-wrapper credit. User rules: **no full builds, no umbrella builds** — check with
`lake env lean <file>`, build only the specific oleans needed as dependencies, wire new modules
into the umbrella import list without building it. Axiom audit via scratch file.

## Promoted
2026-08-13 (10): prolate-dunster-exact-arcsine-leakage-limit; mass-shifted-characteristic-apex-
energy-boundary-law; gibbs-batch-entropy-production-nullspace-lift; gibbs-diagonal-entropy-
response-no-go; route-e-deninger-vacuum-finite-dilation-fracture; mass-shifted-projective-low-edge-
anchor-cofinal-spread; hedenmalm-finite-source-port-obstruction; hedenmalm-root-flux-modular-
charge-faithfulness; rank-two-commutator-parity-multiplicity-balance; route-r-reciprocal-log-
fisher-half-density-entrance-wall.
2026-08-14 (5): route-e-whole-anchor-capacity-displacement-conservation-law; route-e-physical-
saddle-antiscale-coercivity-barrier; route-e-critical-antiscale-diffuse-codiagonal-transfer-law
(no new Lean — its "remaining" items were OPEN TARGETS, not debt); route-e-gibbs-antiscale-
determinant-mellin-odd-cube-law; mass-shifted-frozen-admission-resolvent-flow-no-go.
2026-08-15 (2): halasz-reciprocal-coarea-optimality-law;
**route-e-source-faithful-euler-tilt-unit-shell-law** — closed (9)–(14), (20), (23) with new
modules EulerTiltCharacteristic / EulerTiltAmplitude / TerminalPrimeBand / RouteESaddleLowTilt.

21 cards remain in the folder.

## SHARED ANALYTIC INFRASTRUCTURE — reuse before building anything analytic
PNT / prime-window layer:
- `HTGeometry/RpowKernelRemainder.lean`, `HTGeometry/WindowRpowIntegral.lean`.
- `RHTower/PrimeRpowLogSumAsymptotic.lean` — `thetaError`, `primeRpowLogSumIoc_eq` (Abel identity,
  every exponent), `tendsto_primeRpowLogSumIoc`.
- `RHTower/RouteESaddlePntTransport.lean` — `primeRpowLogSumLE`, `tendsto_primeRpowLogSumLE`,
  `primeRpowLogSqSumLE`, `tendsto_primeRpowLogSqSumLE`, `saddleLogCenter`, `saddleLogVariance`,
  `eulerTiltDeficit`, `varianceTiltDeficit` (σ ∈ [1/2,1));
  **`RHTower/RouteESaddleLowTilt.lean` (NEW)** extends both limits to every σ ∈ (0,1)
  (`tendsto_saddleLogCenter_of_pos`, `tendsto_saddleLogVariance_of_pos`).
- `RHTower/ThetaRelativeErrorMass.lean`, `RHTower/TiltedPrimeLogSum.lean`
  (`abs_tiltedPrimeLogSum_sub_le`), `RHTower/EulerTiltMeanEnergy.lean` (`tiltedPrimeLogSumLE`,
  `logSquareTailConst`), `RHTower/MertensLogSquareSum.lean`, `RHTower/EulerTiltCovariance.lean`
  (`invSquareTailConst`, `logSqSquareTailConst`, `eulerTiltMassConst`, `abs_logLog_floor_sub_le`,
  `sum_primesLE_log_div_eq`, `primeLogSqSumLE`), `RHTower/EulerTiltSaddle*.lean`,
  `RHTower/EulerTiltEscape.lean`, `RHTower/PrimeCosineDefect.lean`,
  `RHTower/EulerTiltCharacteristic.lean` (`eulerTiltCharacteristic`, `abs_two_log_norm_add_euler_le`,
  `primeRpowSum`, `abs_primeRpowSum_sub_logLog_le`), `RHTower/EulerTiltAmplitude.lean`
  (`seven_lt_exp_two`, `quadraticHead_le`, `harmonicTail_le`, `abs_primeCosineDefect_le_const`,
  `exists_bound_log_norm_eulerTiltCharacteristic`), `RHTower/TerminalPrimeBand.lean`
  (`terminalBandMass`, `log_sub_log_le_of_le_add`, `tendsto_terminalBandMass`).
- Mertens: `Sieve/MertensSecondSharp.lean` (`abs_mertensS_sub_logLog_sub_const_le`),
  `Sieve/MertensFirst.lean` (`mertensFirst_upper`), `MertensPrimeWindowWeakConvergence.lean`
  (`mertensPrimeWeightSum`, `abs_mertensPrimeWeightSum_floor_sub_log_le` — bound is `B + 1`).
- Mellin–Plancherel: `MellinLinePolarization.lean`, `FiniteExponentialSumMellin.lean`,
  `GibbsFourFieldMellinPolarization.lean`.
- Finite Gauss quadrature (for the Padé cards): `HTGeometry/FiniteGaussQuadrature.lean`,
  `GaussQuadratureNodes.lean`, `GaussNodeDenominator.lean`, `GaussCauchyPolynomialIdentity.lean`,
  `SecondKindMomentPolynomials.lean`, `FiniteOrthogonalMomentPolynomials.lean`.
- GHS/Halász layer: ~60 `Sieve/Ghs*.lean` modules + `HalaszGhsMasterBound.lean`,
  `HalaszGhsSharpCutoff.lean` (master bound in `sieveMeanSquare` form, NOT yet the entropy form
  `ρ log(C/ρ)` the real-twist card's (Z11)–(Z13) needs).

## IN PROGRESS: real-twist-zeta-deficit-transfer-law
Card gate says "2→3 paused by user", not blocked on open math. Done so far (all compile clean,
axiom-audited only after olean build):
- **`RHTower/PretentiousDistance.lean`** — `unitDiskDist`, `unitDiskDist_eq`,
  `norm_sub_sq_le_two_mul_unitDiskDist`, `sqrt_unitDiskDist_triangle` (local pretentious triangle
  inequality on the closed disc), `sqrt_sum_le_of_sqrt_le` (Minkowski for finite sums),
  `pretentiousDistSq`, `sqrt_pretentiousDistSq_triangle`, `primeChar`,
  `pretentiousDistSq_primeChar` (= ∑(1−cos 2α log p)/p), `pretentiousDistSq_real_reflect` (Z9),
  `pretentiousDistSq_primeChar_le_four_mul` (**Z10**).
- **`RHTower/ZetaEulerLogPrimeSum.lean`** — `zetaLinePoint`, `log_norm_riemannZeta_eq_re_eulerLog`,
  `primeCosTsum`, `norm_log_one_sub_sub_self_le`, `abs_re_neg_log_one_sub_sub_re_le`,
  `abs_re_eulerLog_sub_primeCosTsum_le` (≤ invSquareTailConst).
- **`RHTower/ZetaOneLineDeficit.lean`** — `primeRpowCoeff`/`primeRpowLogCoeff`/`primeCosCoeff`,
  `tsum_primeRpowLogCoeff_le` (≤ 1/δ + C₀), `tsum_tail_primeRpowCoeff_le` (tail beyond x is
  ≤ (1/δ+C₀)/log x by the log p ≥ log x trick), `abs_sum_primeCos_shift_le`, `primeClockEnergy`,
  **`abs_zeta_deficit_sub_primeClockEnergy_le` = (Z2a)** (uniform in τ, x ≥ e²).
NEXT: (Z8) character separation from (Z2a); then (Z2c)/(Z2d) — transport the corpus Littlewood
rate (`Sieve/ZetaLineRate.lean::norm_riemannZeta_line_rate_clean`, `DirichletBlockAbel`,
`DirichletOrderRate`, `ZetaPartialSumTruncation`) to the shifted line `Re s = 1+1/log x`
uniformly in prefixes; then (Z3) via (Z10); then the GHS cellwise transfer (Z11)–(Z13), which
needs the entropy-form sharp GHS theorem.

## Remaining cards (21) and blockers
- **Matomäki–Teräväinen all-interval E₃** blocks 4 route-e cards (whole-anchor-bidirectional,
  reciprocal-allocation-carleson, parity-coalesced-full-mass, grade-recurrent-sparse-reservoir).
- **Shifted-Möbius (Chowla/MR Theorem 2)**: coprime-square-root-sign-law (its unconditional
  sqrt-window capstone is already a promoted stage-3 CHILD card; the parent keeps below-√ targets),
  growing-reciprocal-marker, reciprocal-marker-hall-law.
- **Hard-edge family (8 cards)** gated on `mass-shifted-hard-edge-paley-wiener-compactification`.
- **Padé pair**: moving-center-pade-worldline-law (needs a *moving* Gauss layer: differentiability
  of nodes/weights in the mass parameter via IFT — corpus Gauss layer is at fixed moments),
  pade-carathéodory-boundary-resolution-law.
- Others: real-twist-zeta-deficit-transfer-law (in progress), mass-xi-finite-true-prime-cone
  (253KB), parity-free-simple-ground-fourier-real-zero-law,
  mass-shifted-hyperbolic-capacity-contact-defect-law.

## Working discipline reminders
- Multiple concurrent peer sessions commit into this tree; never `cat >` over an existing file.
- Bash cwd persists between calls — always `cd .../formal` first.
- `lake env lean --json <file>` + a tiny python filter gives error POSITIONS; plain output can hide
  a stray `ring` info (the lint gate fails on those).
- Heartbeats are per declaration: a long theorem with many nlinarith calls hits the 200000 cap →
  split into lemmas (this is what fixed EulerTiltAmplitude and TerminalPrimeBand).
- `set x := e with h` makes a let-bound local that blows up `isDefEq`; use
  `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩` instead.
- `field_simp` often closes goals fully; a trailing `ring` then errors "No goals".
- Mathlib v4.32 names: `Complex.sq_norm` (not `Complex.sq_abs`), `Complex.re_tsum`,
  `Complex.norm_log_one_add_sub_self_le`, `Summable.tsum_le_of_sum_range_le`,
  `Summable.tsum_le_tsum_of_inj`, `Summable.sum_add_tsum_compl`, `tsum_div_const` (no args),
  `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz), `Nat.Primes.summable_rpow`,
  `Real.summable_one_div_nat_rpow`, `Mertens.summable_log_div_rpow`, `hf.map Complex.reAddGroupHom
  Complex.continuous_re` for Summable of real parts, `norm_tsum_le_tsum_norm`,
  `div_le_div_of_nonneg_right h hc.le`, `inv_le_comm₀`, `Real.sqrt_div`, `Real.sq_sqrt`.
