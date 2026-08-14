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
2026-08-14 (5):
- route-e-whole-anchor-capacity-displacement-conservation-law
- route-e-physical-saddle-antiscale-coercivity-barrier
- route-e-critical-antiscale-diffuse-codiagonal-transfer-law (no new Lean: its "remaining" items
  were OPEN TARGETS, not debt — always check debt vs frontier first)
- route-e-gibbs-antiscale-determinant-mellin-odd-cube-law (finished (35)–(38) and (7)/(8))
- mass-shifted-frozen-admission-resolvent-flow-no-go (`RHTower/FrozenAdmissionResolventFlowNoGo.lean`:
  literal three-atom flow, FAR.3–FAR.6, FAR.9–FAR.14, capstone
  `exists_frozen_admission_source_sign_reversal`).  Lesson: a card that "declines Lean" because a
  *generic wrapper* would be theatre can still be formalized literally.

## SHARED ANALYTIC INFRASTRUCTURE — reuse before building anything analytic
PNT / prime-window layer:
- `HTGeometry/RpowKernelRemainder.lean`, `HTGeometry/WindowRpowIntegral.lean`
  (`tendsto_logPow_div_rpow`, `windowRpowIntegral`).
- `RHTower/PrimeRpowLogSumAsymptotic.lean` — `thetaError`, `abs_thetaError_le`,
  `integrableOn_thetaError`, `intervalIntegrable_thetaError_mul`,
  **`primeRpowLogSumIoc_eq`** (Abel identity, valid for EVERY exponent `a`, no positivity),
  `integral_derivRpow_mul_theta_eq` (needs `a > 0`), `tendsto_primeRpowLogSumIoc`.
- `RHTower/PrimeWindowLaw.lean` / `PrimeWindowLawNoLog.lean`, `RouteESaddlePntTransport.lean`,
  `Sieve/MertensThird.lean`, `Sieve/MertensSecondSharp.lean` (`abs_mertensS_sub_logLog_sub_const_le`).
- **`RHTower/ThetaRelativeErrorMass.lean` (NEW 2026-08-14)** — `integrableOn_inv_mul_log_sq`
  (∫ dt/(t log²t) on (e,∞)), `exp_neg_le_inv_sq` (e^{-c√v} ≤ 256/(c⁴v²)),
  `exists_abs_thetaError_le` (|θ(t)/t−1| ≤ C/(log t)²), `integrableOn_abs_thetaError_div_id`,
  `thetaRelMass`, **`abs_integral_thetaError_mul_rpow_le`**
  (|∫_2^x E(t)t^{-δ-1}dt| ≤ thetaRelMass, uniformly in δ ≥ 0, x ≥ 2).
- Mellin–Plancherel stack: `RHTower/MellinLinePolarization.lean`
  (`integral_conj_mellin_line_mul_mellin_line`, `continuous_mellin_line`,
  `integrable_conj_mellin_line_mul_mellin_line`), `RHTower/FiniteExponentialSumMellin.lean`
  (`expDecaySum`, `mellin_expDecaySum`, `mellinConvergent_of_exp_bound`,
  `integrable_logMellinLineSource_of_exp_bound`, `memLp_two_logMellinLineSource_of_exp_bound`),
  `RHTower/GibbsFourFieldMellinPolarization.lean` (`eulerCharacter`, `gibbsCoarseField`,
  `mellin_gibbsCoarseFieldC`, `integral_gammaNormSq_mul_eulerPair_eq_mellin_gibbsAntiscaleDeterminant`).
- Gibbs terminal/batch layer: `RouteEGibbsTerminalChamber/WideBatch/PrefixPhase/PrefixModulus/
  Rapidity/BatchDeterminant.lean` (`tendsto_batchRapidity` → −4,
  `tendsto_log_one_add_abs_batchEulerDeterminant` → 4, `tendsto_mertensS_floor_mul_log_div_sqrt`,
  `tendsto_logRpow_div_rpow`), `HTGeometry/ArctanSinTaylor.lean`.
- Finite Gauss quadrature (for the Padé cards): `HTGeometry/FiniteGaussQuadrature.lean`
  (`momentFunctional_eq_gaussSum_below` = exactness ≤ 2n−1,
  `momentFunctional_sub_gaussSum_eq_topCoeff_mul_nextNorm_below` = the `h_n` defect),
  `HTGeometry/GaussQuadratureNodes.lean`, `HTGeometry/GaussNodeDenominator.lean`.

## IN PROGRESS: route-e-source-faithful-euler-tilt-unit-shell-law
Only (9)–(14) remain (the card's (1)–(8) are in `RouteESourceFaithfulEulerTiltUnitShell.lean`).
Plan, with `ℓ = log Y`, `δ = σ−1 = O(log ℓ/ℓ²)`:
1. DONE: `ThetaRelativeErrorMass.lean` (uniform Abel remainder bound).
2. NEXT: `TiltedPrimeLogSum` — apply `primeRpowLogSumIoc_eq` with `a = -δ` (identity is
   exponent-free) + `integral_rpow` with the `r ≠ -1 ∧ 0 ∉ [[u,v]]` disjunct (the corpus's
   `HTGeometry.integral_rpow_sub_one` assumes `0 < a`, so a negative-exponent variant is needed),
   giving `|∑_{2<p≤Y} p^{-1-δ}log p − (1−Y^{-δ})/δ| ≤ K` uniformly for δ ∈ (0,1], Y ≥ 2 with
   K = (log 4+1) + 1 + 2log 2 + 2·thetaRelMass.
3. Then `(1−e^{-δℓ})/δ = ℓ − δℓ²/2 + O(δ²ℓ³)` (Taylor, |e^{-y}−1+y−y²/2| ≤ y³/6).
4. Denominator correction `∑ p^{-σ}log p/(1+p^{-σ}) − ∑p^{-σ}log p = O(1)` (bounded by
   `∑_n n^{-2σ}log n`, convergent for σ ≥ 3/4).
5. Saddle equation (8)/(9): μ_{σ,Y} strictly decreasing in σ, `E* = log(σ/x)`; solve for σ_x.
6. Weights `w_p = p^{-σ}/(1+p^{-σ})²`: (11)/(22) A = log ℓ+O(1) (Mertens second sharp),
   B = ℓ−log ℓ+O(1), C = ℓ²/2+O(ℓ log ℓ) (needs the k=2 Mertens moment ∑p^{-1}(log p)² by Abel
   summation), then (12) t* = 2π/ℓ+…, D = π² log ℓ+O(1), (13), and (14) via (25)/(26).

## Remaining cards (23) and blockers
- **Matomäki–Teräväinen all-interval E₃** blocks 4 route-e cards (whole-anchor-bidirectional,
  reciprocal-allocation-carleson, parity-coalesced-full-mass, grade-recurrent-sparse-reservoir).
- **Shifted-Möbius (Chowla-type)**: coprime-square-root-sign-law, growing-reciprocal-marker,
  reciprocal-marker-hall-law — check whether the card's *equivalence* is already Lean.
- **Hard-edge family (8 cards)** gated on `mass-shifted-hard-edge-paley-wiener-compactification`.
- **Padé pair**: moving-center-pade-worldline-law (needs *moving* Gauss data: differentiating
  nodes/weights in the mass parameter — the corpus Gauss layer is at fixed moments),
  pade-carathéodory-boundary-resolution-law.
- Others: halasz-reciprocal-coarea-optimality-law, real-twist-zeta-deficit-transfer-law,
  mass-xi-finite-true-prime-cone (253KB), parity-free-simple-ground-fourier-real-zero-law,
  mass-shifted-hyperbolic-capacity-contact-defect-law, route-e-source-faithful-euler-tilt (above).

## Working discipline reminders
- Multiple concurrent peer sessions commit into this tree; check `git status` before touching a
  module; never `cat >` over an existing Lean file.
- Bash cwd persists between calls — always `cd .../formal` first.
- `field_simp` often closes goals fully; a trailing `ring` then errors "No goals".
- Dot-notation traps: `h₂.add h₃` / `.const_mul` resolve to `HasFDerivAtFilter.*` unless
  `Mathlib.Analysis.Calculus.Deriv.Add`/`.Mul` are imported; `HasDerivAt.congr_deriv` is the clean
  way to fix a derivative value (avoid `convert`, which leaves instance-equality goals).
- After `HasDerivAt.pow`/`.mul`, `simp only [Pi.pow_apply, Pi.sub_apply]` before `push_cast; ring`.
- Mathlib v4.32 names: `le_total`; `div_le_div_of_nonneg_right h hc.le`; `squeeze_zero_norm'`;
  `Real.log_prod h`; `Finset.prod_le_prod`; `continuousAt_cpow_const` (ROOT namespace) +
  `Complex.mem_slitPlane_iff`; `Complex.real_smul`; `RCLike.inner_apply'`;
  `MeasureTheory.integral_finsetSum`; `continuous_finsetSum`; `integrableOn_exp_Iic`;
  `exp_neg_integrableOn_Ioi`; `integrableOn_Ioi_deriv_of_nonneg`; `setIntegral_mono_on`;
  `setIntegral_mono_set`; `inv_le_comm₀`; `inv_lt_inv₀`; `mul_nonneg_iff_of_pos_right`;
  no `Real.sinh_pos` (use `positivity`); `Complex.norm_real`.
- `ring` emits a stray "Try this: ring_nf" info when an argument like `rexp (-(-v))` is not
  syntactically normalized — insert `neg_neg` rewrites (the lint gate fails on warnings).
