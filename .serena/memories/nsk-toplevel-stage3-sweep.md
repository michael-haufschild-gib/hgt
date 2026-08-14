# Top-level new_scientific_knowledge stage-2 → stage-3 sweep ledger

Goal (session hook): formalize unconditionally every proven theorem of every TOP-LEVEL card in
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge (subfolders excluded — other agents),
move each card to 3-formalized. No premises standing for analytic inputs, no axioms, no
abstract-wrapper credit. User rules: no full builds / no umbrella builds — check with
`lake env lean <file>`, build only the specific oleans needed as dependencies, wire new modules
into the umbrella import list without building it. Axiom audit via scratch file.

## Promoted
2026-08-13 (10): prolate-dunster-exact-arcsine-leakage-limit; mass-shifted-characteristic-apex-
energy-boundary-law; gibbs-batch-entropy-production-nullspace-lift; gibbs-diagonal-entropy-
response-no-go; route-e-deninger-vacuum-finite-dilation-fracture; mass-shifted-projective-low-edge-
anchor-cofinal-spread; hedenmalm-finite-source-port-obstruction; hedenmalm-root-flux-modular-
charge-faithfulness; rank-two-commutator-parity-multiplicity-balance; route-r-reciprocal-log-
fisher-half-density-entrance-wall.
2026-08-14 (4):
- route-e-whole-anchor-capacity-displacement-conservation-law (`MobiusWholeAnchorTerminalDensityCollapse.lean`).
- route-e-physical-saddle-antiscale-coercivity-barrier (full PNT transport).
- route-e-critical-antiscale-diffuse-codiagonal-transfer-law — **no new Lean needed**: its
  "remaining" items were OPEN TARGETS, not proved statements. Always check debt vs frontier first.
- route-e-gibbs-antiscale-determinant-mellin-odd-cube-law — completed (35)-(38) and (7)/(8).

## SHARED ANALYTIC INFRASTRUCTURE — reuse before building anything analytic
PNT / prime-window layer:
- `HTGeometry/RpowKernelRemainder.lean` — `tendsto_rpowKernelRemainder`.
- `HTGeometry/WindowRpowIntegral.lean` — `tendsto_logPow_div_rpow`, `tendsto_logSubPow_div_rpow`,
  `windowRpowIntegral`, `_succ`, `_le`, `tendsto_windowRpowIntegral`.
- `RHTower/PrimeRpowLogSumAsymptotic.lean` — `thetaError`, `abs_thetaError_le`,
  **`tendsto_primeRpowLogSumIoc`** ((∑_{2<p≤x}p^{a-1}log p)/x^a → 1/a).
- `RHTower/PrimeWindowLaw.lean` / `PrimeWindowLawNoLog.lean` — `tendsto_primeWindowSum`,
  `primeWindowSumNoLog`, `tendsto_primeWindowSumNoLog`, `tendsto_logY_mul_primeWindowSumNoLog`.
- `RHTower/RouteESaddlePntTransport.lean` — `tendsto_primeRpowLogSumLE`, `tendsto_eulerTiltDeficit`,
  `tendsto_saddleLogCenter`, `tendsto_saddleLogVariance`.
- `RHTower/Sieve/MertensThird.lean` — `prod_one_sub_inv_le` (∏(1-1/p) ≍ 1/log N), telescoping helpers.
- `RHTower/RouteEAntiscaleEnergyTransport.lean`, `RouteEEulerDeficitIdentity/Transport.lean` —
  antiscale frequency/energy limits, `neg_log_one_sub_le`, saddle coercivity failure.

Terminal-chamber / Gibbs批 layer (all 2026-08-14):
- `RouteEGibbsTerminalChamber.lean`, `RouteEGibbsWideBatch.lean` (`criticalCosSum`,
  `tendsto_criticalCosSum` → -2), `RouteEGibbsPrefixPhase.lean` (`tendsto_prefixPhase_threshold`),
  `RouteEGibbsPrefixModulus.lean` (`tendsto_prefixModulus_ratio`).
- `RouteEGibbsRapidity.lean` — `criticalHalfDensity`, `sub_criticalHalfDensity_le`,
  `abs_two_mul_criticalHalfDensity_mul_cos_le`, `batchRapidity`, `batchCosSum`,
  `abs_batchRapidity_sub_two_mul_batchCosSum_le`, **`tendsto_batchRapidity`** (→ -4),
  plus reusable `tendsto_logRpow_div_rpow` and `tendsto_mertensS_floor_mul_log_div_sqrt`.
- `RouteEGibbsBatchDeterminant.lean` — `batchPrimes/batchRadius/batchPhase/batchCoordinate`,
  `batchEulerDeterminant`, `batchEulerDeterminant_eq` (= 2·mass·transverse·sinh R),
  `log_batchMass_le`, `neg_log_batchTransverse_le`, `exp_le_four_mul_sinh`,
  **`tendsto_log_one_add_abs_batchEulerDeterminant`** (→ 4).
- `HTGeometry/ArctanSinTaylor.lean` — |arctan u - u| ≤ |u|³, |sin u - u| ≤ |u|³,
  |log(1+x)-x| ≤ 2x² (|x|≤1/2), |artanh u - u| ≤ 4u² (|u|≤1/2).

**Mellin–Plancherel stack (NEW 2026-08-14, reusable for any finite exponential-sum card):**
- `RHTower/MellinLinePolarization.lean` — `integral_conj_fourier_mul_fourier` (Parseval
  polarization for L¹∩L²), **`integral_conj_mellin_line_mul_mellin_line`**
  (∫ conj(M f(σ+it))·M g(σ+it) dt = 2π·M(conj f·g)(2σ)), `continuous_fourier_of_integrable`,
  `continuous_mellin_line`, `integrable_conj_mellin_line_mul_mellin_line`.
  Built on the corpus bridge `MobiusLaplaceMellinPlancherelBridge.lean`
  (`logMellinLineSource`, `mellin_line_eq_fourier_logMellinLineSource`,
  `integrable_norm_sq_mellin_line_of_logMellinLineSource`) + Mathlib `Lp.inner_fourier_eq`.
- `RHTower/FiniteExponentialSumMellin.lean` — `expDecaySum`, `abs_expDecaySum_le`,
  `mellin_exp_neg_mul`, **`mellin_expDecaySum`** (= Γ(s)·∑ c_i m_i^{-s}),
  `mellinConvergent_of_exp_bound`, `integrable_exp_neg_mul_exp_neg_exp`,
  **`integrable_logMellinLineSource_of_exp_bound`**, **`memLp_two_logMellinLineSource_of_exp_bound`**
  (both from a single bound ‖f x‖ ≤ C e^{-ax} on Ioi 0 — no change-of-variables needed).
- `RHTower/GibbsFourFieldMellinPolarization.lean` — `subsetMass`, `subsetMass_cpow`,
  `eulerCharacter`, `sum_powerset_eq_eulerCharacter`, `gibbsCoarseField(C)`,
  `gibbsCoarseField_eq_sum_gibbsDiag`, `mellin_gibbsCoarseFieldC` (= card eq (7)),
  `gibbsAntiscaleDeterminant`, **`integral_gammaNormSq_mul_eulerPair_eq_mellin_gibbsAntiscaleDeterminant`**
  (= card eq (8)).

## Remaining cards (24) and blockers
- **Matomäki–Teräväinen all-interval E₃** blocks: route-e-whole-anchor-bidirectional-harmonic-e3-law,
  route-e-reciprocal-allocation-square-root-jacobian-carleson-reduction,
  route-e-parity-coalesced-full-mass-reservoir-cube-law,
  route-e-grade-recurrent-sparse-reservoir-cube-admission.
- **Shifted-Möbius (Chowla-type) inputs**: route-e-coprime-square-root-mobius-product-sign-law,
  route-e-growing-reciprocal-marker-low-breadth-transport, route-e-reciprocal-marker-mobius-hall-law
  — check whether the card's *equivalence* is already Lean before assuming debt.
- **Hard-edge family (8 cards)** gated on a literal hard-edge Paley–Wiener compactification;
  attack `mass-shifted-hard-edge-paley-wiener-compactification` first.
- **Padé/orthogonal-polynomial**: mass-shifted-moving-center-pade-worldline-law,
  mass-shifted-pade-carathéodory-boundary-resolution-law (corpus Favard layer).
- mass-shifted-frozen-admission-resolvent-flow-no-go — finite three-atom countermodel formalizable.
- Others: halasz-reciprocal-coarea-optimality-law, real-twist-zeta-deficit-transfer-law,
  mass-xi-finite-true-prime-cone (253KB), parity-free-simple-ground-fourier-real-zero-law,
  mass-shifted-hyperbolic-capacity-contact-defect-law.
- **NEXT (in progress)**: route-e-source-faithful-euler-tilt-unit-shell-law — only (9)–(14) remain:
  moving tilt σ_x = 1 + 2log ℓ/ℓ² + …, A = log ℓ+O(1), B = ℓ-log ℓ+O(1), C = ℓ²/2+O(ℓ log ℓ),
  t* = 2π/ℓ+…, D = π² log ℓ+O(1), t*E* = 2π+…, |E e^{i(πN-t*E)}| = ℓ^{-2}e^{O(1)}.
  Route: expand p^{-σ} = p^{-1}e^{-δ log p} with |e^{-y}-1| ≤ y, so everything reduces to the
  Mertens moments M_k(Y) = ∑_{p≤Y}p^{-1}(log p)^k for k = 0,1,2 (k=0,1 exist in
  `Sieve/MertensSecondSharp.lean` / `MertensFirst`; k=2 by Abel summation from Mertens first).

## Working discipline reminders
- Multiple concurrent peer sessions; check mtimes/git status before touching a module; never
  `cat >` over an existing Lean file.
- Axiom audit in the session scratchpad; baseline [propext, Classical.choice, Quot.sound].
- Bash cwd persists between calls — always `cd .../formal` first.
- `field_simp` often closes goals fully; a trailing `ring` then errors "No goals".
- Mathlib v4.32 name traps: `le_total` (not `le_or_lt`); `div_le_div_of_nonneg_right h hc.le`;
  `squeeze_zero_norm'`; `Real.log_prod h` (one explicit arg); `Finset.prod_le_prod` (not
  `prod_le_one`/`one_le_prod'`); `continuousAt_cpow_const` is ROOT namespace (+
  `Complex.mem_slitPlane_iff`); `Complex.real_smul` for ℝ•ℂ; `RCLike.inner_apply'` (conj x * y);
  `MeasureTheory.integral_finsetSum`; `continuous_finsetSum`; `integrableOn_exp_Iic`;
  `exp_neg_integrableOn_Ioi`; no `Real.sinh_pos` (use `positivity`); `Complex.norm_real`.
- `ring` silently emits a stray "Try this: ring_nf" info when an argument like `rexp (-(-v))`
  is not syntactically normalized — insert `neg_neg` rewrites to keep output clean (the lint gate
  fails on warnings).
