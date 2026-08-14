# Top-level new_scientific_knowledge stage-2 → stage-3 sweep ledger

Goal (session hook): formalize unconditionally every proven theorem of every TOP-LEVEL card in
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge (subfolders excluded — other agents),
move each card to 3-formalized. No premises standing for analytic inputs, no axioms, no
abstract-wrapper credit. Build foreground/background but one process; axiom audit via scratch file;
wire umbrellas.

## Promoted
2026-08-13 (10): prolate-dunster-exact-arcsine-leakage-limit; mass-shifted-characteristic-apex-
energy-boundary-law; gibbs-batch-entropy-production-nullspace-lift; gibbs-diagonal-entropy-
response-no-go; route-e-deninger-vacuum-finite-dilation-fracture; mass-shifted-projective-low-edge-
anchor-cofinal-spread; hedenmalm-finite-source-port-obstruction; hedenmalm-root-flux-modular-
charge-faithfulness; rank-two-commutator-parity-multiplicity-balance; route-r-reciprocal-log-
fisher-half-density-entrance-wall.
2026-08-14 (3):
- route-e-whole-anchor-capacity-displacement-conservation-law (new module
  `RHTower/MobiusWholeAnchorTerminalDensityCollapse.lean`).
- route-e-physical-saddle-antiscale-coercivity-barrier (full PNT transport; module list below).
- route-e-critical-antiscale-diffuse-codiagonal-transfer-law — **no new Lean needed**: all its
  theorems A–H were already formalized; the items that kept it at stage 2 ((50), signed recurrence
  seam) are OPEN TARGETS stated by the card, not proved statements. Lesson: check whether a card's
  "remaining" item is a formalization debt or an open frontier target before working on it.

## SHARED ANALYTIC INFRASTRUCTURE (2026-08-14) — reuse before building anything analytic
- `HTGeometry/RpowKernelRemainder.lean` — `tendsto_rpowKernelRemainder` (g→0, |K| ≤ C t^(a-1) ⇒
  (∫_2^x gK)/x^a → 0).
- `HTGeometry/WindowRpowIntegral.lean` — `tendsto_logPow_div_rpow`, `tendsto_logSubPow_div_rpow`,
  `windowRpowIntegral` (= ∫_2^Y u^(a-1)(log Y-log u)^j du) with `_succ` recursion, `_le` bound
  (≤ j!/a^(j+1) Y^a), `tendsto_windowRpowIntegral`.
- `RHTower/PrimeRpowLogSumAsymptotic.lean` — `thetaError`, `tendsto_thetaError`,
  `abs_thetaError_le`, Abel identity, **`tendsto_primeRpowLogSumIoc`**:
  (∑_{2<p≤x} p^(a-1) log p)/x^a → 1/a for every a > 0.
- `RHTower/PrimeWindowLaw.lean` — **`tendsto_primeWindowSum`**:
  Y^{-a} ∑_{2<p≤Y} p^(a-1)(log Y-log p)^j log p → j!/a^(j+1).
- `RHTower/PrimeWindowLawNoLog.lean` — `primeWindowSumNoLog`, `primeWindowSum_eq`
  (S_j = (log Y)N_j - N_{j+1}), `tendsto_primeWindowSumNoLog` (N_j = o(Y^a)),
  **`tendsto_logY_mul_primeWindowSumNoLog`**: (log Y)Y^{-a}N_j → j!/a^(j+1).
- `RHTower/RouteESaddlePntTransport.lean` — `sum_primesLE_eq_add_sum_Ioc`,
  `tendsto_primeRpowLogSumLE`, `tendsto_eulerTiltDeficit`, `tendsto_saddleLogCenter`,
  `tendsto_primeRpowLogSqSumLE`, `tendsto_saddleLogVariance`.
- `RHTower/RouteEAntiscaleEnergyTransport.lean` — `abs_two_sub_two_cos_sub_sq_le` (uniform
  |2-2cos θ-θ²| ≤ 5θ⁴), `sub_pow_four_le`, `antiscaleFrequency`, `antiscaleEnergy`,
  `tendsto_antiscaleEnergy`, `tendsto_antiscaleFrequency`, `tendsto_gamma_normSq_antiscale`.
- `RHTower/RouteEEulerDeficitIdentity.lean` + `RouteEEulerDeficitTransport.lean` — exact deficit
  identity, `neg_log_one_sub_le`, Mertens remainder, `tendsto_eulerLogDeficit`,
  `tendsto_eulerLogDeficit_div_log`, `eventually_saddle_coercivity_fails`, half-density corollaries.
- `RHTower/RouteEGibbsTerminalChamber.lean` (2026-08-14) — `terminalChamber` (X/e<p≤X),
  `terminalFrequency` π/log X, chamber phase bounds, `cos_terminalChamber_le` (≤ -1/2 past e³),
  `chamberMass_eq_sub`, **`tendsto_chamberMass`** (mass·log X/√X → 2-2e^{-1/2}),
  `chamberDeterminant`, `chamberDrag` bounds, `exp_chamberMass_div_three_sub_one_le`,
  `log_one_add_abs_chamberDeterminant_le`, `chamberMass_div_three_le_log_one_add`.
- `RHTower/RouteEGibbsWideBatch.lean` (2026-08-14) — `criticalCosSum`,
  **`tendsto_criticalCosSum`** (∑_{p≤X}p^{-1/2}cos(t_X log p)·log X/√X → -2), `prefixModulus_ge`.

## Card in progress: route-e-gibbs-antiscale-determinant-mellin-odd-cube-law
Done: (1)-(7),(11)-(19) already in `GibbsAntiscaleDeterminantOddCube.lean` /
`GibbsCriticalDissipationAntiscaleResonance.lean`; (20)-(27) terminal chamber ✓;
(28)/(29) prefix modulus ✓; the linear grade of (36) ✓.
Remaining: (30)-(33) prefix phase law (needs ∑√p log p/(p-1) = 2√Y(1+o(1)) — available from
`tendsto_primeRpowLogSumLE` at a = 1/2 plus a convergent correction — and arctan/sin error
control); (34) modulus stability (needs **Mertens' third theorem** ∏_{p≤Y}(1-1/p) ≍ 1/log Y, NOT in
the corpus: build from `Sieve.mertensS` two-sided bounds and log(1-x) ≥ -x-x²);
(37)/(38) full rapidity (artanh correction O(∑p^{-3/2}) + d_p vs p^{-1/2});
(8) four-field Mellin–Plancherel polarization (corpus Mellin layer: `RHTower/L2MellinUnitary.lean`,
`MobiusLaplaceMellinPlancherelBridge.lean`).

## Remaining cards (25) and blockers
- **External deep theorem (Matomäki–Teräväinen all-interval E₃)** blocks: route-e-whole-anchor-
  bidirectional-harmonic-e3-law, route-e-reciprocal-allocation-square-root-jacobian-carleson-
  reduction, route-e-parity-coalesced-full-mass-reservoir-cube-law, route-e-grade-recurrent-sparse-
  reservoir-cube-admission. (See `docs/drafts/pipeline/2-fully-proven/route-e-forbidden-support-e3-
  stability.md`: "the all-interval theorem it perturbs is a deep external input, not present in
  Mathlib".) Formalizing MT is a standalone multi-month project.
- **Shifted-Möbius-correlation (Chowla-type) inputs**: route-e-coprime-square-root-mobius-product-
  sign-law, route-e-growing-reciprocal-marker-low-breadth-transport, route-e-reciprocal-marker-
  mobius-hall-law — but these cards prove *equivalences* conditional on the correlation bound;
  check whether the equivalence itself is already Lean before assuming debt.
- **Hard-edge family (8 cards)** — all gated on a literal hard-edge Paley–Wiener compactification;
  attack `mass-shifted-hard-edge-paley-wiener-compactification` first.
- **Orthogonal-polynomial/Padé cards**: mass-shifted-moving-center-pade-worldline-law,
  mass-shifted-pade-carathéodory-boundary-resolution-law — finite Gauss-quadrature mathematics,
  formalizable with the corpus Favard layer (`HTGeometry/FavardJacobiMomentRealization.lean`).
- mass-shifted-frozen-admission-resolvent-flow-no-go — card refuses a wrapper, but its finite
  three-atom countermodel is formalizable as stated.
- Others: halasz-reciprocal-coarea-optimality-law, real-twist-zeta-deficit-transfer-law,
  mass-xi-finite-true-prime-cone (253KB), parity-free-simple-ground-fourier-real-zero-law,
  mass-shifted-hyperbolic-capacity-contact-defect-law, route-e-source-faithful-euler-tilt-unit-
  shell-law (needs uniform-in-δ PNT sums; build ∫_2^∞|θ(u)-u|/u²du < ∞ first).

## Working discipline reminders
- Multiple concurrent peer sessions; check mtimes/git status before touching a module; never
  `cat >` over an existing Lean file.
- `lake build <module>` authoritative; long builds via run_in_background.
- Axiom audit in the session scratchpad; baseline [propext, Classical.choice, Quot.sound].
- Bash cwd persists between calls — always `cd .../formal` first.
- `field_simp` often closes goals fully; a trailing `ring` then errors "No goals" (and sometimes it
  is needed — check both).
- v4.32: `le_total` not `le_or_lt`; `div_le_div_of_nonneg_right (h : a ≤ b) (0 ≤ c)`;
  `div_le_div_of_nonneg_left (0 ≤ a) (0 < c) (c ≤ b)`; `squeeze_zero_norm'`; `Complex.sq_norm`;
  `Complex.exp_ofReal_mul_I_re/_im`; `Complex.norm_exp_ofReal_mul_I`; `Real.log_prod (h)`;
  `Finset.sum_neg_distrib`; `Filter.Tendsto.atTop_mul_atTop₀`; `Finset.prod_le_prod` (not
  `Finset.prod_le_one`/`one_le_prod'` — those need multiplicative-order instances);
  `Real.one_sub_sq_div_two_le_cos`; `Real.cos_le_cos_of_nonneg_of_le_pi`.
