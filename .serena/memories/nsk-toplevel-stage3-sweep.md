# Top-level new_scientific_knowledge stage-2 → stage-3 sweep ledger

Goal (session hook): formalize unconditionally every proven theorem of every TOP-LEVEL card in
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge (subfolders excluded — other agents),
move each card to 3-formalized. No premises/hypotheses standing for analytic inputs, no axioms,
no abstract-wrapper credit. Module builds foreground, one process; axiom audit via scratch file;
wire umbrellas.

## Promoted (done, moved to 3-formalized)
- prolate-dunster-exact-arcsine-leakage-limit — 2026-08-13, module build + axiom audit clean.
- mass-shifted-characteristic-apex-energy-boundary-law — 2026-08-13, module
  XiShiftedCanonicalAdmissionCharacteristicApexEnergy built, 5 theorems audit clean.
- gibbs-batch-entropy-production-nullspace-lift — 2026-08-13, module build + audit clean.
- gibbs-diagonal-entropy-response-no-go — 2026-08-13, module build + audit clean.
- route-e-deninger-vacuum-finite-dilation-fracture — 2026-08-13, both modules rebuilt, all
  section claims re-audited clean.
- mass-shifted-projective-low-edge-anchor-cofinal-spread — 2026-08-13, sections 8–9 formalized
  (XiShiftedProjectiveAdjacentMeanResetBarrier.lean + Favard), 13 theorems audit clean.
- hedenmalm-finite-source-port-obstruction — 2026-08-13,
  XiHedenmalmFiniteSourcePortObstruction.lean, audit clean.
- hedenmalm-root-flux-modular-charge-faithfulness — 2026-08-13,
  HedenmalmRootFluxModularChargeFaithfulness.lean (energy positivity via interior continuity +
  root ODE; faithful law; full neutrality equivalence), audit clean.
- rank-two-commutator-parity-multiplicity-balance — 2026-08-13,
  RankTwoCommutatorParityMultiplicityBalance.lean (abstract balance + floor simplicity + gap
  current + literal truncated model on EuclideanSpace), 9 theorems audit clean.
- route-r-reciprocal-log-fisher-half-density-entrance-wall — 2026-08-13,
  RouteRReciprocalLogFisherEntranceWall.lean + new reusable
  Sieve/PrimeLogPowerTail.lean (∑ₚ 1/(p logˢp) < ∞ ∀ s>0 via BrunTitchmarsh Chebyshev BigO),
  8 theorems audit clean. Open producer (15) unchanged.

## Reusable lessons this sweep (also for lean-elaboration-traps)
- New WithLp structure API: EuclideanSpace elements build via `WithLp.toLp 2 fun i => ...`,
  read via application `x i` (PiLp app simp lemmas: PiLp.add_apply etc.), extensionality `ext i`
  (PiLp.ext). Raw Pi lambdas in toFun no longer typecheck.
- v4.32 renames hit: div_le_div_iff → div_le_div_iff₀; push_neg deprecated → `push Not`;
  Real.summable_one_div_nat_rpow (iff, needs full Mathlib import — PNTPlus cone lacks it);
  Nat.Primes.not_summable_one_div; isLittleO_log_rpow_rpow_atTop (log^r =o x^s, s>0);
  tendsto_inv_nhdsGT_zero; summable_of_isBigO (cofinite, general index) /
  summable_of_isBigO_nat (atTop); memℓp_gen_iff (0 < p.toReal); Nat.lt_ceil.
- degree_sub_lt / Monic.add_of_left need explicit `have hd : ... .degree = ... .degree`
  ascriptions — inline `by rw` args mis-elaborate with metavariable q.
- linear_combination fails across `set` bindings (atoms differ); avoid set in ring-normal goals.

## New infrastructure built this sweep
- HTGeometry/FavardJacobiMomentRealization.lean — constructive Favard: favardPoly, favardMoment,
  orthogonality, positivity, monicOrtho identification, exists_positiveMomentForm_of_jacobiData.
  Compiles clean, wired into HTGeometry umbrella (2026-08-13).
- RHTower/XiShiftedProjectiveAdjacentMeanResetBarrier.lean (in progress) — packet flux/mean/
  energy/clock defs, LAR.23-26 identities + reset barrier + hyperbolic action form, plus
  resetCounter* counterfamily (LAR.27-29) with Tendsto divergence/boundedness and
  no-locally-bounded-charge falsification. Build of cone pending under peer contention.

## Interface notes (verified)
- eval_mul_XiC_mem_of_coordinateMultiplication_stable (XiHedenmalmInvariantHomogenization.lean:78),
  xiCoordinateMultiplication (XiHedenmalmMultiplicityChain.lean:269), XiC_analytic
  (XiHadamardFactorization.lean:209), XiC_zero_ne (:320) — hedenmalm obstruction inputs.
- XiDivisorSupport = ↥(MeromorphicOn.divisor xi Set.univ).support (XiCanonicalProduct.lean:21);
  burnolCartierDividedShiftHeadFlux (BurnolCartierHeadEnergyStokesFlux.lean:34).
- not_summable_one_div_on_primes used in StieltjesLaneCutoffDivergence.lean; Cauchy condensation
  in mathlib PSeries (summable_condensed_iff_of_nonneg); prime dyadic tail for
  ∑ 1/(p (log p)^s), s>0 must be built (Chebyshev/π(x) route, PNTPlus.BrunTitchmarsh available).
- rank-two-commutator card: PMB.1-16 are literal finite linear algebra, formalizable as stated.
- parity-free card: finite odd theorem (PF.1-14) bounded work; §4 infinite theorem is a program
  (truncated convolution on L², min-max, Hurwitz).

## Near (partial Lean exists; finish exact remaining content)
- mass-shifted-projective-low-edge-anchor-cofinal-spread — survivor formalized+built
  (XiShiftedCanonicalAdmissionProjectiveCofinalSpread.lean); remaining paper-only: exact
  positive-Jacobi reset counterfamily + Xi denominator obstruction (finite algebra, formalizable).
- route-e-deninger-vacuum-finite-dilation-fracture — all three theorem blocks formalized; check
  claim-completeness, then promote.
- route-e-source-faithful-euler-tilt-unit-shell-law — remaining: PNT asymptotics (9)–(14).
- route-e-physical-saddle-antiscale-coercivity-barrier — remaining: PNT transport (3)–(10).
- route-e-gibbs-antiscale-determinant-mellin-odd-cube-law — remaining: four-field Mellin
  polarization + PNT terminal lower bounds.
- route-e-critical-antiscale-diffuse-codiagonal-transfer-law — remaining: estimate (50) + signed
  recurrence seam.
- route-e-reciprocal-allocation-square-root-jacobian-carleson-reduction — remaining: stretched-L
  asymptotic column estimate (4) + co-moving flux.
- route-e-parity-coalesced-full-mass-reservoir-cube-law — remaining: token supply, physical
  co-degree, mixed Gibbs asymptotics, seam flux.
- route-e-whole-anchor-capacity-displacement-conservation-law — remaining: global E3 counting,
  Mertens transport, asymptotics (2)–(6).
- route-e-grade-recurrent-sparse-reservoir-cube-admission — remaining: structured all-interval E3
  theorem + asymptotic pool laws.

## Not started / paused (real analytic formalization programs)
- halasz-reciprocal-coarea-optimality-law — build plan listed in card ("Lean notes only" section:
  PNTPlus.BrunTitchmarsh, GallagherAlmostDiagonal, PerronFiniteSum, Ramare modules).
- real-twist-zeta-deficit-transfer-law — Littlewood line-rate chain + GHS entropy pieces mostly in
  corpus already per card.
- route-r-reciprocal-log-fisher-half-density-entrance-wall — deferred during refactor; re-check.
- route-e-whole-anchor-bidirectional-harmonic-e3-law — not started (refactor pause).
- mass-xi-finite-true-prime-cone — 253KB card, paper-only pass; huge.
- route-e-coprime-square-root-mobius-product-sign-law / route-e-growing-reciprocal-marker-low-
  breadth-transport / route-e-reciprocal-marker-mobius-hall-law — large sieve programs; much Lean
  exists; hard gates reduced to comparisons vs Brun–Titchmarsh / shifted Möbius correlations —
  check which pieces are paper-proved vs open before working.

## Gated-by-card-design (card text refuses abstract wrappers; need LITERAL constructions)
- mass-shifted-frozen-admission-resolvent-flow-no-go — card explicitly withholds 2→3 (generic
  countermodel gives no completed-Xi theorem). Candidate: formalize exact three-atom countermodel
  as literal theorem if promotion is to happen at all.
- mass-shifted-hyperbolic-capacity-contact-defect-law — [LEAN GATED].
- parity-free-simple-ground-fourier-real-zero-law, rank-two-commutator-parity-multiplicity-balance
  — "infrastructure theatre" warnings; literal hard-edge operator needed.
- mass-shifted-moving-center-pade-worldline-law [BRIDGE], mass-shifted-pade-carathéodory-boundary-
  resolution-law — no Lean claimed; generic rational/Carathéodory identities.
- Hard-edge family (all gated on literal hard-edge Paley–Wiener compactification):
  mass-shifted-hard-edge-paley-wiener-compactification (root of the tree; needs Chebyshev–Cayley
  evaluation, Poisson summation tail on Xi strip, divisor limit, Gaussian witness truncation),
  mass-shifted-completed-source-hard-edge-compactness, mass-shifted-hard-edge-hyperbolic-weil-
  boundary, mass-shifted-hard-edge-root-jet-radical-rigidity, mass-shifted-hard-edge-parity-jet-
  inertia, mass-shifted-hard-edge-super-apex-hausdorff-inertia, mass-shifted-hard-edge-gauss-node-
  jet-residue-law, mass-shifted-hard-edge-hyperbolic-source-capacity.
  Order of attack if attempted: paley-wiener first (everything depends on it).
- hedenmalm-finite-source-port-obstruction, hedenmalm-root-flux-modular-charge-faithfulness —
  "exact Lean theorem and axiom/lint gates" open; check what exact statements need.

## Promoted this session additionally (see card statuses)
- route-r-reciprocal-log-fisher-half-density-entrance-wall (with new Sieve/PrimeLogPowerTail.lean)
- rank-two-commutator-parity-multiplicity-balance
- hedenmalm-root-flux-modular-charge-faithfulness
Total promoted 2026-08-13: 10 cards; 28 top-level stage-2 cards remain.

## Active card: route-e-whole-anchor-capacity-displacement-conservation-law (task 8)
STATE 2026-08-13 end of session: steps 1–2 of the plan below are COMPLETE, wired, built, audited:
- Sieve/AlmostPrimeGlobalCount.lean: primePiCount + exists_primePiCount_le (effective Chebyshev),
  mertensUpperConst + mertensS_le_logLog_add, squarefreeOmegaCount k, minFac_pow_le_of_squarefree,
  primeFactors_card_div_minFac, squarefreeOmegaCount_succ_le,
  exists_squarefreeOmegaCount_{one,two,three}_bound (Hardy–Ramanujan (10)).
- MobiusWholeAnchorGlobalTerminalCapacity.lean: wholeAnchorBandPrimes,
  wholeAnchorTerminalUniverse, card_window_fixed_label_le,
  wholeAnchorTerminalUniverse_card_le_sum ((11)/(12) split), log_natDiv_ge_of_sq_le,
  logLog_sub_le_mertensS, sum_one_div_bandPrimes, mertensBandProductConst,
  bandPrimes_eulerProduct_le ((13)), exists_wholeAnchorTerminalUniverse_card_le ((12)→(2)
  Euler form), exists_wholeAnchorTerminalUniverse_card_le_theta ((2)/(14) θ form).
REMAINING for promotion (step 3): (a) o(1) sequence corollary (3) via squeeze from θ form;
(b) kernel composition corollary: P.exists_average_le_column (FiniteRowStochasticKernel in
MobiusReciprocalAllocationJacobian.lean:179, Target := ↥(wholeAnchorTerminalUniverse ...),
Fintype.card_coe) chained with the θ bound → column ≥ #Anchor/(C·θ·b);
(c) proposed-band (5)/(6): hypotheses exp(√(logLog b)) ≤ log W and log Z·(logLog b)² ≤ log b
give card ≤ C·b·exp(−√(logLog b)) (needs logLog b ≥ 1 from b ≥ 16 via log 2 > 0.693 bounds);
then update card + git mv to 3-formalized.
Finite core done in RHTower/MobiusWholeAnchorCapacityDisplacement.lean (reservoir band, E3
packet, powerset mass = Euler product `wholeAnchor_fullReservoirMass_eq_eulerProduct`,
row-stochastic (4)/(9)). Remaining plan:
1. NEW Sieve/AlmostPrimeGlobalCount.lean:
   - primePiCount N := ((range (N+1)).filter Prime).card; ∃C ∀N≥2 effective Chebyshev from
     BrunTitchmarsh.card_range_filter_prime_isBigO (finite small-N max absorb).
   - E_k sets: (Icc 1 N).filter (Squarefree ∧ primeFactors.card = k), k = 2, 3.
   - minFac decomposition: squarefree ω=k ⇒ minFac^k ≤ m; m ↦ (minFac, m/minFac) into
     biUnion over {p prime : p*p*p ≤ N} (avoids real cube roots; ∑ 1/p ≤ mertensS N);
     coprime split via Nat.Coprime.primeFactors_mul; card_biUnion_le.
   - Mertens upper: mertensS N ≤ Sieve.logLog N + K, K := meisselMertensConst +
     (2*mertensFirstConst + 1/2)/Real.log 2, from abs_mertensS_sub_logLog_sub_const_le.
   - E₂(N) ≤ C N (logLog N + K)/log N; E₃(N) ≤ C' N (logLog N + K)²/log N (∃C ∀N≥2 form,
     small N crude count ≤ N; log(N/p ℕdiv) lower bound via p³ ≤ N ⇒ N/p ≥ N^{2/3}).
2. Extend/sibling module for the card: terminal universe def (⋃_{R ⊆ band} t_R·E₃ ∩ [cX,CX]),
   (11) per-t window count from E₃ bound, (12) ≤ ∑_powerset 1/t_R · bound = Euler product ·
   bound, (13) ∏_{W<p≤Z}(1+1/p) ≤ (log Z/log W)·e^{K'} via log(1+u)≤u + sharp Mertens both
   ends, (14)/(2) assembly, (3) o(1) corollary, (5)/(6) specialization.
3. Wire, audit, promote card.

## Working discipline reminders
- 6 concurrent peer sessions in this repo; check mtimes/git status before touching any module.
- lake build <module> is authoritative; lake env lean is necessary not sufficient.
- Axiom audit via scratchpad file (NOT /tmp per session scratchpad rule).
- Baseline axioms: [propext, Classical.choice, Quot.sound].
