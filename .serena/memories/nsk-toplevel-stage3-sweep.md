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

## Working discipline reminders
- 6 concurrent peer sessions in this repo; check mtimes/git status before touching any module.
- lake build <module> is authoritative; lake env lean is necessary not sufficient.
- Axiom audit via scratchpad file (NOT /tmp per session scratchpad rule).
- Baseline axioms: [propext, Classical.choice, Quot.sound].
