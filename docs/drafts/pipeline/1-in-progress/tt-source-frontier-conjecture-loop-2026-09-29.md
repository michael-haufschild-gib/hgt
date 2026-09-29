# TT source frontier conjecture loop

- **ID:** tt-source-frontier-2026-09-29
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/rh-current-frontier-map.md, route TT
- **Statement:** Find and prove an unconditional new source theorem advancing signed integrated covariance or directed natural-square-root-window means.

## Goal

Contribute a significant Lean theorem toward proof or falsification of RH. A receiver reformulation does not discharge its source premise. Public-source searches can establish absence from inspected sources, not absence from all public literature or inaccessible training data.

## Plan

1. Audit TT frontier, relevant memories and exhaustive source search.
2. Freeze exact conjecture and write dependency-closed proof or failure mechanism.
3. Audit corpus overlap and public sources; iterate after failures or redundant results.
4. Formalize qualifying result, audit leaf with `lake env lean`, inspect axioms, wire umbrella, lint and clean scratch artifacts.

## Constraints

Unconditional capstone; no new axioms, analytic premises, numerical experiments, heartbeat increases, full builds or umbrella builds. One owned foreground Lean process at a time. Preserve unrelated working-tree edits. Use `--old` for necessary named incremental builds.

## Log

- 2026-09-29 — Initialized. TT has T1 signed centered nonlocal covariance and T2 directed natural-square-root-window source laws open. Existing positive stationary cone growth is unconditional but not centered-current control. Prior theta-tail signature work belongs to a different source-sign lane and supplies no TT producer.
- 2026-09-29 — Serena memory/manual read. `docs/architecture.md` and `docs/testing.md` absent. `update_plan` and `multi_tool_use.parallel` unavailable; plan persisted here and independent reads batched using `Promise.allSettled`.

## Conjectures

### C1 — stationary prime–vacuum cancellation

Candidate: centered complete stationary covariance is `o(X)` at moving cutoff `X`.
Rejected as a qualifying contribution: coarse PNT consequence with no critical-scale source control. No code promoted.

### C2 — exact half-density endpoint energy

Frozen before proof: `¬ WoldNatResidualSquareEnergy (1/2)`, equivalently the actual residual `R_N` is not square summable. Corpus has the strict result only for `t>1/2`.

Proof idea: square summability would make the natural Abel continuation holomorphic on the open translated critical half-plane. Cauchy–Schwarz bounds its radial value at `s0+x` by `O(x^(-1/2))`, so `x A(s0+x)→0`. Corpus forces a nonzero negative-integer residue at an unconditional Hardy zero, contradiction. Endpoint harmonic dual divergence therefore does not protect the energy producer.

Potential positive survivor: radial pole gives an explicit unavoidable critical energy charge; finite or summable polar repairs cannot erase all critical frequencies. Audit exact strength and overlap before promotion.

### C3 — logarithmically damped critical energy

Frozen stronger candidate: even `sum R_N^2 / (1+log N)` diverges. The dual kernel has squared norm `O(x^(-2))`; finite-head/tail splitting of a hypothetical summable energy then gives `x A(s0+x)→0`, contradicting the same quantized residue. This would identify the borderline logarithmic repair, rather than merely remove strict-power slack. Not yet paper-proved or formalized.

## Paper proof for C2

`[PROVED HERE]` Suppose `Q=sum |R_(N+1)|^2<infinity`. For `Re s>-1/2`, the complex-power unit-step estimate bounds the Abel atom by `|s||R_(N+1)|(N+1)^(-Re s-1)`. The squared dual series converges; on each interior ball its lower real abscissa supplies a common summable Cauchy–Schwarz majorant. Thus the Abel sum is holomorphic there. On `Re s>0`, the existing exact natural-cutoff partial-sum identity and telescope identify `A(s)+C` with the natural Abel germ.

For `s=s0+x`, `Re s0=-1/2`, `0<x<1/4`, Cauchy–Schwarz and the unit-step real-power tail bound give `|A(s)|^2 <= |s|^2 Q (1+1/(2x))`. Therefore `|x A(s)|^2 <= |s|^2 Q (x^2+x/2)→0`; the constant holonomy also has zero scaled radial limit. The forced critical-wall residue theorem supplies `x(A(s)+C)→-m`, `m>=1`, at one unconditional Hardy zero, contradiction. No RH premise or numerical calculation enters.

## Novelty and validation

Pending.

- 2026-09-29 — Lexical endpoint search returns existing strict `not_woldNatResidualSquareEnergy_of_half_lt`; exhaustive Wold source text has no endpoint or natural logarithmically damped counterpart. Deep Abel/L2 search is partial after deadline; its inspected candidates contain the forced wall residue and no endpoint result. Compiler freshness must still be supplied by named checks.
- 2026-09-29 — Generic Lean scratch checks Abel atom bound, shifted real-power square summability, Young majorant, finite-to-infinite Cauchy–Schwarz, and harmonic dual bound. Completing local holomorphy and radial residue annihilation; no tree proof promoted yet.
- 2026-09-29 — Public audit: Zhao, “On the mean values of the error terms in Mertens’ theorems” (2025), https://link.springer.com/article/10.1007/s40993-025-00640-y, studies classical E1/E2/E3. Lemma 9 gives E2 mean-square upper bounds; inspected results do not state the exact natural Wold endpoint. This is limited negative search evidence, not a global novelty certificate.

### C4 — quantized critical prefix-energy loading

Frozen positive-survivor candidate: an unconditional wall zero with multiplicity `m` and coordinate `s0=rho-1` forces nonzero logarithmic loading of the natural prefix square energy. More precisely, if a tail bound `E(N) <= c log N + O(1)` existed, the Abel residue would force `c >= m^2 / |s0|^2`. A real-source/reflected-frequency refinement may improve that constant; that stronger factor is a new conjecture, not asserted.

Paper mechanism to audit: split the radial exponent equally between source and dual in Cauchy–Schwarz, rather than use the unsplittable endpoint dual. Partial summation of the prefix-energy bound gives discounted source energy `O(c/x)`, while the dual is `O(1/x)`. The forced quantized residue then bounds `c` below. This extracts positive unavoidable source loading; a bare negation or generic Hilbert lemma will not close the no-go card.

- 2026-09-29 — C2 unconditional capstone accepted by `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalSquareEnergyEndpoint.lean` (exit 0). Wired that leaf additively into RHTower. Named `lake build --old` and scratch axiom audit pending. This closes strict/equality gap, but novelty and positive-salvage bar remain open; goal not complete.

- 2026-09-29 — Named `lake build --old GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyEndpoint` passed, leaf build 8.8s. No umbrella or full build run. Global `scripts/formal_tools.py lint` exit 1: 13 unrelated unreachable modules (CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, FermiNymanLogarithmicWitness, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellBoundaryLayer, ThetaMovingShellFourierJet, WeilPolarConeFirstVariation, ZetaZeroDensityPowerSaving). New endpoint leaf is wired and not named in errors. No unrelated modules edited to resolve others’ wiring.
