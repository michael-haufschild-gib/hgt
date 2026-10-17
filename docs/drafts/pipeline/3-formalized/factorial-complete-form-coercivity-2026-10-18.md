# Factorial complete-form coercivity

- **ID:** factorial-complete-form-coercivity-2026-10-18
- **Stage:** 3-formalized
- **Type:** CANDIDATE
- **Scope:** BiScaleUncertainty; WL/RW. Original goal remains unconditional RH in Lean.
- **Statement:** For each of the two actual balanced factorial sources, the complete real-space expression `gammaBracket 0 * h(0) + biScaleLevyEnergy - 2 * fullPairing h`, divided by `h(0)`, tends to positive infinity.

## Plan

1. Audit current source-local packet estimates and their dependencies by direct Lean checks.
2. Prove cutoff-free individual pairing bounds, then logarithmic coercivity of the complete real-space expression.
3. Audit the exact bridge to the spectral Weil functional for these Lipschitz sources; do not silently apply the smooth-test bridge.
4. Check axioms, leaf modules, umbrella wiring and formal lint. Continue toward the all-source sign problem; this family alone cannot prove RH.

`update_plan` is unavailable in this tool session; this card tracks the plan.

## Corpus evidence and preliminary attack

Read the BiScaleUncertainty README fully. WL/RW ledger and README remain read-only.
Hybrid corpus search `signed prime polar factorial packet` completed without errors or partial results; semantic completeness was unmeasured and most compiler metadata was pending/stale. Current source declarations, not index status, determine applicability. A second whole-corpus search `factorial source Weil coercivity` returned mostly unrelated factorial results. Exact source search found no existing family coercivity endpoint; this is not an external novelty claim.

Current local certificate states the finite-cutoff individual bound `pairing^2 <= 50000*h(0)^2`. Existing jump certificate gives
`J/h(0) >= (3/23)*exp(-1/2)*log(n+1) - (41+2*log(1000000))/6`.
These concern actual constructed sources, with no Chebyshev-error assumption.

**Preliminary verdict: BRIDGE.** Combining them can remove an unpaid pairing cost for this concrete family. It does not establish a lower bound for arbitrary sources, nor for arbitrary linear combinations of factorial sources. External/novelty audits are omitted under the user's explicit corpus-only instruction.

## Dependency-closed paper argument for the real-space expression

Put `N=n+1`, `delta=sourceFactorialWidth N`, `L=log(4*N+1)`, and `K=10*N`. Reflection of either balanced source is supported in `[-2*delta,L]`. The cutoff estimate gives `L+3*delta <= log(K+2)`. If `x >= log(K+2)`, then in every product `f(u)*f(u+x)`, either `u <= -2*delta` or `u+x >= L`; hence the autocorrelation is zero. Therefore `fullPairing h = pairing K h` exactly, with no limiting exchange.

Origin energy `R` is at least `6*sqrt(N)>0`. The local packet theorem gives `fullPairing(h)^2 <= 50000*R^2`; since `224^2>50000`, `|fullPairing(h)| <= 224*R`. Reflection preserves autocorrelation and jump energy, so this holds for each original source.

Write `Q=gammaBracket(0)*R+J-2*fullPairing(h)`. Division by `R>0` yields
`Q/R >= gammaBracket(0)+(3/23)*exp(-1/2)*log(N)-(41+2*log(1000000))/6-448`.
The coefficient of `log(N)` is strictly positive. Thus each normalized expression tends to positive infinity, and both are eventually strictly positive.

This proves the real-space statement using existing exact-source bounds. Their current Lean dependencies and the resulting theorem have now passed direct checks. Identification with the spectral `weilFullFunctional` on the Lipschitz sources requires the separate finite-jump argument below: the existing `RealWeilTestFn` identities require `ContDiff 2`.

## Paper argument for spectral identification

For any compact continuous real source `f`, its complexification belongs to both `L1` and `L2`. The existing `lintegral_archSymbol_mul_normSq_fourier` identifies the nonnegative spectral excess `2*(theta'(2*pi*xi)-theta'(0))*|Fourier(f)(xi)|^2` with the jump Dirichlet energy as an extended integral. The shift-square identity and `exp_half_div_sinh_eq` identify the latter with the physical jump integral. If that physical integrand is integrable, the extended integral is finite. Continuity of the spectral excess gives measurability, hence its integrability. Adding the integrable constant spectral term (Plancherel) gives integrability of the full symbol without source differentiability.

The existing spectral splitting identity then gives the Gamma term `gammaBracket(0)*h(0)+J`. The transform of a compact continuous autocorrelation is the squared source transform on the real line. At the two imaginary pole frequencies, direct exponential integration gives the whole-line integral of `2*h(x)*cosh(x/2)`; evenness makes this twice the positive-half-line polar pairing. Each prime atom is exactly twice `primeTerm h n`, and compact support makes the prime sequence finitely supported. Assembly proves the literal spectral Weil identity with the original von Mangoldt weights and both poles. Applying the already proved jump-domain certificate to the factorial sources removes the final domain premise.

No smoothing limit, derivative estimate, changed arithmetic source, or omitted boundary term is used. The spectral endpoint and its eighteen public supporting theorems have passed direct Lean checks and the axiom audit.

## Status

- Paper argument for real-space endpoint complete.
- Seven source-local dependencies passed direct `lake --old env lean` checks. Logs `/tmp/bsu-coercivity-SignedPrimePolar*.log`; the atomic-packet check returned exit 0 directly. Two dependency logs contain redundant-tactic warnings (packet envelope and local energy); concurrent source edits are preserved.
- All three new leaf modules passed direct checks: `FactorialCompleteFormCoercivity.lean` in session `18634`, and `CompactFiniteJumpWeilFormula.lean` / `FactorialWeilCoercivity.lean` in session `30245`. Both API probes also passed. All new modules are wired into the BiScaleUncertainty umbrella.
- Final spectral-bridge check and the axiom audit passed in session `58046`. Every one of the eighteen public theorems uses only `propext`, `Classical.choice`, and `Quot.sound`. Evidence: `/tmp/bsu-factorial-weil-axioms.log`; source hashes and exact audit coverage: `/tmp/bsu-factorial-weil-verification.json`. No own Lean process remains running.
- `scripts/formal_tools.py index` succeeded and regenerated the three formal index documents. `scripts/formal_tools.py lint --check-generated` exited 1 with exactly four unrelated missing-umbrella-import errors: `BalancedNodalStationaryAndPrimeShiftDecompositionProducer`, `SchurSquareCorrelation`, `SchurSquarePolarAmbiguity`, and `SeparatedCopySquareClassification`. Concurrent drafts were not changed or wired without verification. No forbidden-declaration errors were reported. Logs: `/tmp/bsu-factorial-weil-index.log`, `/tmp/bsu-factorial-weil-lint.log`. No umbrella build was run.
- All-source RW sign and WL one-sided deficit bound remain open.

## Next conjecture to attack after verification

Determine the complete Weil sign on the pure factorial-ramp direction and the full two-dimensional span with its narrow tent partner. The sum of the two balanced sources cancels the tent, so positivity of the two displayed vectors does not prove positivity of their span. The present logarithmic lower bound comes from the narrow tent; it cannot be assigned to the pure ramp without a new proof. A search for a factorial-ramp/Riemann-kernel identification found no directly applicable theorem; no such identification is assumed.

Follow-up corpus query `factorial ramp Mellin zeta` completed without errors or partial results, but supplied no direct ramp transform theorem; compiler coverage remained mostly pending/stale. Exact source search in the area's Weil/Mellin/Fourier-named modules found no ramp-transform occurrence. These searches do not establish absence from the whole corpus. The finite clamped-sum definition of `smoothFactorialLift` suggests deriving its transform first; no limiting zeta identity or sign is currently proved here.
