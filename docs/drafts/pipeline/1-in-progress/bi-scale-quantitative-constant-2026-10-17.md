# Quantitative logarithmic-grid uncertainty constant

- Stage: 1-in-progress
- Type: CANDIDATE
- Date: 2026-10-17
- Scope: independent Bi-Scale Uncertainty theory; no RH objective.
- Brief: attachment `4aea9418-a6fa-4acd-95b8-ea3615aae6cf/pasted-text-1.txt`.
- Goal: 100 significant contributions toward sharp unconditional bounds for the normalized archimedean increment energy under finite logarithmic-grid zeros and hyperbolic polar neutrality. Do not count auxiliary lemmas as separate contributions.

## Plan and current evidence

1. [x] Read supplied brief and all 207 lines of field README; inspect existing foundation and folded-collar modules.
2. [x] Audit common-origin accounting across dyadic cosets; derive exact joint sphere relaxation and paper integrated bound.
3. [x] Audit whether polar neutrality gives a uniform quantitative gain without a common support bound: it does not; polar/nonpolar infima coincide on the full real continuous positive-definite finite-energy cone.
4. [ ] Write dependency-closed proofs; formalize significant new endpoints in the field directory; wire umbrella.
5. [ ] Finish package audits. Shared-origin leaf and its five endpoint axiom audits pass; polar/transport formalizations remain. Preserve concurrent work.

`update_plan` and `multi_tool_use.parallel` are not exposed in this session. This card tracks the plan; independent tool reads use awaited parallel promises. Serena symbol lookup rejects the ignored Lean source paths, so file reads are the available fallback. `docs/architecture.md` and `docs/testing.md` do not exist.

## Exact issues under investigation

Current formalization target: construct the actual source `f_T(u)=f(u)−exp(−T/2)f(u−T)`, prove its literal autocorrelation and polar identities, exact normalized local preservation, then quantitative energy convergence. This closes the concrete operation behind the paper infimum-invariance theorem; do not substitute an abstract assumed transfer map.

- Summing the one-chain origin-leverage bound over cosets spends the same origin energy repeatedly. A valid joint bound needs one shared origin coordinate.
- Candidate joint support function: with block constraints `u0² + ||u_m||² ≤ R²`, the maximum of `W0 u0 + Σ_m <w_m,u_m>` is `R sqrt(W0² + (Σ_m ||w_m||)²)`.
- Polar escape candidate: a distant exponentially small translated copy can enforce one exponential moment exactly while preserving all finite-grid zeros and changing normalized energy by a quantity tending to zero. If true, polar neutrality alone leaves the finite-grid infimum unchanged.
- README's final displayed deformation identity contains an extra constant term. Existing Lean identity is algebraically correct. Check sign interpretation beyond crossover before integrating.

## Contribution ledger

One significant paper-proved contribution package: quantitative polar enforcement and infimum invariance, including exact preservation on bounded windows for compact kernels, whole-cone taper extension, and an even-source-preserving variant. These are one package, not separate counter increments. Fully Lean-certified packages: zero until the polar package is formalized.

Shared-origin support law, equality witness, rational penalty, and literal dyadic-grid specialization are Lean-certified in `SharedOriginMultiCosetLeverage.lean`. Adjacent concurrent research independently found this support formula; count it as a shared bridge, not as separate novel knowledge. Existing foundation/folded-collar work also does not count toward this task's 100.

Authoritative facts/failures: `docs/reports/BiScaleUncertainty/WORKING-LEDGER.md`. Complete paper proofs and explicit N-dependent quadrature certificates: `docs/reports/BiScaleUncertainty/quantitative-constant.md`.

## Validation

Shared-origin module passed direct `lake --old env lean -o ... SharedOriginMultiCosetLeverage.lean`, exit 0 without diagnostics. Scratch audit of all five result endpoints passed; only `propext`, `Classical.choice`, `Quot.sound`. Module wired into umbrella. Index regeneration passed. Latest formal lint returned two errors: concurrent `OptimalOriginAllocation` and `OverlapSafeCollarMeasureTransport` were unreachable from their umbrella at that snapshot. No error named this task's module; global lint is not green. Previously unlinked `MultiChainToeplitzGramCoupling` is now wired.

No numerical experiments; no full or umbrella builds; no increased heartbeat limits; no commits. Goal remains active: globally sharp constants, full formalization, and the 100-contribution requirement are unfinished.
