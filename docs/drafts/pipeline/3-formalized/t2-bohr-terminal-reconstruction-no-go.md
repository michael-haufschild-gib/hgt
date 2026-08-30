# T2 Bohr-to-terminal reconstruction no-go on the ordered-prime clock

- **ID:** T2-B2-TERMINAL-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · Route T2 positive-ray joint-current landing
- **Statement:** On the literal ordered-prime logarithmic clock there is a residual tending to zero whose positive-height Abel increments are square-summable and whose finite exponential currents are Bohr-Cauchy, while its positive-height terminal diverges to infinity.

## Goal
Kill the T2 branch

`positive-ray joint current Bohr-Cauchy -> Hilbert/closed-graph reconstruction of the Borel terminal -> strict-subhalf finite landing -> RH`.

The theorem retains the exact three ingredients available after the current T2 frontier theorem: ordered-prime frequencies, increment coefficients at height `1/10`, and the boundary condition that the residual itself tends to zero. The counterexample proves that no topology-only or closed-graph argument from those data can discharge the terminal. Any surviving T2 proof must use an additional Wold-specific arithmetic norm or identity.

## Gates
- [x] 0 → 1 in-progress: well-posed; literal prime clock; exact proof-chain target; corpus and literature audit completed
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `not_T2PrimeClockBohrTerminalLandingPrinciple`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Paper proof — [PROVED HERE]
Write `h_N = log p_N`, `g_N = h_(N+1)-h_N`, and

`r_N = exp(-h_N/20)`.

Since `h_N -> +∞`, `r_N -> 0`. At positive height `1/10`, define the exact Abel increment

`c_N = (r_(N+1)-r_N) exp(h_(N+1)/10)`.

Monotonicity gives `g_N >= 0`, and

`|r_(N+1)-r_N| = exp(-h_N/20) (1-exp(-g_N/20)) <= g_N/20`,

using `1-exp(-u) <= u` for `u >= 0` and `exp(-h_N/20) <= 1`. Hence

`|c_N|^2 <= (1/400) g_N^2 exp(h_(N+1)/5)`.

The right side is summable by the corpus positive-height prime-gap theorem
`summable_xiHeatCassiniOrderedPrimeLogGap_sq_mul_positiveFifthHeight`; therefore `c ∈ ell^2`.
Distinct ordered-prime log frequencies and finite exponential Parseval give the exact Cesaro
mean-square identity for every finite tail. The `ell^2` tail criterion makes the finite currents
Bohr-Cauchy.

But the literal terminal is

`|r_N| exp(h_N/10) = exp(h_N/20) -> +∞`.

Thus vanishing of the primitive and Bohr-Cauchy cofinality of its exact positive-height Abel
increment current do not imply terminal vanishing. This contradicts the proposed universal
reconstruction principle and closes the no-go. ∎

## Corpus and literature audit
- Corpus searches for exact weighted-increment/terminal counterexamples, Bohr-terminal reconstruction, and residual-to-terminal implications found no theorem with the ordered-prime clock plus `r_N -> 0`.
- Existing corpus no-go theorems only rule out generic bounded point evaluation on `ell^2`/finite Sobolev profiles; they do not retain exact Abel increments or a vanishing primitive.
- Hedenmalm--Lindqvist--Seip and later Hilbert-space Dirichlet-series work locate bounded `ell^2` point evaluation beyond the half-density line. Weighted discrete Hardy literature classifies related abstract Hardy operators, but the audit found no exact ordered-prime Abel-current counterexample or T2 consequence.
- Novelty claim is project-specific: exact literal-prime current, exact positive-ray terminal, and direct RH-chain obstruction. General Hardy-operator ancestry is acknowledged.

## No-go closure
- **Exact killing theorem/mechanism:** `not_T2PrimeClockBohrTerminalLandingPrinciple`. A vanishing primitive has a square-summable exact positive-height increment current satisfying finite Parseval and Bohr cofinality, but its terminal tends to infinity.
- **Strongest positive survivor:** `t2BohrTerminalCounterAbsTerminal_tendsto_atTop` together with `t2BohrTerminalCounterCurrent_bohrCauchy`: exact terminal escape and exact Bohr cofinality coexist on the same literal prime clock. This is stronger than a generic discontinuity statement and identifies an unstable boundary mode invisible to `B^2`.
- **New insight:** more Bohr smoothness cannot close T2. Surviving proof chain is now
  `joint Bohr current + Wold-specific terminal-controlling arithmetic norm/identity -> terminal disappearance -> strict-subhalf landing -> RH`.
- **Status:** dependency-closed paper proof and Lean formalization in `XiHeatCassiniWoldPositiveTenthBohrTerminalNoGo.lean`; direct Lean PASS; targeted module build PASS; axiom audit only `[propext, Classical.choice, Quot.sound]`; umbrella wired. Global lint failure is pre-existing and unrelated (unreachable modules plus `HTGeometry/CompositionJetField.lean:167` proof debt); new module is reachable and introduced no lint finding.

## Lean certificate
- Module: `GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthBohrTerminalNoGo`
- Principal theorem: `RHTower.not_T2PrimeClockBohrTerminalLandingPrinciple`
- Witness laws:
  - `t2BohrTerminalCounterResidual_tendsto_zero`
  - `summable_norm_sq_t2BohrTerminalCounterCoefficient`
  - `tendsto_t2BohrTerminalCounterCurrent_tail_cesaro_normSq`
  - `t2BohrTerminalCounterCurrent_bohrCauchy`
  - `t2BohrTerminalCounterAbsTerminal_tendsto_atTop`
- Verification: `lake env lean` PASS; targeted `lake build` PASS; `#print axioms` standard foundations only.

## Log
- 2026-08-29 — created directly in 1-in-progress after corpus/literature audit and proof-chain freeze.
- 2026-08-29 — paper proof completed; promoted through Stage 2.
- 2026-08-29 — formalized, audited, umbrella-wired; promoted to Stage 3.
