# Claim trace — The geometry and complexity of quantum recurrence

Status: Stage 1 manuscript assembly. This file distinguishes manuscript synthesis from mathematical proof status.

## Framework

| Manuscript item | Status | Exact source |
|---|---|---|
| Haar-on-the-hull occupation | `[BRIDGE]` | Kronecker--Weyl / unique ergodicity; proved in manuscript Appendix A |
| Finite target-capacity union bound | `[BRIDGE]` | Elementary Haar union bound; proved in manuscript Appendix A |
| Four-law synthesis | `[NOVELTY UNVERIFIED]` | New manuscript organization; not standalone mathematical novelty |

## Law I — persistence

| Claim | Status | Source |
|---|---|---|
| Finite contraction peripheral-carrier selection | `[LEAN-PROVED]` | Prior manuscript proof; formal recurrence carrier modules in `formal/GaloisForLFunctions/RHTower/` |
| Arbitrary stationary spectral collision hierarchy | `[LEAN-PROVED]` | Prior manuscript and imported appendices |
| Countable pure-point recurrence / atomless zero-density boundary | `[LEAN-PROVED]` | Prior manuscript and imported appendices |

## Law II — interaction and factorization

| Claim | Status | Exact source |
|---|---|---|
| `tau(H)=sum_C(D_C-1)` for generic arbitrary finite graph-local Hamiltonians | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/3-formalized/arbitrary-graph-quantum-temporal-curvature-law.md`; arbitrary-graph spectral factorization modules under `formal/GaloisForLFunctions/HTGeometry/` |
| Interaction multiplication `Delta tau=(A-1)(B-1)` | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | Same card; `temporalRank_merge_components`, `temporalRank_merge_gain` |
| Pair temporal curvature reconstructs supplied interaction graph | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | Same card; `adj_iff_pairTemporalCurvature_pos` |
| Partition-curvature factorization lattice | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | Same card and formal component-partition layer |
| Anchored chordal return density | `[LEAN-PROVED]` | `HTGeometry/ConnectedNetworkRecurrenceLaw.lean`; `anchoredProjectiveReturnFrequency_of_connected` |
| Connected-network thermodynamic rate | `[LEAN-PROVED]` for homogeneous finite-volume theorem; heterogeneous graph corollary `[PAPER-PROVED]` | `HTGeometry/ThermodynamicProjectiveRecurrenceExtinctionLaw.lean`; algebraic extension proved in manuscript |
| One-network thermodynamic exhaustion | `[LEAN-PROVED]` | `HTGeometry/InfiniteNetworkExhaustion.lean`; `networkExhaustionGoodSet_residual`, `measure_compl_networkExhaustionGoodSet_eq_zero`, `infiniteNetworkExhaustion_temporalRank_tendsto_atTop` |
| Component recurrence torus | `[LEAN-PROVED] [BRIDGE]` | `docs/drafts/pipeline/3-formalized/component-recurrence-torus-and-replica-factorization-law.md`; `HTGeometry/ComponentRecurrenceTorus.lean` |
| All-order component histogram collision law | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | Same card; `HTGeometry/ComponentSpectralFormFactorProduct.lean` |
| Fixed-component product-exponential limit | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | Same card; `HTGeometry/ComponentFormFactorExponentialLimit.lean` |

## Law III — target capacity and complexity

| Claim | Status | Exact source |
|---|---|---|
| Reverse-water target information and recurrence deadline | `[LEAN-PROVED]` | Prior manuscript and imported appendices |
| Observer coherence graph and visible capacity | `[LEAN-PROVED]` | Prior manuscript and imported appendices |
| Eigenbasis-free Choi target tube bound | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/3-formalized/universal-static-choi-complexity-plateau.md` |
| Static connected graph-local completed-time Choi plateau | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` composition | Arbitrary-graph theorem + Choi tube theorem + unique ergodicity. Exact composition proved in manuscript; not yet one Lean declaration |
| Local circuit heap count | `[LEAN-PROVED] [BRIDGE]` | `docs/drafts/pipeline/3-formalized/local-circuit-trace-capacity-law.md`; `RHTower/LocalCircuitTraceCapacity.lean`; trace-monoid mechanism classical |
| Linear-`D` completed-time heap plateau | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | Same card composed with Choi cap; not yet formalized |
| Fixed-product-state quenched plateau on Gaussian nearest-neighbour chains | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/2-fully-proven/local-clifford-return-excised-phase-incidence-law.md`; direct target-cap proof reproduced in manuscript |
| Common deterministic hard-time subsequence | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/2-fully-proven/computable-static-local-exponential-state-complexity-law.md`; Fatou--Tonelli composition reproduced in manuscript |
| Rational uniformly computable static-local hard witnesses | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | Same card; continuity, rational-density and dovetailed certification proof reproduced in manuscript |
| Prime-torsion arbitrary-ray avoidance | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/3-formalized/prime-torsion-circuit-ray-polygon-law.md`; `RHTower/PrimeTorsionCircuitRayPolygon.lean` |
| Syndetic autonomous hard polygon plus return | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/3-formalized/prime-torsion-autonomous-circuit-polygon-law.md`; `RHTower/PrimeTorsionAutonomousCircuitPolygon.lean` |
| Ordinary Pauli-local hard polygon | `[LEAN-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/3-formalized/pauli-local-prime-torsion-circuit-polygon-law.md`; `RHTower/PauliLocalPrimeTorsionCircuitPolygonLaw.lean` |
| Permanent two-query Haar separator | `[LEAN-PROVED] [LITERATURE]` | Exact port of Cui--Schuster--Mao--Huang--Brandao; `docs/drafts/pipeline/3-formalized/traceless-local-two-query-haar-separation-law.md` |

## Law IV — reflection and recovery

| Claim | Status | Exact source |
|---|---|---|
| Autonomous robust complexity palindrome | `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/2-fully-proven/autonomous-return-complexity-reflection-law.md`; Lean deferred |
| Exact-length shell / partition-function reflection | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | Same card; Lean deferred |
| Markovian simultaneous recovery and distinguishability bound | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/2-fully-proven/markovian-return-recovery-complexity-reflection-law.md`; Lean deferred |
| Exact full-channel recurrence forces unitary semigroup | `[LITERATURE] [BRIDGE]` | CPTP inverse classification plus semigroup law; Nayak--Sen cited |

## Information boundary

| Claim | Status | Source |
|---|---|---|
| Complete finite-record ambiguity | `[LEAN-PROVED]` | Prior manuscript and imported appendices |
| Sharp moment-support threshold and minimax `1/2` | `[LEAN-PROVED]` | Prior manuscript and imported appendices |
| Onset--recurrence dimension independence | `[PAPER-PROVED] [NOVELTY UNVERIFIED]` | `docs/drafts/pipeline/2-fully-proven/onset-recurrence-dimension-independence-law.md` |

## Forbidden manuscript claims

- No optimally recentered projective operator-norm density formula; proved formula is anchored chordal.
- No infinite-volume recurrence or interchange of limits.
- No quantitative first-return time from completed density.
- No first-onset, monotonicity, Brown ramp or Brown recurrence scale.
- No Brown-scale circuit dictionary in prime-polygon theorem.
- No Haar/design randomization by constant-local static dynamics.
- No derivation of physical space without supplied subsystem decomposition.
- No recovery conclusion from recurrence of one state; Markovian theorem requires full-channel return.
