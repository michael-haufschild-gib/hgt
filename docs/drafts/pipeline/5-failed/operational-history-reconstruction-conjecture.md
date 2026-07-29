# Operational history-reconstruction conjecture

- **ID:** `operational-history-reconstruction-conjecture`
- **Stage:** 5-failed
- **Type:** FALSIFIED; EXACT GAUGE SURVIVOR FORMALIZED
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/OperationalHistorySimilarityGauge.lean`
- **Source:** `../1-in-progress/observer-dependent-temporal-dimension.md`
- **Statement:** Equality of every finite labelled conditional-probability
  history determines an internal clock uniquely up to clock origin and the
  action-fixed commutant.

## Goal

Upgrade an algebraic clock stabilizer into an operational theorem valid for
continuous clocks and local type-III observable algebras.

## Gates

- [x] 0 → 1 in-progress: proof-route-blind conjecture frozen with hard
      falsifiers
- [ ] 1 → 2 fully-proven: failed by universal similarity gauge
- [ ] 2 → 3 formalized: false statement not applicable; exact no-go
      survivor formalized
- [ ] 3 → 4 publication-ready: retired as novelty route

## Approach

Test whether complete sequential probabilities imply the multiplier and
shift covariance premises of the algebraic stabilizer. Audit gate-set
tomography, quantum-process tomography, hidden-realization identifiability,
antiunitary symmetries, and type-III representation freedom before attempting
the continuous reconstruction bridge.

## No-go closure

- **Exact killing theorem/mechanism:** For every invertible linear
  realization change \(S\), transform state, instruments, and reports by
  \(\rho\mapsto S\rho\),
  \(\Phi_a\mapsto S\Phi_aS^{-1}\), and
  \(r\mapsto rS^{-1}\). Every scalar report of every finite labelled word is
  unchanged by telescoping cancellation. Global matrix transposition gives a
  quantum-compatible antiunitary/Jordan instance: it preserves density
  matrices, POVM effects, and Kraus-form complete positivity while lying
  outside multiplicative inner automorphisms in dimension at least two.
- **Strongest positive survivor:** Complete linear operational histories
  determine at most a simultaneous-similarity class. This is exact for
  arbitrary state-space dimension, arbitrary label and reporter types, and
  every finite history length. A clock-uniqueness theorem needs external
  calibration that reduces this similarity gauge before its
  origin/commutant stabilizer can apply.
- **New insight:** “Tomographically complete” does not eliminate
  representation gauge; it only separates points after a representation has
  been chosen. Internal histories cannot themselves supply that missing
  anchor.
- **Status:** Universal finite-history identity, a two-dimensional proof
  that transposition is nonmultiplicative, preservation of finite Kraus
  form, density-matrix and POVM-effect conditions, and terminal Born reports
  are formalized in `OperationalHistorySimilarityGauge.lean` and
  direct-compiled clean.
  Nielsen et al., *Gate Set Tomography* (2021), treats the same common
  similarity as the fundamental GST gauge. Wigner-type theorems already
  classify probability-preserving state symmetries as unitary or
  antiunitary.

## Log

- 2026-07-28 — generated as fourth abductive jump with no route from all
  histories to multiplier covariance.
- 2026-07-28 — falsified by simultaneous similarity; physical transpose
  obstruction isolated; exact universal gauge law formalized.
