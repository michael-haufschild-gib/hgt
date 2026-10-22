# Natural Wold square energy: exact cofinal subhalf criterion

- **ID:** tt-natural-subhalf-energy-criterion-2026-09-29
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean verification in progress
- **Source:** docs/reports/rh-current-frontier-map.md, route TT/T2
- **Statement:** `RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → t < 1/2 → WoldNatResidualSquareEnergy t`.

## Goal

Identify viable natural-mesh energy producer boundary after unconditional exclusion of critical
square energy. Closed equivalence has no external premise; it supplies a criterion, not an
unconditional source-energy estimate or an RH proof.

## Gates

- [x] 0 → 1: source-pure statement and dependency-closed attack.
- [x] 1 → 2: paper proof below; all mathematical dependencies already formalized.
- [ ] 2 → 3: named incremental build, exact direct Lean audit, scratch axiom audit.
- [ ] 3 → 4: external novelty audit and standalone paper.

## Corpus audit

Root's lexical audit `/tmp/hgt-tt-subhalf-energy-search.json` and deep audit
`/tmp/hgt-tt-subhalf-energy-deep.json` reviewed. Deep inventory complete (62,963 files), retrieval
partial; compiler snapshots mostly pending or stale. Returned statements include older
cofinal-three-quarter receiver, square-energy-to-power-spectrum transfer with quarter loss,
natural zero-width pointwise spectrum equivalence, and exact canonical singular-divisor
tomography. No inspected statement provides this exact cofinal-half energy equivalence.
This bounded audit does not certify absence from public literature or inaccessible training data.

## Dependency-closed paper proof

Write `R(N) = xiHeatCassiniWoldNatResidualLogDiscrepancy N` and
`E(t) = ∑ N^(2t-1)|R(N)|²`.

**RH implies every strict subhalf energy.** Existing exact pointwise natural spectrum gives
`|R(N)| ≤ B N^(-c)` eventually for every `0<c<1/2`. For fixed `0<t<1/2`, choose
`c=(t+1/2)/2`, so `t<c<1/2`. Energy terms are bounded eventually by
`B² N^(2t-1-2c)`; exponent is strictly less than `-1`, hence summable.

**Cofinal subhalf energies imply RH.** From `E(t)<∞`, Cauchy–Schwarz gives
`∑ |R(n+1)|(n+1)^q <∞` whenever `q<t-1`. For every `q<-1/2`, choose positive
`t<1/2` with `q<t-1`. The resulting weighted absolute spectrum gives local normal
convergence and holomorphy of the literal natural Abel increment current throughout
`Re s>-1/2, Im s>0`. Add the exact log-holonomy constant to recover the literal Abel
germ on `Re s>0`. Existing zeta-cleared identity extends this germ across the sector.
If RH fails, corpus theorem supplies a zero `rho` with `1/2<Re rho<1`; conjugation
selects positive imaginary part. Canonical continuation has residue `-m`, `m≥1`,
at `s0=rho-1`. Isolated-zero nonvanishing identifies canonical continuation with the
holomorphic constructed current along a positive real punctured approach. Holomorphy
forces scaled residue zero, contradicting `m≥1`.

## Plan

1. Copy root's read-only scratch draft to owned scratch and repair elaboration issues.
2. Promote verified proof to assigned new module; optimize without heartbeat changes.
3. Run one foreground named `lake build --old`, exact direct audit, and scratch axiom audit.
4. Report proof and verification to root for spot-check and umbrella wiring.

## Log

- 2026-09-29 — Initialized assigned proof task. Existing endpoint/log-critical exclusions do not
  discharge this criterion's source-energy family. Overall RH goal remains active.
- 2026-09-29 — First owned scratch audit failed on notation/reduction: `conj` was unavailable
  (replaced with source-verified `starRingEnd ℂ`); sector definition uses `-(1/2)` rather than
  definitionally different `-1/2`; punctured residue and eventual equality needed explicit
  composition reduction. Both weighted-summability and forward-energy proofs elaborated.
  Corrected scratch audit running; no theorem assumption or heartbeat changes.
