# Directed prime--Gamma passive-completion parity no-go

- **ID:** C1-KMS-DIRECTED-NOGO
- **Stage:** 2-fully-proven
- **Type:** FALSIFIED
- **Source:** C1 prime--Gamma passive-response lane
- **Statement:** Neither canonical directed prime-log finite KMS responses nor canonical directed
  Gamma-sewn Stokes truncations can converge to the completed prime--Gamma response, already at
  centered point `I / 4`.

## Goal
Hostile-test first source-only finite-KMS candidate before adding Gamma or completion machinery.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper

## Approach
At `z = I / 4`, every directed prime-log resolvent atom has positive real part, so the negative
finite KMS response converges to a limit with strictly negative real part. Every directed
Gamma-sewn one-subtracted Stokes atom also has strictly positive real part; absolute summability
therefore gives a limit with strictly positive real part. Reflection-oddness of the completed Xi
source forces its real part to vanish at the same point. Hausdorff uniqueness of limits excludes
both comparisons with the completed source.

## No-go closure
- **Exact killing theorem/mechanism:** both directed carriers violate centered reflection parity
  before any sign question; this remains true for the physical Gamma-sewn Stokes source despite
  unconditional finite passivity.
- **Strongest positive survivor:** reflected/Hermitian completion is necessary before the
  thermodynamic limit. Existing reflected Stokes carrier is therefore the minimal surviving
  source-native class; its exact completed-Gamma comparison remains open.
- **New insight:** finite passivity is not enough. Candidate approximants must preserve
  completed-source oddness at each limiting comparison point.
- **Status:** `[PAPER-PROVED]`; all dependencies are existing Lean theorems plus elementary
  resolvent algebra. Lean formalization pending final audit.

## Log
- 2026-08-18 — created in Stage 1 after Lean-corpus audit.
- 2026-08-18 — `[PAPER-PROVED]`; promoted to Stage 2.
- 2026-08-18 — second hostile loop extends obstruction to physical Gamma-sewn Stokes truncations;
  finite-stage passivity survives exactly.
