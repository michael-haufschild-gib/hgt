# Census of the Wall

A map of every Lean module and draft to its **Door grade** (`00-charter-wall-and-door.md` §3–4). The
grade says where an item stands relative to the wall; the one-liner is the Door reason (usually Door-2:
*strip the new vocabulary — does a parent still prove it?*). Statement-level status — which conjectures
are theorems, what to work on next — is in `door/00-status.md`; the conjectures themselves are in
`door/`.

Grades: **NATIVE** · **CONJECTURE (native aim)** · **BRIDGE** (border) · **IMPORT** (classical,
reframed) · **EMBASSY** (metaphor) · **META** (index/charter).

**The field's content today.** Native **definitions** (the multi-`q` module, corank, difference-trdeg),
native **conjectures** (G1–G5 and their scaffolding), **bridge** results at the single-prime / finite /
function-field borders, and a Lean **ledger** of elementary facts that is the floor under the
conjectures. The reframed "continents" map where classical results sit relative to the borders. The
route to a **NATIVE** entry is the irreducible theorem (C5); the candidates are the difference-Hölder
statement (G1) and the corank dichotomy (G3), pending the Door-2 re-test
(`door/door-C5-irreducibility-and-door-2-retest.md`).

---

## A. Lean modules (`formal/GaloisForLFunctions/`)

Tier-A by design (the elementary border). Per-module detail: `docs/architecture.md`; indexed by which
conjecture each supports: `door/bucket-ledger-footholds.md`.

- **NATIVE** — none yet. The candidates are the §59/§60 difference-category theorems (G1/G3), which live
  in the drafts, not in Lean; the Door-2 re-test decides their grade.
- **BRIDGE (border stones).** `MultiQDifference` (one Euler factor's `q`-difference equation),
  `FlatConnection` (finite integrability + co-extension flatness), `Resonance` (corank lattices, `Λ=0`
  slices), `RankOneCohomology`, `HolonomyAbelian`.
- **CONJECTURE-scaffold (native aims, statement/skeleton level).** `DSSDeterminant`,
  `MultiplicityEstimate`, `SpectrumGenericity`, `FieldConjectures` (DSS / realization stated as `Prop`s,
  no axioms).
- **IMPORT (classical facts, formalized — the ledger floor).** `Core` (ℚ-LI of `{log p}`),
  `OrbitFreeness`, `EulerProduct` (the Euler-product firewall), `KoszulCohomology` / `EHKoszulDuality`,
  `SecularMoments` / `SecularNewton` / `MultisetNewton` / `MomentReconstruction`, `SpectralTorelli` /
  `PowerSumTorelli`, `SmoothNumbers`, `DiagonalCharacter`, `BoundaryModulus`, the Satake / λ-ring family
  (`SatakeTensor`, `SatakeInterval`, `ExteriorSatake`, `LocalFactorDuality`, `CompleteHomogeneous`,
  `AdamsOperations`, `SymPowerPlethysm`, `SatakeReality`, `SatakeSymPower`, `SatoTateMoment`),
  `WCoordinate` / `ArakelovW` / `SigmaOrbit` / `BerryKeating`, the carrier family (`CarrierPickKernel`,
  `CarrierCauchy`, `SecularHankel`, `KreinLangerInertia`, `MeasureCarrier`, `CayleySchur`),
  `MultiplierScaling`, `OscillatorAlgebra`, `ExteriorParity` / `FunctionalEquationParity`,
  `SuperzetaResolvent`, `ArchimedeanLane`.

The Lean tree is the elementary floor: classical and border facts, machine-checked, that the
conjectures build on.

## B. Drafts

**Active (`docs/drafts/`).**
- `00-core-vision` — the vision — **META**.
- `00-charter-wall-and-door` — the rules (§1 test, §2 wall, §3 door) — **META**.
- `00-foundations-native-objects-and-gatekeepers` — N1–N4 + G1–G5 — **FOUNDING** (native definitions +
  native conjectures).
- `00-manifest-wall-census` — this file — **META**.
- `door/` — the gatekeeper buckets (`G1`–`G5`), the door/C5 bucket, the cross-cutting buckets (A1/A2
  unification, time, the seam, function-field, realization, no-margin, sibling conjectures, ledger
  footholds), the status table (`00-status.md`), and the index (`00-index.md`).

**Development corpus (`docs/denied/`),** preserved as record and mined into `door/`:
- **FOUNDING / CONJECTURE (native definitions + aims).** `infinite-base-difference-galois-for-L-functions`
  (the founding draft), `hypertranscendental_galois_field_foundations`, `hypertranscendental_galois_program`,
  `multi-q-difference-galois-foundations`, `transcendence-theory-nonholonomic-functions` (G2),
  `dss-multiplicity-estimate-spectral-genericity`, `dss-across-the-period-nonperiod-divide`,
  `spectral-torelli-inverse-problem`, `difference-galois-cohomology`.
- **BRIDGE (border).** `geometric-rosetta-function-field-continent` (the function-field border, where
  G1–G5 are theorems).
- **IMPORT (classical results, reframed — the map of where they sit).** `automorphic-continent-rankin-selberg-ramanujan`,
  `dynamics-continent-lyapunov-avila-morales-ramis`, `secular-positivity-hierarchy`,
  `rh-byproduct-secular-hankel-overdetermination`, `spectral-functoriality-operations-calculus`,
  `superzeta-tower-resolution-B23`, `arakelov-height-of-zeros`, `absolute-zeta-archimedean-frobenius`,
  `the-archimedean-lane`, `the-shoreline-and-the-archimedean-lane`, `edge-value-transcendence-baker-wing`,
  `carrier-unifies-dss-and-rh-faces`, `prime-zero-period-comparison`,
  `period-comparison-primes-zeros-the-planet`, `seam-is-the-period-nonperiod-divide`,
  `moduli-prime-systems`, `wild-cells-B24-B27-adjudication`.
- **EMBASSY (metaphor / physical analogy, inspiration not mathematics).**
  `arithmetic-cosmology-causality-inflaton`, `arithmetic-cosmology-II-pt-symmetry-horizons-time-loops`,
  `time-emergence-scale-clock-wheeler-dewitt`, `rh-holographic-pseudorandom-boundary`,
  `speculative-proofs-grand-conjectures`.
- **META (indices / roadmaps).** `00-manuscript-outline`, `00-planetary-atlas`, `proven-core`,
  `formalization-queue`, `formalization-roadmap-finite-to-apex`.

---

When an item's grade changes — a conjecture becomes a theorem, the Door-2 re-test lands, a draft is
re-graded — update its line here and the matching row in `door/00-status.md`.
