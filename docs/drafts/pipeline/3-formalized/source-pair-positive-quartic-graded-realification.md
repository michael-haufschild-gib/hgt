# Source-pair positive quartic graded realification

- **ID:** `source-pair-positive-quartic-graded-realification`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** GTA (`ORIENT LAND COMP`)
- **Statement:** Every complex source pair `a ± ib` admits a finite real graded lift preserving signed power traces in degrees one and two whose quartic signed-trace anomaly is nonnegative and vanishes exactly when `b = 0`.

## Goal

Replace GTA's joint signed cubic/quartic reporter by one positive quartic orientation invariant. This would prevent cross-packet sign cancellation and reduce the source-orientation burden to vanishing of one nonnegative global supertrace, while retaining the already-classified need for coefficient-faithful Xi assembly.

## Gates

- [x] 0 → 1 in-progress: exact source-pair claim frozen; internal parent identified; hostile tests named
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PAPER-PROVED]`
- [x] 2 → 3 formalized: exact unconditional Lean theorem, targeted verification and axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, priority audit

## Internal frontier

- `[CORPUS]` `sourcePairRealGradedAnomaly_one` and `sourcePairRealGradedAnomaly_two` preserve degrees one and two for the canonical real graded lift.
- `[CORPUS]` `sourcePairRealGradedAnomaly_three` and `sourcePairRealGradedAnomaly_four` give signed defects `12ab²` and `4b²(6a²-b²)`.
- `[CORPUS]` `sourcePairRealGradedHigherTraceAnomaly_faithful` needs the cubic and quartic defects jointly: canonical quartic defect alone changes sign and has a nonreal zero cone.
- `[LOCAL-RESEARCH]` GTA retains higher-trace orientation after degree-one/two realification but lacks a source law immune to global cancellation.

## Frozen conjecture

`[CONJECTURE GTA-PQ4]` There are finite real even and odd node packets, defined uniformly from `(a,b)`, such that their signed power sums agree with the conjugate complex pair through degree two and their quartic signed-power defect is a nonnegative polynomial with zero set exactly `b = 0`.

Public sentence: nonreality can be moved into one positive fourth-order source charge without changing mass or quadratic energy.

## Complete paper proof

For `n ≥ 0`, write source-pair power trace

```text
S_n(a,b) = (a+ib)^n + (a-ib)^n.
```

Take real even nodes `a+7b,a-7b` and real odd nodes `5b,5b,-5b,-5b`. Define signed real graded trace

```text
G_n(a,b)
 = (a+7b)^n + (a-7b)^n
   - 2(5b)^n - 2(-5b)^n
```

and anomaly `A_n = G_n-S_n`.

Degree one is immediate: odd nodes cancel and both even/source pairs sum to `2a`, so `A_1=0`.

For degree two,

```text
G_2 = 2a² + 98b² - 100b² = 2a²-2b² = S_2.
```

The cancellation is the Pell identity `7²-2·5²=-1`; hence `A_2=0`.

For degree four,

```text
(a+7b)^4+(a-7b)^4 = 2a^4+588a²b²+4802b^4,
2(5b)^4+2(-5b)^4 = 2500b^4,
S_4 = 2a^4-12a²b²+2b^4.
```

Therefore

```text
A_4 = 600a²b²+2300b^4
    = 100b²(6a²+23b²).
```

Both factors are nonnegative. If `b=0`, `A_4=0`. Conversely, if `A_4=0` and `b≠0`, then `b²>0` and `6a²+23b²>0`, contradiction. Thus `A_4≥0` and `A_4=0 ↔ b=0` for all real `a,b`.

All six replacement nodes are real. Construction is polynomial, homogeneous, source-coordinate-defined, and independent of any divisor or zero list. This proves `[PAPER-PROVED] GTA-PQ4`.

## Hostile attacks

1. Degree-one/two matching does not force canonical lift. Four-odd-node symmetric ansatz with even scale `k` and odd scale `l` requires `k²-2l²=-1`; nontrivial Pell solution `(k,l)=(7,5)` changes quartic sign globally.
2. Positivity does not use divisor data: nodes depend only on literal `(a,b)` and fixed integers `7,5`.
3. Exact-term searches found signed/truncated moment theory but no matching graded realification or quartic-faithful construction. Priority remains provisional; algebraic derivability alone does not establish scientific novelty.
4. `a=0` gives `2300b^4`; `b=0` gives zero; all other ratios give strict positivity. Charge is homogeneous of degree four.

## Open core

`[CLOSED]` Explicit Pell lift constructs a quartic-positive faithful member.

`[OPEN CORE]` Assemble these local positive charges across actual theta stages with coefficient-faithful Xi completion, then derive a literal-source fourth-supertrace vanishing law. Local positivity removes cancellation but does not supply global vanishing.

## No-go closure

- **Exact killing theorem/mechanism:** predecessor C1-GM1 Hilbert coercivity failed because every trace-class correction is compact and cannot control an infinite cofinal unit family.
- **Strongest positive survivor:** fixed Pell-scaled graded realification with one cancellation-free quartic charge.
- **New insight:** preserving mass and quadratic trace does not force sign-indefinite higher orientation. Extra real separation can move all nonreality into one positive fourth-order supertrace.
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`; exact-claim literature searches found no match; priority remains provisional.

## Lean realization

`formal/GaloisForLFunctions/HTGeometry/SourcePairPositiveQuarticGradedRealification.lean` proves unconditionally:

- exact real even/odd matrix blocks and all-degree trace interpretations;
- preservation of signed traces in degrees one and two;
- quartic identity `A₄ = 100b²(6a²+23b²)`;
- nonnegativity and `A₄ = 0 ↔ b = 0`;
- real-divisor replacement plus strictly positive anomaly alternative for every nonreal source pair.

Direct `lake env lean`, exact-module `lake build`, and `scripts/formal_tools.py lint` pass. `#print axioms` for headline theorems reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `GaloisForLFunctions/HTGeometry.lean`; no umbrella build was run.

## Log

- 2026-08-27 — frozen after C1 global-mean coercivity conjecture failed by trace-class compactness. Representation changed from Hilbert coercivity to higher graded trace orientation, using GTA's corpus-proved degree-one/two lock and joint higher-anomaly faithfulness.
- 2026-08-27 — hostile uniqueness attack failed through Pell family; `(7,5)` construction closes paper proof and makes quartic anomaly alone positive and faithful.
- 2026-08-27 — exact theorem formalized, targeted build/lint/axiom gates passed, and HTGeometry umbrella wired.
