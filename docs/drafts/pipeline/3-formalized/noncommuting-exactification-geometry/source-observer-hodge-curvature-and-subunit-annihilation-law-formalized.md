# Source–observer Hodge curvature and subunit annihilation — Lean certificate

- **ID:** `source-observer-hodge-curvature-and-subunit-annihilation-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `source-observer-hodge-curvature-and-subunit-annihilation-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/SourceObserverHodgeCurvature.lean` | §2 Thm 2.1, §3 Cor 3.1–3.4 with the sharpness witness, §4 Thm 4.1 |

Namespace `GaloisForLFunctions.HTGeometry`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| comparison curvature and the observer field | `comparisonCurvature`, `observerField`, `observerField_eq_add` |
| §2 Thm 2.1 the Gauss–Hodge identity | `inner_observerField_self_eq`, `norm_observerField_sq_le` |
| §3 Cor 3.1 exact comparison annihilates the field | `observerField_eq_zero_of_exact` |
| §3 Cor 3.2 subunit curvature annihilation | `observerField_eq_zero_of_subunit`, `norm_observerField_sq_le_of_subunit` |
| §3 Cor 3.3 source energy condition | `reWork_le_of_subunit` |
| §3 Cor 3.4 approximate co-closure | `observerField_eq_zero_of_reWork` |
| §4 Thm 4.1 gauge covariance of the criterion | `comparisonCurvature_gauge`, `isFormalCoDifferential_gauge`, `subunit_criterion_gauge_iff` |
| sharpness at gain `1` | `exists_unitGain_observerField_ne_zero` |

## Verification

Foreground per-file elaboration and a cached foreground `lake build` pass.  The axiom audit of
`subunit_criterion_gauge_iff` and `exists_unitGain_observerField_ne_zero` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Boundary

The annihilation law is a Hilbert-space identity for a comparison pair and its formal
co-differential.  The sharpness witness shows the subunit hypothesis cannot be relaxed to gain `1`.
No arithmetic comparison pair is constructed.
