# Typed event-order diamond carrier boundary

- **ID:** `event-order-diamond-carrier-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CARRIER CLASSIFICATION / NO-SELECTION BOUNDARY
- **Paper proof:** `event-order-diamond-carrier-boundary.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.EventOrderDiamond`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Formalized statements

The module
`formal/GaloisForLFunctions/HTGeometry/EventOrderDiamond.lean`
proves unconditionally:

1. `eventOrderDiamondDefect_eq_zero_iff` — the typed defect vanishes exactly when the two
   complete histories agree;
2. `eventGaugeTransform_apply` — evaluation under a source/target frame change;
3. `eventGaugeTransform_comp` — intermediate frame cancellation under composition;
4. `eventOrderDiamondDefect_gauge_covariant` — full vertex-gauge covariance with only endpoint
   action remaining;
5. `eventGaugeTransform_eq_zero_iff` and
   `eventOrderDiamondDefect_gauge_eq_zero_iff` — frame-independent vanishing;
6. `eventOrderDiamondDefect_postcompose` and
   `eventOrderDiamondDefect_precompose` — common later and earlier histories compose with the
   defect;
7. `eventOrderDiamondDefect_contextIndependent` — fixed-type history-independent events collapse
   to an endomorphism commutator;
8. `matrix_contextIndependent_orderDefect_trace_zero` — the finite matrix central trace channel
   then vanishes; and
9. `eventOrderDiamondDefect_universal` — every linear map occurs as a typed defect, proving exact
   no-selection;
10. `eventDiamondFixedCarrier_upper_reconstruct` and
    `eventDiamondFixedCarrier_lower_reconstruct` — both typed paths are exact compressions of
    block-endomorphism paths on one direct-sum carrier; and
11. `eventDiamondFixedCarrier_defect_reconstruct` — the full typed defect is exactly the
    corresponding fixed-carrier defect compression.

No event map is assumed invertible. Only vertex-frame changes are linear equivalences.

## Audit

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.EventOrderDiamond
✔ [2954/2954] Built GaloisForLFunctions.HTGeometry.EventOrderDiamond
Build completed successfully (2954 jobs).
```

Repository formal lint:

```text
scripts/formal_tools.py lint
PASS
```

`#print axioms` was run from `/tmp/EventOrderDiamondAxioms.lean`. Dependencies are limited to
Mathlib's standard quotient/extensionality infrastructure:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration in the module.

## Physical boundary

The Lean theorem does not define actualization, causal order, spacetime, gauge curvature,
Hypertranscendence, the Standard Model, or dynamics. Universality is a hostile result: because
every linear map is a typed defect, the carrier cannot select a force. The frozen physical
programme must independently derive event types, admissible edges, amplitude calibration, and the
four stable physical projections. Fixed-carrier dilation is a second hostile result: a nonzero
finite typed diamond cannot by itself witness fundamental carrier change.

## Gates

- [x] 0 → 1: precise typed carrier and gauge action
- [x] 1 → 2: complete paper proof
- [x] 2 → 3: unconditional Lean module, focused build, axiom audit, lint
- [ ] 3 → 4: intentionally blocked; no new physics or publication-level theorem follows

## Log

- 2026-07-29 — formalized typed diamond covariance, attachment, commutator collapse, trace
  obstruction, and no-selection universality; focused build and axiom audit passed.
- 2026-07-29 — added exact direct-sum block dilation and reconstruction of both paths and their
  defect; repeated focused build, axiom audit, and lint passed.
