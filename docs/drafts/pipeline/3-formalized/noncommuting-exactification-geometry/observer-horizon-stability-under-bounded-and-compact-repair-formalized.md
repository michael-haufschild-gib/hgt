# Observer horizon stability under bounded and compact repair — Lean certificate

- **ID:** `observer-horizon-stability-under-bounded-and-compact-repair-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `observer-horizon-stability-under-bounded-and-compact-repair.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/ObserverHorizonStability.lean` | §1 multivalued horizon of a closed relation, §2 bounded-repair invariance, §3 positive-form horizon invariance, §4 compact stability of a weakly null singular sequence |

Namespace `GaloisForLFunctions.HTGeometry`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| §1 horizon of a closed relation, graph form | `multivaluedHorizon`, `graphShear`, `graphShear_image_graph` |
| §1 the bounded repair `T + B` and its closed graph | `boundedShift`, `closure_graph_boundedShift` |
| §2 Thm 2.1 bounded repair moves the horizon by a bounded shift | `multivaluedHorizon_boundedShift` |
| §2 single-valuedness of the horizon is preserved as well | `multivaluedHorizon_boundedShift_eq_singleton_iff` |
| §3 Thm 3.1 sequential closability is a bounded-form invariant | `IsSequentiallyClosableForm`, `isSequentiallyClosableForm_add_iff`, `isSequentiallyClosableForm_add_bounded_iff` |
| §4 a compact operator kills a weakly null sequence in norm | `tendsto_norm_compact_of_weaklyNull`, `tendsto_norm_add_compact_of_weaklyNull` |
| §4 Thm 4.1 no lower bound survives a compact repair | `not_exists_lower_bound_of_weaklyNull` |
| §4 Thm 4.1 the repaired operator is not injective with closed range | `not_injective_and_isClosed_range_of_weaklyNull` |

## Verification

Foreground per-file elaboration and a cached foreground `lake build` of the module both pass.
The axiom audit of `not_injective_and_isClosed_range_of_weaklyNull` reports only `propext`,
`Classical.choice`, `Quot.sound`.

The route-level corollaries 2.2, 3.2 and 4.2 of the card are readings of these three theorems
against corpus inputs recorded elsewhere; they add no mathematical content of their own, and §5 is
a summary table of the same three statements.

## Boundary

The statements are about a single closed operator or relation on a Hilbert space and its bounded
or compact perturbations.  Nothing here selects a particular arithmetic operator, and no RH
consequence is claimed.
