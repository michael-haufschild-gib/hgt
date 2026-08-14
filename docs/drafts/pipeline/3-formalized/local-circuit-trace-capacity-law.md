# Local-circuit trace capacity law

- **ID:** `local-circuit-trace-capacity-law`
- **Stage:** 3 -- formalized in Lean 4
- **Parent:** `../3-formalized/local-circuit-heap-capacity-law.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/LocalCircuitTraceCapacity.lean`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [NO SORRY] [WIRED]`
- **Date:** 2026-08-14

## Formal theorem

Let `alpha` be a finite ordered alphabet and let `independent` be a symmetric relation.  Words are
equivalent under adjacent swaps of independent letters.  A dependence edge is an unordered pair
of distinct, non-independent letters.  If every letter is incident to at most `Delta` dependence
edges, then the number `h_ell` of length-`ell` trace classes satisfies

```text
h_ell <= choose (|alpha| + ell - 1) ell * 2^(Delta * ell).
```

For all depths through `s`,

```text
sum_{ell=0}^s h_ell
  <= (s + 1) * choose (|alpha| + s - 1) s * 2^(Delta * s).
```

No trace normal form is assumed.  The proof constructs a complete code consisting of the
multiplicity multiset and one ordered binary projection for every dependence edge.  Equality of
codes is proved to imply trace equivalence by moving the first matching letter across an
independent prefix.  Double counting edge incidences yields the exact exponent `Delta * ell`.

## Principal declarations

- `traceEq_of_perm_of_pairProjections`
- `traceEq_of_wordTraceCode_eq`
- `edgeProjectionMass_eq_sum_incident`
- `edgeProjectionMass_le_of_maxDegree`
- `natCard_fixedTraceClass_le_maxDegree`
- `cumulativeTraceCount_le_maxDegree`

## Audit

- Scoped build: `lake build GaloisForLFunctions.RHTower.LocalCircuitTraceCapacity`
- Imported by `GaloisForLFunctions.RHTower`
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration

## Boundary

This theorem closes exact circuit-dictionary entropy accounting.  It does not prove physical-time
first escape, monotone complexity growth, plateau onset, or Brown-scale recurrence time.  Those
require a quenched incidence estimate for one static local Hamiltonian after common return and
fast-forwardable carrier removal.
