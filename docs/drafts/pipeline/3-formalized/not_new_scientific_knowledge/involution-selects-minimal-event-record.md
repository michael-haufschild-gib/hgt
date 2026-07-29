# An involution canonically selects a minimal complementary event record

- **ID:** `involution-selects-minimal-event-record`
- **Stage:** 3-formalized
- **Type:** SPECTRAL-FRACTURE CLASSIFICATION / SOURCE-NATURAL RECORD BRIDGE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../../2-fully-proven/not_new_scientific_knowledge/involution-selects-minimal-event-record.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`

## Formal theorem

For a complex matrix involution \(A^2=1\), define

\[
C_A=(1+A)/2,\qquad R_A=(1-A)/2.
\]

Lean proves:

1. \(C_A+R_A=1\);
2. \(C_AR_A=R_AC_A=0\);
3. \(C_A^2=C_A\);
4. \(\ker C_A=\operatorname{range}R_A\);
5. \(\ker R_A=\operatorname{range}C_A\);
6. \(x\mapsto(C_Ax,R_Ax)\) is injective when the record is corestricted to its range;
7. \(\operatorname{coker}C_A\) is canonically linearly equivalent to
   \(\operatorname{range}R_A\); and
8. on \(\mathbb C^{10}\), `trace A = 2` forces record rank four and the exact continuation
   kernel/range/cokernel index `4/6/4`.

## Lean declarations

```text
involutionContinuationProjection
involutionContinuation_add_record
involutionContinuation_mul_record
involutionRecord_mul_continuation
involutionContinuation_isIdempotent
involutionContinuation_ker_eq_record_range
involutionRecord_ker_eq_continuation_range
involutionRecordToRange
involutionRecordToRange_surjective
involutionContinuation_prod_record_injective
involutionRecordToRange_ker_eq_continuation_range
involutionContinuationCokernelEquivRecordRange
traceTwoInvolution_record_four_continuation_six
traceTwoInvolution_continuation_four_six_four
```

## Verification

- scratch proof against pinned toolchain: passed;
- direct
  `lake env lean GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`: passed without
  warnings;
- final `lake build GaloisForLFunctions.HTGeometry.EventInvolutionComplement`: passed
  (`2947/2947`);
- `scripts/formal_tools.py lint`: passed;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- no stale Lean or Lake process remained.

## Novelty and physics boundary

`[NOT NEW MATHEMATICS]` This is elementary spectral decomposition of an involution. Krasnov's
compatible-pure-spinor `6+4` product structure is also published mathematics.

Lean does not prove that a physical event selects the involution, that either projector is a
quantum operation, that the record becomes a distinct spacetime carrier, or that the Albert cubic
supplies its Lorentzian metric and dynamics.

## Exact research delta

The prior event model assumed a maximal-rank intertwiner and then needed an arbitrary complementary
record. Under an involutive source, both are now canonical:

\[
A\longmapsto\big((1+A)/2,(1-A)/2\big).
\]

The remaining difficulty is physical transport and interpretation, not finite-dimensional
selection.

## Log

- 2026-07-29 — dependency-closed spectral complement promoted to unconditional Lean.
- 2026-07-29 — module build, formal lint, and standard-foundation axiom audit passed.
