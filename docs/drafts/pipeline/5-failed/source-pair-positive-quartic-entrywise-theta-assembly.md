# Source-pair positive quartic entrywise theta assembly

- **ID:** `source-pair-positive-quartic-entrywise-theta-assembly`
- **Stage:** 5-failed
- **Type:** FALSIFIED / THEOREM (Lean)
- **Route:** GTA (`ORIENT LAND COMP`)
- **Statement:** Summing the positive quartic source-pair charge over literal complex coefficients of a finite source matrix detects whether its ordinary divisor is real.

## Goal

Test whether the canonical coefficient-cell assembly already used by theta odd-pole completion can globalize the positive local quartic reporter without selecting eigenvalues.

## Gates

- [x] 0 → 1 in-progress: exact entrywise claim frozen; source-cell carrier fixed
- [x] 1 → 2 fully-proven: explicit Hermitian counterexample and positive survivor
- [x] 2 → 3 formalized: exact counterexample theorem, targeted build/lint/axiom audit

## Internal frontier

- `[CORPUS]` `thetaSourceSignedFiniteMatrix_cellDecode` recovers every literal theta-stage coefficient from a real source-pair cell.
- `[CORPUS]` `thetaSourceCanonicalCellOddPoleEscapeXiCompletion` assembles odd cells entrywise and retains compact-open Xi completion.
- `[CORPUS]` `sourcePairPositiveQuarticCharge_eq_zero_iff` gives one nonnegative local coefficient charge.

## Frozen conjecture

`[CONJECTURE GTA-PQ4-E]` For a finite complex source matrix, zero entrywise total positive quartic charge is equivalent to real ordinary divisor.

## Hostile attack

Test Hermitian matrices with nonreal off-diagonal coefficients. Hermiticity forces real spectrum while entrywise coefficient charges may remain positive.

**Verdict:** `[FALSIFIED]`.

Take

```text
H = [[0,i],[-i,0]].
```

Then `H*=H`, and

```text
det(zI-H)=(z-1)(z+1),
```

so every divisor point is real. Diagonal coefficient cells have zero charge. Both off-diagonal cells have `(a,b)=(0,±1)`, hence charge `100·1·23=2300`. Entrywise total is `4600>0`. Therefore real divisor does not imply zero entrywise charge.

## Open core

`[CLOSED]` Entrywise local orientation does not descend to real-divisor orientation.

`[OPEN CORE]` Construct a conjugation-invariant, root-free, stage-degree-dependent positive reporter from literal source, or prove its class reduces to the existing Hermite/Green RH-strength flag.

## No-go closure

- **Exact killing theorem/mechanism:** Hermitian off-diagonal phase is coefficientwise nonreal but spectrally real; entrywise charge is not unitary/gauge invariant.
- **Strongest positive survivor:** local positive quartic charge remains a faithful spectral-pair reporter, but only after a conjugation-invariant pairing/assembly. Coefficient-cell assembly is excluded.
- **New insight:** odd-pole entrywise completion and spectral-orientation realification cannot share the same assembly functor. GTA must keep occurrence and orientation channels separate until a unitary-invariant landing.
- **Status:** `[LEAN-PROVED NO-GO]`; positive survivor is `[LEAN-PROVED]` in `source-pair-positive-quartic-graded-realification.md`.

## Lean realization

`formal/GaloisForLFunctions/HTGeometry/SourcePairPositiveQuarticEntrywiseAssemblyNoGo.lean` proves the counterexample matrix is Hermitian, its divisor factors as `(z-1)(z+1)`, every divisor zero is real, and its entrywise charge is exactly `4600>0`.

Direct `lake env lean`, exact-module `lake build`, and formal lint pass. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `GaloisForLFunctions/HTGeometry.lean`; no umbrella build was run.

## Log

- 2026-08-27 — opened from positive quartic local reporter and canonical entrywise theta odd-cell assembly.
- 2026-08-27 — falsified by `[[0,i],[-i,0]]`; complete paper proof and representation lesson recorded.
- 2026-08-27 — no-go formalized and moved to failed lane after positive survivor audit.
