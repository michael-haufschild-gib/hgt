# Unconditional circle winding for the descended completed zeta

- **ID:** xi-descent-unconditional-circle-winding
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean), [PROVED]
- **Date:** 2026-07-11
- **Module:** GaloisForLFunctions.RHTower.UPlaneWindingCircle

## Formal surface

- `windingNumber_xiDescent_circle`: on any positive-radius circle avoiding `xiDescent` zeros, Lean
  constructs the exact finite set of interior zeros and identifies the winding with their total
  analytic order.
- `loopCharge_xiDescent_circle`: reduces the same internally constructed total order modulo the
  rung `2^k`.

## Discharged interfaces

The underlying argument-principle theorem required a caller to provide a larger radius, a finite
zero census, proof that the census contains every zero in the larger ball, and proof that every
census point lies inside the target circle. Local finiteness of the entire descended function now
constructs all of this internally. The only geometric precondition left is necessary: the boundary
loop itself must avoid zeros.

## Certificate

- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.UPlaneWindingCircle` (8590 jobs).
- Axiom audit passed for both public theorems; only `propext`, `Classical.choice`, and `Quot.sound`
  occur.
- No full or umbrella build.
- No sorry, admit, axiom, opaque, or unsafe declaration in the new module.
