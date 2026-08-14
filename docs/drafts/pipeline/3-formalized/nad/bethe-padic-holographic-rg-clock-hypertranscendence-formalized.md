# bethe-padic-holographic-rg-clock-hypertranscendence — formalized

- **ID:** `bethe-padic-holographic-rg-clock-hypertranscendence-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `bethe-padic-holographic-rg-clock-hypertranscendence.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`
- **Shared substrate:** `_RG-CLUSTER-SHARED-LEAN.md`

## What is formalized

The card's own dynamical argument is unconditional in Lean: the exact rational family and its
algebra, the multiplier at the anchor, the interior non-superattracting non-repelling fixed point,
and the exclusion of **every** family on the Ritt list (power, inverse power, Chebyshev, Lattès)
from that fixed point.  The Schröder/Poincaré function the conclusion is stated about is itself
constructed and characterized: Koenigs' theorem (existence and uniqueness) for a general holomorphic
germ, its local inversion, and its entire extension.

See `_RG-CLUSTER-SHARED-LEAN.md` for the module-by-module list and the audited declarations.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

Every declaration resolves and `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`.  No `sorry`, `admit`, `axiom`, `opaque` or `unsafe` declaration is used.

## Boundary

The converse classification (Ritt / Becker--Bergweiler) remains a cited classical input, as the
card's own Lean boundary states; it is not postulated in Lean.  The card's remaining open gates are
external literature audits and explicitly labelled onward conjectures (and, for the postselected
qubit card, a physical experiment) — none of them formalization obligations.
