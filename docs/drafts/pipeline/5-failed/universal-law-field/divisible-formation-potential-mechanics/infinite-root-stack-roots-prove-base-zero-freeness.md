# Infinite-root-stack roots prove base zero-freeness

- **ID:** ULF-DFPM-FAIL-3
- **Stage:** 5-failed
- **Conjecture:** Constructing roots at every depth on an infinite root stack proves that the base
  formation transfer has zero divisor.
- **Verdict:** [FALSE] [RAMIFIED-COVER COUNTERMODEL] [DESCENT HOLONOMY SURVIVES]

## Countermodel

On a disk with coordinate (z), take (R(z)=z).  For every (n\ge2), the ramified cover

\[
 z=w^n
\]

supplies the root (w).  Equivalently, the (n)-th root stack carries a tautological root.  But the
base divisor of (R) is still the nonzero point (z=0) with multiplicity one.

Thus “roots exist after changing the base” does not satisfy the base-meromorphic hypothesis of the
divisible-lift selection theorem.  Infinite root stacks retain divisor charge as isotropy; they do
not erase it.

## Positive survivor

If (R(z)=z^q u(z)) with (u(0)\ne0), an (n)-th root on the punctured universal cover acquires
monodromy

\[
 \exp(2\pi i q/n)
\]

around the puncture.  It descends to a single-valued meromorphic root on the base exactly when
(n\mid q).  Trivial descent for unbounded (n) therefore forces (q=0).

The missing field law is **effective divisible descent**: source-produced roots must descend through
the common recovery base with trivial Kummer isotropy.  Merely constructing a root gerbe is theatre.

This local descent theorem is incorporated into ULF-DFPM-1.  No Lean was written in this pass.

