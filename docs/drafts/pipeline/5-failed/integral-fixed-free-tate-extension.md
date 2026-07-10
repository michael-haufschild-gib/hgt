# Integral fixed/free Tate residue (DUAL-GATE FAIL)

- **ID:** integral-fixed-free-tate-extension
- **Stage:** 5-failed
- **Type:** PROVED BRIDGE / RETIRED RH ROUTE
- **Date:** 2026-07-10
- **Lean:** `formal/GaloisForLFunctions/RHTower/IntegralOrbitTateExtension.lean`
- **Verdict:** The algebra is correct, but the proposed scientific claim fails the novelty gate and
  the non-tautology attack.  It is the already-known mod-two cardinality of a fixed versus free
  involution orbit, repackaged through the unit extension residue.

## Proved algebra

The canonical integral matrix `[[X^m,1],[0,X]]` base-changes to the rational FE-semilinear unit
extension.  For the residue lattice:

- fixed orbit: the norm is `n |-> 2n`, so the unit residue survives in `Z/2Z`;
- free swap orbit: every invariant `(c,c)` is the norm of `(c,0)`, so the unit pair dies.

All statements are formalized and axiom-clean.

## Why this is not new knowledge

The fixed/free distinction is exactly orbit cardinality modulo two:

- a fixed orbit has one event;
- a free involution orbit has two events.

`BandEdgePairing.lean` already proves that a fixed-point-free involution has even cardinality and
that nonzero unit mod-two flux forces a fixed point.  The Tate computation is the same theorem in
the residue-module vocabulary.  A competent algebra prompt or literature search supplies it
immediately.

## Why it does not attach arithmetic content

Assigning the unit residue to each orbit makes the charge nonzero precisely when the orbit is fixed.
That is not a derived ξ constraint; it is a restatement of orbit type.  The proposed attachment
theorem—“every ξ-zero orbit receives nonzero fixed-orbit charge”—would already assert that every
orbit is fixed and hence would restate RH.

The integral lattice remains useful infrastructure, but it is not an RH-bearing invariant and must
not be cited as new branch knowledge.

## Surviving residue

Any live invariant must use compatibility information beyond:

- local extension residue;
- stabilizer norm or orbit cardinality;
- the exponent-two FE/Schwarz symmetry group.

In particular, it must distinguish how FE and Schwarz identifications glue the completed arithmetic
object, not merely whether their composite fixes the base point.
