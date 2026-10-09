# Identify actual root-loop transport with covering monodromy

- **ID:** POLYNOMIAL-COVERING-MONODROMY-IDENTIFICATION-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; external novelty unverified; corpus only
- **Parent:** `finite-planar-polynomial-realization.md`
- **Target:** Identify the constructed root-loop permutation with the native covering-space monodromy for the actual polynomial over the complement of its supplied critical values. Keep permutation orientation explicit.

## Corpus audit

The documented `polynomial covering critical` lexical query returned six hits across three modules; all six declaration entries were inspected. The exact covering mechanism is installed `Polynomial.isCoveringMapOn_eval` in `Mathlib/Analysis/Complex/CoveringMap.lean`: evaluation covers the complement of the image of its derivative zero set. Its complete proof was inspected. `HTGeometry/TwoMarkPolynomialApproximation.lean` and `Bottcher/EscapeCovering.lean` already restrict this theorem for specific families. `OrderedCriticalValueCovering.lean` instead covers parameter configurations. Native `IsCoveringMap.monodromy` and `liftPath` are in installed `Topology/Homotopy/Lifting.lean`. No external sources used.

## Complete paper proof [PROVED HERE]

For an actual parameter v, let P be its additive polynomial and B_j its supplied critical values. Put Y={w:∀j,w≠B_j}, X={z:P(z)∈Y}, and p:X→Y, z↦P(z). The proved derivative-root classification says every zero of P′ equals a supplied critical position; its value is the corresponding B_j by the actual definitions. Hence Y misses every actual critical value. Restrict the inspected polynomial covering theorem to Y. Its standard preimage restriction is exactly p, so p is a covering for every v; distinctness of B is unnecessary here.

For b∈Y, the ordinary root fiber {z:P(z)=b} is equivalent to p⁻¹(b): attach to z the regular-source membership obtained from P(z)=b, and erase that membership in the inverse. Both composites preserve the complex root exactly, so they are identities.

Given a loop γ at b in Y, lift it through the covering from the image of an ordinary root z. Forgetting the regular-source membership gives a continuous complex path u with P(u(t))=γ(t), u(0)=z. The previously proved unique polynomial root continuation therefore identifies its endpoint with `rootLoopTransport` for the underlying complex loop. Native covering monodromy is defined by this same lifted endpoint. The fiber equivalence consequently intertwines the two actions on every root. In particular the actual root-loop transport depends only on the based homotopy class of a regular-value loop. The convention in the installed monodromy group homomorphism must be checked explicitly; no orientation equality is inferred merely from names.

This identifies already constructed continuation with the actual covering, without assuming transitive monodromy, branch inertia, exterior behavior, meridian-product relations, or Hurwitz exchanges. Those later geometric obligations remain separate.

## Native simple-branch permutation — complete paper proof [PROVED HERE]

The inspected `coe_monodromyPerm` theorem is definitionally the same `monodromy` endpoint map, with no reversal of the loop. The intertwining equality therefore identifies permutations with the same orientation. Based-homotopic regular loops have equal native quotient classes, so their root-loop permutations coincide after applying the injective fiber equivalence.

For each regular critical value, the preceding audited theorem constructs a positive circle, avoidance, and a root-loop transposition. Include that circle pointwise into Y using avoidance. Its basepoint belongs to Y by evaluating avoidance at time zero. Forgetting this inclusion recovers the same complex circle. The intertwining equality sends its two exchanged roots to two distinct native covering-fiber elements, exchanges those elements and fixes all others, since the fiber equivalence is surjective. Thus the native `monodromyPerm` of this positive circle is itself a transposition. This discharges the branch permutation for the actual covering; it adds no monodromy hypothesis.

## Log

## Final certificate — 2026-10-09

Two production modules, `HTGeometry/OrderedPolynomialCoveringMonodromy.lean` (8 explicit declarations) and `HTGeometry/OrderedPolynomialMeridianMonodromy.lean` (1), prove the exact identification and native transposition target. Both production leaf builds, all nine standard-only axiom audits and both final actual-source `lake env lean` checks pass; final logs are empty. Audit log: `/tmp/hgt-polynomial-covering-monodromy-axioms.log`. Both modules are wired into the HTGeometry umbrella. Index refresh and authoritative global lint both pass (`/tmp/hgt-polynomial-covering-monodromy-index.log` and `/tmp/hgt-polynomial-covering-monodromy-lint.log`).

`rootLoopTransport_eq_covering_monodromy` identifies every actual root-loop action with native covering monodromy in the same path orientation. `rootLoopTransport_eq_of_homotopic` proves based-homotopy invariance. `exists_positiveCircle_monodromyPerm_isSwap` constructs the positive circle in the actual regular target and proves its native `monodromyPerm` is a transposition. The actual covering exists even when critical values collide; distinctness is used only for the simple-branch transposition. No native monodromy hypothesis is assumed.

Next: `polynomial-exterior-cycle.md`, with dependency-closed paper proofs for the exterior cycle and a stronger primitive-coordinate rigidity law forcing exact sheet cardinality without a finiteness premise. Meridian-product geometry, critical-value exchanges, prescribed planar realization, and finite Xi completions remain open. Earlier log entries below are historical; implementation scratch files are removed after this certificate, and audits remain.

- 2026-10-09 — paper proof and inspected corpus dependencies recorded before new code. The preceding eight-module local transposition construction is in final production/axiom/source audit; no second compiler will run concurrently.

- 2026-10-09 — preceding local transposition construction is fully audited and promoted. `OrderedPolynomialCoveringMonodromy.lean` passes scratch (8 declarations): actual regular source/target/projection, covering theorem, exact fiber equivalence, equality of root-loop transport with native covering monodromy, and based-homotopy invariance. Two subtype elaboration errors were repaired by exposing set membership and composing value equalities directly. Production build is followed by checking `/tmp/hgt-ordered-polynomial-meridian-monodromy.lean`, which constructs the positive circle inside the actual regular target and transfers the proved transposition to native `monodromyPerm`. Final native audits remain pending.

- 2026-10-09 — native identification production build passes. `exists_positiveCircle_monodromyPerm_isSwap` passes scratch Lean: the constructed positive circle lies in the actual regular target and its native covering monodromy is a transposition. A local name conflicted with unit-interval notation and was renamed; no mathematical change. The second production build, all nine public axiom checks and both actual-source final checks are running sequentially. Higher-degree local cycles and exterior monodromy remain next geometric obligations.
