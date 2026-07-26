# The loss-aware doctrine atlas is the maximal method-neutral field-one construction

- **ID:** field-one-loss-aware-doctrine-atlas
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / NO-GO CLOSURE (Lean)
- **Labels:** `[BRIDGE] [PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Depends on:** `field-one-multiplicative-core`,
  `field-one-additive-fork`,
  `field-one-affine-projective-monoid-geometry`,
  `field-one-signed-band-axis`,
  `field-one-group-cyclotomic-extensions`
- **Statement:** A method-neutral `F₁` is an indexed atlas, not one carrier.
  Its nodes name doctrines and enhancement axes; its edges name comparison
  kind and a nonempty loss ledger whenever the edge is not an equivalence;
  its point counts name their point functor. The atlas contains every major
  doctrine family in the literature audit, while the exact two-element core,
  three-element signed base, two total-addition branches, and two projective
  point functors remain formally distinct.

## Definitions

The doctrine index contains pointed monoids, relative monoid schemes, Soulé
gadgets, blueprints, ordered blueprints, bands, hyperrings/pastures,
idempotent semirings, the characteristic-two branch, Lambda geometry, Durov
generalized rings, Haran non-additive geometry, sphere spectra, Gamma
algebras, congruence spaces, and arithmetic/scaling sites.

Enhancement axes are multiplicative, total-additive, relational-additive,
ordered, descent, generalized-operation, homotopical, topological, and
analytic. A node profile carries a nonempty finite set of axes and a finite
set of point functors.

An atlas edge records source, target, comparison kind, evidence status, and
loss features. Evidence status distinguishes Lean-formalized, literature, and
mixed edges. The constructor requires a proof that every non-equivalence edge
has a nonempty loss ledger. Loss features distinguish carrier identification,
forgotten or imposed additive/null relations, scalar extension, modules,
spectrum, point functor, exactness, and homotopy data.

## Complete paper proof

### Carrier no-go

The pointed-monoid base has carrier `WithZero PUnit`, hence two elements.
The signed band base has carrier `SignType`, hence three. The already-proved
carrier theorem rules out a type equivalent to both. Therefore a single
literal carrier cannot represent all nodes.

### Addition no-go

Every total semiring addition on a nontrivial two-element carrier has
`1+1=0` or `1+1=1`, with the branches disjoint. Relational addition evades
the dichotomy by changing operation type, not by providing a third total
operation. Therefore the atlas must keep total and relational additive axes
separate.

### Base-extension no-go

For the signed carrier, forgetting balanced null sums changes scalar
extension from the quotient specializing the sign to `-1`, canonically `R`,
to the group algebra `R[C₂]`. Therefore a non-equivalence edge needs an
explicit loss ledger; carrier-level mapping alone is insufficient.

### Point-functor no-go

The module/Tits projective point functor has `n` points in rank `n`, while
the monoid-Proj topological point functor has `2^n-1`. Both are valid and
already proved. Therefore an unqualified point count cannot be an atlas
invariant.

### Positive construction

Index each doctrine instead of quotienting doctrines together. Give every
node a nonempty axis profile and named point functors. Give every comparison
an edge kind. Require every non-equivalence edge to carry a nonempty loss
ledger. The signed-forgetful edge records loss of null relations and change
of scalar extension; sign collapse records carrier identification and
changed null relations. All listed doctrine families receive profiles, so
none is selected as a universal winner. Exact algebraic content remains in
the dependency modules, while the atlas records how that content may and may
not be compared.

This construction is dependency-closed: carrier, addition, scalar-extension,
and point-functor obstructions are the universal identifications it rejects;
doctrine-specific localization or scheme comparison theorems can be added as
evidence-labelled edges without changing the base definition. ∎

## Hostile audit

1. **The atlas proves all doctrines equivalent — `FALSE`.** Its purpose is to
   preserve inequivalence and require explicit comparison data.
2. **A doctrine name formalizes its published scheme theory — `FALSE`.**
   Profiles are construction indices; only theorem packages named by a node
   are formal certificates.
3. **The atlas has a preferred node — `FALSE`.** It has a distinguished
   multiplicative shadow because that universal property is proved, not a
   doctrine declared universally superior.
4. **Every edge is lossy — `FALSE`.** Certified equivalences may have empty
   ledgers; only non-equivalences must name a loss.
5. **Point counts are atlas-global — `FALSE`.** They are indexed by point
   functor.

**Verdict:** `BRIDGE`. This is a conservative formal organization of proved
incompatibilities and current doctrine families, not a claim of new
mathematics.

## Gates

- [x] 0 → 1: doctrine inventory and exact invariants typed.
- [x] 1 → 2: dependency-closed proof and hostile audit complete.
- [x] 2 → 3: exact Lean atlas package and axiom audit complete.
- [ ] 3 → 4: publication-ready extraction.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FieldOneDoctrineAtlas`
- **Theorems:** `primaryAxis_mem_doctrineProfile`,
  `certifiedProjectivePointCount_correct`,
  `nonEquivalence_has_named_loss`, `every_comparisonFacet_required`,
  `doctrineAtlas_no_literal_common_carrier`,
  `moduleTits_ne_monoidProj`, `characteristicTwo_ne_idempotent`
- **Construction:** `fieldOneDoctrineAtlas`
- **Audit:** direct `lake env lean` and final targeted `lake build` passed;
  `#print axioms` reports only standard Lean principles.

## Log

- 2026-07-26 — atlas gap isolated after hostile review of the construction
  document; paper definition and no-go closure completed.
- 2026-07-26 — formalized unconditionally; targeted build and axiom audit
  passed; construction document linked to exact Lean certificate.
