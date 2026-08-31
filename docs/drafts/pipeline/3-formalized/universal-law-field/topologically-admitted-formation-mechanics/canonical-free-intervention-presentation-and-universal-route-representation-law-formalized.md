# Canonical flat intervention quotient and universal readout law — Lean formalization

- **ID:** ULF-TAFM-13
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper source:** `../../../2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/canonical-free-intervention-presentation-and-universal-route-representation-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.CanonicalFreeInterventionPresentation`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified object

`LinearInterventionGrammar k I R O` stores primitive intervention histories, primitive legal
rewrite boundaries, observer reports, and observer neutrality on every relation. Its canonical
history module is

`PresentedHistory G = (I →₀ k) ⧸ LinearMap.range G.boundary`.

No readout coordinates occur in this definition.

## Certified laws

1. `observer_boundary`: observer information is neutral on every finite rewrite chain.
2. `routeLinear_boundary_eq_zero`: the primitive flat-readout test kills all legal rewrite
   boundaries.
3. `range_boundary_le_routeLinear_ker`: admissibility gives the exact quotient-lift premise.
4. `routeQuotientLift_classOf`: canonical quotient lift reconstructs the free readout map on every
   source history.
5. `apply_classOf_eq_routeLinear_of_generator`: any flat representation with prescribed generator
   values has that same reconstruction law.
6. `routeAnnihilatesRelations_of_representation`: a presented representation necessarily kills
   every primitive relation.
7. `existsUnique_routeRepresentation_iff`: a generator assignment extends to exactly one flat
   quotient representation iff it annihilates every primitive legal relation.
8. `presentedObserver_classOf` and `presentedObserver_generatorClass`: observer assignment descends
   canonically and retains all declared generator reports.
9. `canonicalFreeInterventionPresentation_capstone`: universal flat-readout classification and observer
   reconstruction in one closed theorem.

## Verification

- Direct foreground elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/CanonicalFreeInterventionPresentation.lean`
- Targeted leaf build only: `2997/2997` jobs passed
- Umbrella wiring: imported by `HTGeometry.UniversalLawField`; umbrella not built
- Axiom audit: eight significant declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`

## Exact remaining producer

First construct the stronger free observed two-field theorem: general routes may carry a source
rewrite boundary to a nonzero target rewrite boundary, so they do not factor through this flat
quotient. Then extract a literal divisor-independent intervention signature and proved relation
table shared by at least three structurally different route organs, retaining their rewrite
witnesses. Equip that chain-level source with a source-derived normed completion and prove the
ULF-TAFM-12 cofinal sublinear curvature--filling budget. No literal arithmetic factorization, norm,
RH premise, or RH claim is formalized here.
