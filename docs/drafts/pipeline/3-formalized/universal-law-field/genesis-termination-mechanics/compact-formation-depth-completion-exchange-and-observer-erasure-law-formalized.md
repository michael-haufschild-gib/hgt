# Compact formation depth and completion exchange — Lean certificate

- **ID:** ULF-GTM-3
- **Stage:** 3-formalized
- **Paper theorem:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/genesis-termination-mechanics/compact-formation-depth-completion-exchange-and-observer-erasure-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFormationCompletionExchange`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified content

Lean proves, unconditionally:

1. finite-depth reach for point formations through finite words;
2. closure commutes with every bounded word depth for finite continuous formation families on a
   compact Hausdorff space;
3. completed finite-word saturation is the least closed invariant law space;
4. completion boundary equals closure of the filtered union minus union of stage closures;
5. every neighbourhood of a boundary law contains effective realizations beyond every fixed word
   depth;
6. bounded-depth saturation makes the boundary empty;
7. generator dictionaries multiply depth by at most their maximum word length;
8. mutual dictionaries preserve generated law spaces and completion boundaries;
9. continuous equivariant observers can erase but cannot create boundaries, and injective
   observers preserve them exactly;
10. infinitely many continuous constant generators on the one-point compactification of `ℕ`
    violate completion exchange already at depth one.

## Significant declarations

```lean
boundedFormationReach_closure
closure_formationSaturation_least
formationCompletionBoundary_eq_limitExchange
completionBoundary_nhds_exists_beyond
formationCompletionBoundary_eq_empty_of_bounded_saturation
boundedFormationReach_subset_of_dictionary
formationCompletionBoundary_eq_of_mutual_dictionaries
observer_completionBoundary_subset
observer_completionBoundary_eq_of_injective
infiniteSignature_depthOne_completionExchange_fails
```

## Verification

- direct foreground elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFormationCompletionExchange.lean`;
- forbidden-token lint: `scripts/formal_tools.py lint`;
- axiom audit: only Lean/mathlib foundations are admitted;
- final umbrella audit:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`.

Final umbrella audit completed 11,430 jobs successfully. No `sorry`, `admit`, new `axiom`,
`opaque`, `unsafe`, or computational certificate is used. `#print axioms` on every audited
capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
