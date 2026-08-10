# Descent-breaking grammar extension and definability barrier — Lean certification

- **ID:** ULF-PCG-2
- **Paper card:**
  `../../../2-fully-proven/universal-law-field/prospective-challenge-geometry/descent-breaking-grammar-extension-and-definability-barrier-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveDescentBreakingGrammarExtension`
- **Status:** [LEAN-PROVED] [UNCONDITIONAL] [ROUTE-INDEPENDENT] [NOT RH]

## Certified mechanism

For arbitrary sets, old context generators `f,g`, a proposed fresh generator `h`, and arbitrary
reporters, Lean certifies:

1. three-generator context words and execution;
2. embedding of old words and exact execution preservation;
3. equivalence and generator preservation of the extended future kernel;
4. conservative inclusion of the extended kernel in the old kernel;
5. the exact law
   `h preserves old future kernel ↔ extended kernel = old kernel` pointwise;
6. the strict-refinement form
   `not preservation ↔ strict prospective refinement`;
7. a finite old-context witness after every descent-breaking fresh action;
8. concatenation semantics for old words;
9. every old-word-definable operation preserves the old future kernel and causes no refinement;
10. a three-state source-effective grammar birth;
11. erasure of that birth by constant postobservation; and
12. `constitutiveDescentBreakingGrammarExtension_closed`, the unconditional capstone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDescentBreakingGrammarExtension.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveDescentBreakingGrammarExtension
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Direct elaboration is warning-free. The owned-module build passes with `8,661` jobs; the final
Universal Law Field umbrella build passes with `11,568` jobs. Source-level axiom prints report
either no axioms or only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. No project
axiom, placeholder, unsafe declaration, computation certificate, route premise, or RH premise is
used.

Repository-wide formal lint still reports five unrelated pre-existing unreachable modules in
`RHTower`/`HTGeometry`; neither ULF-PCG module is among them.

## Exact scope

This theorem tests effectiveness of a supplied grammar extension. It does not generate `h`, prove
minimality among several descent breakers, handle partial/higher-arity/pro operations, or provide a
source-normal update law. That production mechanism remains the field frontier.
