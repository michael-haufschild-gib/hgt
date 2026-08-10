# Prospective separation, plateau, observer delay, and completion — Lean certification

- **ID:** ULF-PCG-1
- **Paper card:**
  `../../../2-fully-proven/universal-law-field/prospective-challenge-geometry/prospective-separation-filtration-plateau-observer-delay-and-completion-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveProspectiveChallengeGeometry`
- **Status:** [LEAN-PROVED CORE] [UNCONDITIONAL] [ROUTE-INDEPENDENT] [NOT RH]

## Certified mechanism

For arbitrary sets, two unary context generators, and arbitrary reporters, Lean certifies:

1. word depth and finite-horizon prospective agreement;
2. equivalence and horizon monotonicity;
3. left/right context-shift laws;
4. equality of all finite horizons with the full future reporter kernel;
5. permanent stabilization after one exact plateau;
6. postobserver data processing and exact preservation under injective postobservation;
7. the three-state sharp delayed-exposure cell;
8. finite realization of every all-true horizon by finite Boolean lists;
9. global nonrealization of the all-true coherent history;
10. coordinatewise convergence of finite source signatures to that history;
11. product-topology closure membership outside the source image; and
12. `constitutiveProspectiveChallengeGeometry_closed`, the unconditional capstone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveProspectiveChallengeGeometry.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveProspectiveChallengeGeometry
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Direct elaboration is warning-free. The owned-module build passes with `8,667` jobs; the final
Universal Law Field umbrella build passes with `11,568` jobs. Source-level axiom prints report
either no axioms or only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. No project
axiom, placeholder, unsafe declaration, computation certificate, route premise, or RH premise is
used.

Repository-wide formal lint still reports five unrelated pre-existing unreachable modules in
`RHTower`/`HTGeometry`; neither ULF-PCG module is among them.

## Exact scope

The numerical prefix pseudoultrametric is not counted as Lean-certified. Certified content is the
prospective filtration, permanent plateau, observer delay, finite/global realization gap, and
product-topology completion witness. No grammar-update producer, partial admission, positivity,
cost, hypertranscendence, or arithmetic landing is asserted.
