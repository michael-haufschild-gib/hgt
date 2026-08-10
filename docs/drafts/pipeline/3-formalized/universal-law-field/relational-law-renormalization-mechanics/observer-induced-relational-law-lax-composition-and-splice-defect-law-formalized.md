# Observer-induced relational law, lax composition, and splice defect — Lean certification

- **ID:** ULF-RLR-1
- **Paper card:**
  `../../../2-fully-proven/universal-law-field/relational-law-renormalization-mechanics/observer-induced-relational-law-lax-composition-and-splice-defect-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveRelationalLawRenormalization`
- **Status:** [LEAN-PROVED] [AXIOM-FREE] [UNCONDITIONAL] [ROUTE-INDEPENDENT]
  [MECHANISM NOT OBJECT] [NOT RH]

## Certified mechanism

For arbitrary sets, deterministic source laws, and observer maps, Lean certifies:

1. canonical observer-induced effective relations;
2. identity and total relational survival under surjective observation;
3. right-uniqueness exactly when source law preserves observer kernel;
4. existence and uniqueness of deterministic descended law in that chamber;
5. lax effective execution;
6. exact execution when later law preserves observer kernel;
7. constant-prelaw converse detecting kernel preservation;
8. strict relation pushforward under serial observation;
9. every deterministic selector misses some source transition at a branched input;
10. strict four-state splice and branch creation/erasure cells;
11. direct-image composition inclusion;
12. direct image preserves all relation compositions exactly iff observer is injective;
13. two-defect serial observation--execution interchange filtration;
14. exact first layer under later-law descent;
15. two unconditional four-state cells proving defect layers independent;
16. `relationalLawRenormalization_unconditional`; and
17. `relationalLawInterchange_unconditional`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveRelationalLawRenormalization.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveRelationalLawRenormalization
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Direct elaboration passes. Leaf build passes with 2,998 jobs. Final Universal Law Field umbrella
build passes with 11,574 jobs. Axiom audit reports **no axioms** for descent classification,
pushforward exactness, interchange filtration, both independence cells, and both capstones. No
project axiom, placeholder, unsafe declaration, computation certificate, route premise, or RH
premise is used.

## Exact scope

This is set-level relational mechanics. It proves no topology, closure, convexification,
probabilistic selection, recurrence, hypertranscendence, physical time, source-normal selector, or
RH theorem. It supplies the strict anti-theatre gate: any serial quotient/execution chart must
separate source-execution splice from observer-midpoint splice before assigning one scalar defect.
