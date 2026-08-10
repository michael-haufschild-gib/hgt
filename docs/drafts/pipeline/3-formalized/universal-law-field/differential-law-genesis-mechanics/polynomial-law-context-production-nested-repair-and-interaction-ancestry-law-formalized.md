# Polynomial law context production and interaction ancestry — Lean certification

- **ID:** ULF-DLG-1
- **Paper card:**
  `../../../2-fully-proven/universal-law-field/differential-law-genesis-mechanics/polynomial-law-context-production-nested-repair-and-interaction-ancestry-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveLawDerivativeGenesis`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

For arbitrary same-universe set-level polynomial law signatures, Lean certifies:

1. `LawContainer`, `Extension`, and `OneHoleContext`;
2. `contextOfMarked`, `plug_at_hole`, and `plug_away`;
3. `plug_contextOfMarked_restore` — a marked execution canonically produces a restorative context;
4. `CompositeExtension`, `CompositeSite`, `outerFailureContext`, and `innerFailureContext`;
5. `nestedRepair_original` — nested inner/outer plugging restores the complete composite;
6. `nestedRepair_outer_away` — repair leaves every unrelated outer branch fixed;
7. `failurePair_interaction_partition` — every failure pair is exclusively same-outer or
   split-outer;
8. `ancestry_blind_observer_identifies_interactions` together with the same/split witness theorems;
9. `constitutiveLawDerivativeGenesis_closed` — unconditional capstone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveLawDerivativeGenesis.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveLawDerivativeGenesis
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Direct elaboration and the owned-module build pass without warnings. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. No project axiom, `sorry`, `admit`, `opaque`,
`unsafe`, numerical computation, or unresolved premise is used.
Final `GaloisForLFunctions.HTGeometry.UniversalLawField` build passes with `11,558` jobs. Replayed
warnings belong to unrelated imported modules; the new module is warning-free.

## Exact scope

Container derivatives, zippers, polynomial functors, and one-hole contexts are classical parents.
The certified delta is their use as a route-independent failure-to-challenge mechanism with an
exact ancestry-erasure no-go. The theorem derives context and repair location, not the replacement
value, semantic effectiveness, presentation invariance, higher Faà-di-Bruno partition, positivity,
recurrence, hypertranscendence, or an RH result.
