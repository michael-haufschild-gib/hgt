# Observer-unitization pump law — Lean certification

- **ID:** ULF-PRD-PUMP-1
- **Paper card:**
  `observer-unitization-recurrence-open-history-and-cost-nondescendence-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveObserverUnitization`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `constitutiveHistoryAction_pow`: exact linear action on powers.
- `constitutiveObserverUnitization_pow`: exact identity observation of all powers.
- `constitutivePositiveHistory_pow_injective`: positive action makes lifted power history injective.
- `constitutiveObserverUnitization_cost_not_descend`: action cannot factor through unitizing observer.
- `constitutiveObserverUnitization_pump`: bundled recurrence/open-history/action/nondescendence law.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveObserverUnitization.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveObserverUnitization
```

Targeted build completed successfully. `#print axioms` reports no axioms for observer return and
cost nondescendence, and only `propext` for remaining declarations. Module is imported by dedicated
universal-law-field umbrella. No project postulate or computation proof is used.

## Exact field consequence

One observer-localization event can generate four organs from one history: recurrent observation,
open lifted history, positive linear action, and provable cost nondescendence. Curvature, metric,
covering-space, and route-specific data are unnecessary.
