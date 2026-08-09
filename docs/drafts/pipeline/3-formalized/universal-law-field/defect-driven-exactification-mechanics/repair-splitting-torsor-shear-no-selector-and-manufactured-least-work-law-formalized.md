# Repair splitting torsor and manufactured least-work no-go -- Lean certification

- **ID:** ULF-DDE-1
- **Stage:** 3-formalized
- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/defect-driven-exactification-mechanics/repair-splitting-torsor-shear-no-selector-and-manufactured-least-work-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveRepairTorsorSelectorNoGo`
- **Status:** [LEAN-PROVED] [UMBRELLA-WIRED] [NO SORRY] [NO ADDED AXIOMS]

## Certified declarations

### Algebraic repair torsor

- `constitutiveRepairProjection_section`;
- `constitutiveRepairProjection_shear`;
- `constitutiveRepairSection_classification`;
- `constitutiveRepairSection_injective`;
- `constitutiveRepairShear_section`;
- `constitutiveRepairShear_transitive`;
- `constitutiveRepairShear_section_eq_iff`;
- `constitutiveRepairShear_no_fixed_section`.

### Manufactured least-work selector

- `constitutiveRepairCost_section`;
- `constitutiveRepairCost_decomposition`;
- `constitutiveRepairCost_minimal`;
- `constitutiveRepairCost_eq_min_iff`;
- `constitutiveEveryRepairSelector_isManufacturedUniqueMinimum`.

## Verification

- direct source elaboration passed;
- final foreground umbrella build
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed 11,415 jobs;
- forbidden-token scan found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
  `native_decide`;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical boundary

Lean proves the no-go, not a universal selector. Exact repair data yield an affine torsor, and an
arbitrary selector can always be made uniquely optimal by a centered positive squared-norm cost.
The active field problem is therefore source-revealed work integrability: deriving a cost law from
intervention response before optimization.

## Log

- 2026-08-09 -- paper theorem translated exactly; umbrella and axiom audits passed.
