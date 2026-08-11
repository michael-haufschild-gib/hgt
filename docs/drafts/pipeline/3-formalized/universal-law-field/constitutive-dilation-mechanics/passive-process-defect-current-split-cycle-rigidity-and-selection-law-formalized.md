# Passive process defect current, split-cycle rigidity, and selection law -- Lean certification

- **ID:** ULF-CDM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/constitutive-dilation-mechanics/passive-process-defect-current-split-cycle-rigidity-and-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutivePassiveCycleMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-PROVED] [NO PROJECT AXIOMS] [MECHANISM CORE] [NOT RH]

## Certified declarations

- `workDefect`;
- `workDefect_comp`;
- `passiveDefect`;
- `passiveDefect_nonneg_iff`;
- `passiveDefect_comp`;
- `passive_split_cycle_norm_eq`;
- `passive_split_cycle_defects_eq_zero`;
- `passive_three_cycle_defects_eq_zero`;
- `neutral_of_passive_split_cycle`;
- `no_positive_defect_in_passive_three_cycle`.

## Exact content

Heterogeneous work defects telescope under composition.  Norm-passive two- and three-leg cycles
with exact return preserve work on every leg, so every passive defect vanishes.  Any independently
proved strict detector whose zero locus is neutral therefore selects that neutral locus.

The theorem does not construct a source work, compression, or passive reconstruction.  It certifies
the rigidity law those data would trigger and therefore leaves literal source formation as the
open mathematical gate.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePassiveCycleMechanics.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutivePassiveCycleMechanics
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Direct elaboration passes.  Leaf build completes 1,666 jobs; umbrella build completes 11,830 jobs.
Scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the headline
theorems.  No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, computation certificate, RH premise,
or zero-location specialization occurs.
