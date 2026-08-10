# Controlled naturality and symmetry allocation -- Lean certification

- **ID:** ULF-CNM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/controlled-naturality-mechanics/orbit-complete-equivariance-export-curie-and-mark-stabilizer-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveControlledNaturalityMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [MECHANISM NOT OBJECT]
  [SYMMETRY ALLOCATION] [NOT RH]

## Certified declarations

- `OrbitCompleteReporter`, `EquivariantReporter`, and `ReporterEffectiveRelative`;
- `reporterEffectiveRelative_iff_symmetry_export`;
- `reporterDeterminedBy_iff_attained_fixed` and `invariantAttainedReporter_inert`;
- `input_stabilizer_le_output_stabilizer`;
- `JointlyEquivariantLaw` and `fixedMark_equivariant_under_stabilizer`;
- `orbitCompleteness_is_loadBearing` and `marking_is_not_sufficient`;
- `controlledNaturalityMechanics_closed`.

## Exact content

When old semantic fibres equal group orbits, an equivariant reporter changes legal execution exactly
when some symmetry moves an attained response. If every attained response is fixed, the reporter is
inert. Deterministic equivariance preserves point stabilizers. A jointly equivariant marked law,
after fixing its mark, remains equivariant under every symmetry stabilizing that mark.

Two unconditional scope cells prevent overclaim. Without orbit-completeness, an effective reporter
can have no moved target value. Conversely, a genuinely moved mark can feed a constant inert law.
Neither symmetry movement nor marking alone is law genesis.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveControlledNaturalityMechanics.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveControlledNaturalityMechanics
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Leaf build completes 8,665 jobs. Umbrella build completes 11,583 jobs. Axiom prints on symmetry
export, Curie inheritance, marked equivariance, both scope cells, and the closed capstone report at
most `propext`, `Classical.choice`, and `Quot.sound`; the attained-fixed equivalence reports no
axioms. No computation certificate or project axiom occurs.

## Field boundary

This certifies static symmetry allocation. Fixed reporters accumulate by stabilizer intersection,
so the theorem itself cannot produce path dependence. The open field law is endogenous allocation:
an earlier export or mark must change which later challenge the source can legally generate.
