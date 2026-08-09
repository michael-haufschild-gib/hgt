# Finite-jet realization boundary — Lean certification

- **ID:** ULF-RBD-JET-1
- **Paper card:**
  `finite-jet-realization-boundary-and-continuous-classifier-no-go.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFiniteJetBoundary`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### `constitutiveFiniteJet_noContinuousBoolClassifier`

Closed theorem: no continuous Boolean-valued map on the finite-jet topology can assign one value to
all differentially algebraic laws and the other value to all hypertranscendental laws.

### `constitutiveFiniteJet_realizationBoundary_law`

Closed conjunction certifying:

1. every prescribed finite jet has both a differentially algebraic and a hypertranscendental exact
   realization;
2. both law classes are dense in finite-jet topology;
3. both have empty interior;
4. both are nonclosed;
5. continuous Boolean classification is impossible.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFiniteJetBoundary.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFiniteJetBoundary
```

Targeted build completed successfully. `#print axioms` lists only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, or computation proof is used
in the module.

## Exact scope

Formalization certifies observer-topological nonseparation. It does not equate
hypertranscendence with orbit noncompactness, add a physical cost, or construct an arithmetic
source landing.
