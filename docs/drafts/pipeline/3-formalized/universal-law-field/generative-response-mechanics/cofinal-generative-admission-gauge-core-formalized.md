# Cofinal generative admission gauge core -- Lean certification

- **ID:** ULF-GRM-2
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/generative-response-mechanics/cofinal-generative-admission-gauge-and-three-cone-data-processing-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.CofinalGenerativeAdmission`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED CORE] [NO PROJECT AXIOMS] [INFINITE/COFINAL] [NOT RH]

## Certified mechanism

Lean certifies the mechanism separating finite observer legality from executable global motion:

1. admission at scale `epsilon` is exactly domination at reciprocal scale `epsilon⁻¹`;
2. positive linear comparisons preserve every admitted scale and dominating coefficient, so they
   cannot create an admission obstruction;
3. finite-aperture admission is equivalent to inward motion at every absent coordinate;
4. full straight admission implies finite admission, but the converse fails cofinally;
5. an explicit geometric probability carrier has total mass one and a tangent of total mass zero,
   passes every finite aperture, yet admits no positive global straight-line scale.
6. a jointly positivity-reflecting observer family reconstructs admission and domination exactly;
   failure at a fixed scale must appear in at least one observer, although the witness may migrate
   with scale.

The last declaration is the fourth-organ prediction in certified form: every finite diagonal Gram
aperture is strictly positive for some common local scale, while the full countable diagonal family
has zero global perturbation radius.

## Certified declarations

- `admittedAt_iff_dominatedAt_inv`;
- `finitelyAdmitted_iff_contingentlyLegal`;
- `admittedAt_map`, `dominatedAt_map`, and `positiveLinearMap_comp`;
- `cofinalAdmission_collapse`;
- `probabilityAdmissionBase_hasSum` and `probabilityAdmissionTangent_hasSum`;
- `probabilityAdmission_finitelyAdmitted`;
- `probabilityAdmission_not_straightAdmitted`;
- `probabilityAdmission_conservative_cofinal_collapse`.
- `admittedAt_iff_forall_map` and `dominatedAt_iff_forall_map`;
- `exists_map_not_admittedAt`;
- `coordinateAdmissionObserver_jointlyReflects`;
- `probabilityAdmission_migrating_obstruction`.

## Formal boundary

The paper's exact `ell^1` norm-closure identity and Fourier uniqueness reporter are not yet
formalized. This card certifies the load-bearing admission/data-processing mechanism, exact
finite-versus-cofinal separation, conservation law, and spectral prediction. It does not label the
entire paper card Lean-complete.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/CofinalGenerativeAdmission.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

The final umbrella build passes 11,610 jobs. A `/tmp` axiom audit of reciprocal feasibility,
finite/contingent equivalence, positive-map transport, both cofinal collapse capstones, and the
conserved probability theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
Repository lint passes. No `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, or computation
certificate occurs.
