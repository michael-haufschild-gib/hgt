# Involutive scattering optical master constraint

- **ID:** `involutive-scattering-optical-master-constraint`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** exact quantum-field-theory value relation / hypothesis discharge
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Usefulness gate:** replaces a quadratic master-constraint operator by an explicit linear
  scattering complement in both general HTGeometry and the concrete logarithmic Sonin model

## Claim

Let `U` be a bounded unitary operator and put `C = U - 1`.  Expanding `U†U = 1` gives the
bounded optical theorem

```text
C† C = 2 - U - U†.
```

If in addition `U² = 1`, then unitarity and involutivity force `U† = U`, so

```text
quantumMasterConstraint (U - 1) = 2 (1 - U).
```

The relation is static.  It uses no time flow, asymptotic limit, spectral computation, or
numerical experiment.

## Physics provenance

For an S-matrix written as `S = 1 + iT`, the unitarity relation `S†S = 1` is the optical theorem
`2 Im(T) = T†T`.  The first displayed identity is the same operator algebra with the defect
written directly as `C = U - 1`.  A primary modern QFT source is:

- D. Meltzer, E. Perlmutter, and A. Sivaramakrishnan, *Unitarity methods in AdS/CFT*, JHEP 03
  (2020) 061, arXiv:1912.09521, https://doi.org/10.1007/JHEP03(2020)061.  Equations (1.1)--(1.2)
  state `S†S = 1` and its optical-theorem form.  The paper develops the corresponding relation in
  AdS/CFT, so the source belongs to QFT/quantum gravity rather than RH literature.

## Direct corpus applications

1. `HTGeometry.quantumMasterConstraint_unitarySubOne_eq_two_sub_self_sub_adjoint` gives every
   bounded unitary constraint `U-1` an explicit positive master operator.  A consumer no longer
   has to expand adjoints or supply self-adjointness of `U`.
2. `HTGeometry.quantumMasterConstraint_involutiveScattering_eq_two_mul_complement` combines the
   optical theorem with the existing involutive-isometry lemma.  It discharges the adjoint
   hypothesis and proves that the quadratic master constraint contains exactly the same operator
   data as the anti-invariant sector `1-U`.
3. `RHTower.quantumMasterConstraint_soninLogFourierScattering_eq_two_mul_complement` applies the
   general theorem to the already formalized logarithmic Fourier scattering involution.
4. This retires one false strengthening route: positivity of the Sonin scattering master
   constraint cannot by itself yield information beyond control of the anti-invariant scattering
   sector, because the two operators are exact scalar multiples.
5. Together with the existing fixed-sector average and its norm partition, the result puts the
   physical projection, rejected-sector energy, and master-constraint language on one exact
   interface.  Future Ward or source estimates can choose the cheapest form without comparison
   constants.

## Formal surface

- `quantumMasterConstraint_unitarySubOne_eq_two_sub_self_sub_adjoint`
- `quantumMasterConstraint_involutiveScattering_eq_two_mul_complement`
- `quantumMasterConstraint_soninLogFourierScattering_eq_two_mul_complement`

## Verification boundary

- isolated source check of `FiniteConstraintGroupAverage.lean`: passed (three pre-existing style
  warnings only);
- isolated source check of `SoninLogCoordinateScattering.lean`: passed with no diagnostics;
- targeted module builds of `FiniteConstraintGroupAverage` and
  `SoninLogCoordinateScattering`: passed;
- `#print axioms` for both the general involutive-scattering theorem and the Sonin specialization
  reports only `propext`, `Classical.choice`, and `Quot.sound`;
- numerical scripts: none.
