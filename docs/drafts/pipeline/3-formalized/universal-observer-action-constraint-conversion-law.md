# Universal observer-action constraint-conversion law

- **ID:** `universal-observer-action-constraint-conversion-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL FINITE-CARRIER CONSERVATION LAW
- **Date:** 2026-07-31
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/UniversalObserverActionConstraintConversionLaw.lean`

## Exact law

Fix any finite projective phase carrier. For any two valid completed
observer-action laws on that carrier,
\[
  \boxed{\tau_0+\rho_0=\tau_1+\rho_1,}
\]
where \(\tau_j\) is operational temporal dimension and \(\rho_j\) is the
rational rank of zero-action projective relations. Each side equals the
complete projective character capacity.

If \(\tau_0\le\tau_1\), then
\[
  \boxed{\tau_1-\tau_0=\rho_0-\rho_1.}
\]

Zero-action relations are exactly the almost-sure phase constraints of the
completed law. The theorem therefore applies to arbitrary observer choices,
clock scalings and action-regime limits. It does not require a Hamiltonian
model, analytic perturbation parameter, inverse-power clock, genericity or
arithmetic independence.

## Formal declarations

- `observerAction_temporalCapacity_conserved`;
- `observerAction_temporalDimension_sub_eq_zeroConstraintRank_sub`;
- `observerAction_phaseConstraintCapacity_conserved`.

## Relation to interaction

Weak interaction is one physical mechanism that changes the zero-action
kernel. The separable-interaction and fixed-hopping Anderson theorems supply
explicit Hamiltonian realizations that convert the complete initial kernel
to temporal dimension.

## Verification

Foreground target compilation passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/UniversalObserverActionConstraintConversionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/UniversalObserverActionConstraintConversionLaw.olean
```

The scratch axiom audit reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.
