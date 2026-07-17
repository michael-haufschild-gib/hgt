# Kerr--Newman charged-scalar Gamma-response lattice boundary

- **ID:** `kerr-newman-charged-scalar-gamma-response-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM / direct physics specialization
- **Status:** `[PROVEN]` exact Gamma value relation, DA/HT lattice classification, neutral polynomial collapse, and logarithmic-clock boundary formalized in Lean
- **Source:** L. Ma, Z.-H. Wu, Y. Pang, and H. Lu, *Charging the Love numbers: Charged scalar response coefficients of Kerr-Newman black holes*, arXiv:2408.10352v2, equations (4), (21), and (33)

## Claim

Write the effective multipole gap as

\[
  \Delta=1+2L=\sqrt{(2\ell+1)^2-4(q_eQ)^2}.
\]

After removing factors independent of the complexified frequency coordinate `z`, the response
coefficient in equation (21) has the exact variable Gamma core

\[
  K_\Delta(z)=
  \frac{\Gamma\left(z+(1+\Delta)/2\right)}
       {\Gamma\left(z+(1-\Delta)/2\right)}.
\]

This is the existing reduced same-orientation Gamma quotient with channel shift `-Delta`.
Therefore:

1. `K_Delta` is differentially algebraic over `C(z)` exactly when `Delta` is an integer.
2. It is hypertranscendental exactly when `Delta` is not an integer.
3. In the neutral mode `Delta=2*ell+1`, it is exactly the finite Pochhammer polynomial
   `prod_{j=0}^{2*ell} (z-ell+j)`, matching the polynomial collapse displayed in equation (33).
4. Its logarithmic response clock is exactly
   `digamma(z+(1+Delta)/2)-digamma(z+(1-Delta)/2)` and is HT exactly off the same integer lattice.

The selector is the observable's effective-multipole translation gap, not the temporal evolution
of the perturbation.

## Positive content of the exceptional sector

The integer-lattice no-go does not end at “not HT.”  It identifies the complete response core as
an explicit rational polynomial and therefore gives a finite algebraic realization.  Moving the
charged scalar off that lattice does not merely complicate coefficients: it changes the
differential-algebraic class of the frequency observable.

## Corpus target

- specialize `reducedVenezianoAmplitudeMero` to the Kerr--Newman shifts;
- reuse `differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift`;
- reuse `hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift`;
- reuse `reducedVenezianoAmplitudeMero_negSuccShift` for the neutral polynomial normal form.

All four targets are discharged.  The principal declarations are:

- `kerrNewmanChargedScalarGammaResponseMero_eq_gammaRatio`;
- `differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap`;
- `hypertranscendentalOver_kerrNewmanChargedScalarGammaResponseMero_iff_nonintegerGap`;
- `differentialAlgebraicOver_kerrNewmanChargedScalarPhysicalGammaResponseMero_iff`;
- `hypertranscendentalOver_kerrNewmanChargedScalarPhysicalGammaResponseMero_iff`;
- `kerrNewmanNeutralScalarGammaResponseMero_eq_pochhammer`;
- `kerrNewmanChargedScalarLogResponseClockMero_eq_digammaDifference`;
- `hypertranscendentalOver_kerrNewmanChargedScalarLogResponseClockMero_iff_nonintegerGap`.

## RH pressure test

This supplies no zero-location mechanism.  It does add a sharp route discriminator: a physical
Gamma response may cross between finite DA and HT observability when a spectral/multipole gap
leaves an integer lattice.  Any RH construction importing such a response must retain the gap
parameter; treating the response as a generic “Gamma factor” loses the exact source boundary.

## Lean certificate and verification

- `formal/GaloisForLFunctions/HTGeometry/KerrNewmanChargedScalarGammaBoundary.lean`
- [x] exact missing-module `:olean` target built with cached dependencies, one process
- [x] direct source check, one process
- [x] six capstone axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`
- [x] source contains no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` token
- [x] no numerical computation and no full build
