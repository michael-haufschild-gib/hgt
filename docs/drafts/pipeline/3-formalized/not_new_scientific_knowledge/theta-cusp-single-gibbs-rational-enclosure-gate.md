# Theta-cusp single-Gibbs rational enclosure gate

- **ID:** `theta-cusp-single-gibbs-rational-enclosure-gate`
- **Stage:** 3-formalized
- **Type:** exact finite verification law
- **Scientific status:** source-specific formal bridge; novelty not claimed
- **Lean source:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaSingleGibbsRationalEnclosureGate.lean`
- **Statement:** One explicit finite list of rational moment enclosures forces both live
  first-atom source certificates and hence the complete linear trace-Hankel block.

## Positive finite gate

Let

\[
L_m=\int_0^\infty x^m e^{5x/2}e^{-\pi e^{2x}}\,dx.
\]

The theorem fixes rational lower and upper endpoints for `e^{-pi}` and `L_0,...,L_8`.  From those
enclosures alone, exact interval arithmetic proves both

\[
\left(14\left(\frac{3005}{2997}\right)^2-9\right)
(8L_3-L_4)^2U_G
\le
9(4L_1-L_2)
\left(8L_3-6L_4+\frac12L_5\right)^2
\]

and

\[
16\left(\frac{3005}{2997}\right)^2
(2e^{-\pi}-L_0)(8L_3-L_4)
\le45(4L_1-L_2)^2.
\]

Therefore every real linear-polynomial prime--archimedean trace-Hankel test is nonnegative.

This is the precise positive interface between analysis and the source-temperature route: a
successful proof may supply the stated enclosures by quadrature, special-function inequalities,
or a stronger structural estimate; after that, no additional low-degree physics argument is
needed.

## What remains open

The implication from the rational boxes is unconditional.  Existence of the enclosure package is
not yet proved.  The remaining analytic task is certified enclosure of one fixed positive
incomplete-Gamma moment fiber.  Moreover, this finite low-degree block is not the full cofinal
Hausdorff hierarchy equivalent to RH.

## Formal theorem surface

- `thetaCuspFirstAtomMorseFisherDecayFactor_rationalBounds`
- `thetaCuspFirstAtomSingleGibbsLowDegreeCertificate_of_rationalMomentEnclosure`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_singleGibbsRationalMomentEnclosure`

The module contains no project axioms or placeholders.
