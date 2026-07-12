# The continued Xi source factors through the critical Mellin defect

- **ID:** `xi-critical-mellin-source-factorization`
- **Stage:** 3-formalized
- **Type:** THEOREM / TOP-DOWN VALUE-RELATION BRIDGE
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiCriticalMellinSourceFactorization.lean`

## Statement

Put

\[
u(z)=-\frac12+iz,
\qquad
\mathcal D(u)=\frac1u+\frac1{u+1}
  +\frac{\zeta'(u+1)}{\zeta(u+1)}.
\]

On `Re u>0`, `D` is exactly the convergent polar channel minus the von Mangoldt channel already
formalized in `CCMComplexMellinColligation.lean`.  The same formula defines its canonical
meromorphic source continuation.  For every centered coordinate `z`, the continued prime--Gamma
relative trace satisfies the exact value relation

\[
T(z)=-i\left[
  \left(\frac1{u(z)}+\frac1{u(z)+1}\right)
  -\mathcal D(u(z))
  -\frac{A'(1/2+iz)}{A(1/2+iz)}
\right],
\]

where `A=archFactor`.  Therefore the RH-bearing continued Cauchy kernel is

\[
K_T(z,w)=
\frac{T(\overline w)-T(z)}{z-\overline w}
=
\frac{T_{\mathrm{polar}-\mathcal D-\Gamma}(\overline w)
      -T_{\mathrm{polar}-\mathcal D-\Gamma}(z)}
     {z-\overline w}.
\]

No Xi zero, zero ordering, positivity premise, limiting measure, or RH hypothesis enters these
identities.

## Top-down consequence

The open source-kernel problem is no longer an unidentified bridge between the CCM critical
Mellin channel and the continued Xi Cauchy kernel.  More importantly, expanding the
archimedean logarithmic derivative shows that the apparent polar background does not furnish an
independent positive majorant.  Write

\[
\Delta_f(z,w)=\frac{f(\overline w)-f(z)}{z-\overline w},
\quad B(z)=\frac1{u(z)}+\frac1{u(z)+1},
\quad G(z)=\frac{A'(1/2+iz)}{A(1/2+iz)}.
\]

On the regular source domain, the identity

\[
\frac{A'(s)}{A(s)}=\frac1s+\frac1{s-1}+\Gamma_{\mathbb R}(s),
\qquad s=\frac12+iz,
\]

and `u=s-1` give exact cancellation of `B`.  Hence

\[
T(z)=i\bigl(\mathcal D(-\tfrac12+iz)+\Gamma_{\mathbb R}(\tfrac12+iz)\bigr).
\]

Therefore the previously proposed theorem “the critical-Mellin defect is dominated by the explicit
polar--Gamma background” is not an independent route.  After cancellation, its divided-difference
form is exactly positivity of the full continued Xi source kernel.  This is an RH-bearing sign
criterion in source coordinates, not a source-side discharge of that sign.

The positive theorem retained here is the exact reduced value relation: the continued source is the
sum of the critical Mellin defect and the Gamma connection.  Any future source proof must exploit
additional structure of that coupled sum; it cannot treat the displayed polar contribution as an
external positive reserve.

## Formal certificate

The module proves:

- `criticalMellinDefectLaplaceChannelComplex_eq_continued`;
- `continuedPrimeArchSourceRelativeTrace_eq_continuedPolarMellinArch`;
- `ccmContinuedCauchyKernel_eq_continuedPolarMellinArch_dividedDifference`;
- `continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma`;
- `ccmContinuedCauchyKernel_eq_continuedMellinGamma_dividedDifference`.

The standalone Lean module and named Lake target compile.  `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`; the declarations use no project axiom, `sorry`, `admit`,
`opaque`, or `unsafe` declaration.

## Gates

- [x] convergent complex Mellin defect identified with its continued source expression
- [x] continued prime--Gamma trace factored globally through that expression
- [x] RH-bearing continued Cauchy kernel rewritten as its exact divided difference
- [x] polar boundary terms cancelled exactly against the archimedean rational terms on the regular
  source domain
- [x] retire polar--Gamma domination as an independent RH mechanism
- [ ] find genuinely additional source structure forcing positivity of the reduced coupled source
