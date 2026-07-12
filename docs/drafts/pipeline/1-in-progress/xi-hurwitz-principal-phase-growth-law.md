# Xi--Hurwitz principal-phase growth law

- **ID:** `xi-hurwitz-principal-phase-growth-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Hurwitz monodromy character values on the Xi divisor and the fixed-width rectangular Weil carrier

## Statement

For every Xi divisor point `rho` in the open critical strip, let

\[
q(\rho)=\exp(-2\pi i\rho).
\]

The open-strip branch removes the usual argument ambiguity:

\[
\operatorname{Arg}(-q(\rho))=-2\pi\left(\operatorname{Re}\rho-\tfrac12\right).
\]

Consequently, on the positive transverse Xi divisor,

\[
\sup_{\operatorname{Re}\rho>1/2}
  \frac{|\operatorname{Arg}(-q(\rho))|}{2\pi}
=\sup_{\operatorname{Re}\rho>1/2}
  \left(\operatorname{Re}\rho-\tfrac12\right)
=\delta_\Xi.
\]

For every fixed width `L>0`, the already formalized rectangular growth theorem identifies
`delta_Xi` with the sharp power exponent of the logarithmically sampled rectangular Weil values.
Thus the supremal principal phase of the Hurwitz monodromy character is exactly the sharp power
growth exponent of one scalar Weil sequence.

## Status registers

- [CONJECTURE] The exact principal-argument identity holds on the full open strip with no branch
  exception.
- [PROVED IN LEAN ELSEWHERE] The rectangular sharp power exponent equals `xiRightTransverseSup`
  whenever the positive transverse divisor is nonempty.
- [OPEN CORE] Formalize the principal-argument identity and identify the two suprema.
- [NOVELTY UNVERIFIED] The branch identity is standard complex analysis.  The coupled HGT-value /
  sharp-Weil-growth law requires a parent-theory and literature audit before any scientific-novelty
  claim.

## Positive boundary statement

When the positive transverse divisor is empty, every Xi zero is on the critical line and the
rectangular family is uniformly bounded.  The law therefore has a positive zero-phase boundary,
not a no-go branch.

