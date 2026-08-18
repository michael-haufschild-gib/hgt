# Ambidextrous Kummer doubling-defect selection law

- **ID:** ULF-DFPM-5-LC
- **Stage:** 3-formalized
- **Type:** LEAN-CERTIFIED FINITE FORMATION SELECTOR
- **Status:** [UNCONDITIONAL] [NO RH PREMISE] [NO ADDED AXIOMS] [SOURCE BIFLATNESS OPEN]

## Certified mechanism

For integer charge `q` and Kummer depth `n`, define the covariant doubling defect

\[
 \Delta_n(q)=[q]_{2n}-2[q]_{2n}=[-q]_{2n}.
\]

If `q` is nonzero and `n > |q|`, this class is nonzero.  Consequently

\[
 \bigl(\forall n>|q|,\ \Delta_n(q)=0\bigr)
 \quad\Longleftrightarrow\quad q=0.
\]

Thus one cofinal family of finite restriction/inclusion comparisons selects zero discrete charge
without a limiting estimate or analytic premise.

## Lean certificate

Module:

`GaloisForLFunctions.HTGeometry.ConstitutiveAmbidextrousKummerSelection`

Certified declarations:

- `ambidextrousDoublingDefect`;
- `ambidextrousDoublingDefect_eq`;
- `ambidextrousDoublingDefect_ne_zero`;
- `ambidextrousDoublingDefect_flat_iff`;
- `ambidextrousDoublingDefect_add`;
- `ambidextrousDoublingDefect_neg`;
- `ambidextrousKummerSelection_capstone`.

Scratch elaboration and direct leaf elaboration pass.  Targeted build of only this leaf passes.  The
leaf is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`; the umbrella was not built.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` where needed.

## Exact boundary

The certificate proves selection once simultaneous restriction/inclusion flatness is given.  It
does not construct source horizontalness, the three-depth crossed cocycle, the global regular
packet, or the meromorphic RH specialization.  The open field problem is to derive covariant
inclusion horizontalness from pre-zero source formation rather than impose it after observing a
divisor.
