# Xi thermal quartet relative-gap bound

- **ID:** xi-thermal-quartet-relative-gap-bound
- **Status:** `[PROVED]` unconditionally and formalized.
- **Route:** Connes / completed prime--Gamma / Born--Witten--KMS.
- **Scientific status:** `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`.

## Theorem

Let

\[
C=2+\gamma_E-\log(4\pi),
\qquad
\kappa_4(C)=\frac{16C(4-C)}{(16-5C)^2}.
\]

For every Xi-zero copy, the transverse reciprocal-square coordinate vanishes on the critical
line.  Off the line, functional-equation and Schwarz symmetry charge four distinct zero copies,
and the endpoint budget gives

\[
\gamma^2\ge \frac{4-C}{C}.
\]

Writing

\[
u=(\beta-\tfrac12)^2,
\qquad v=\gamma^2,
\]

the exact transverse-to-node ratio satisfies

\[
\frac{4uv}{(v-u)^2}
\le
\frac{16C(4-C)}{(16-5C)^2}
=\kappa_4(C).
\]

Since (C<93/2000),

\[
0\le\kappa_4(C)<
\kappa_4(93/2000)
=\frac{11765616}{994456225}
<\frac1{84}.
\]

After summation over the complete divisor,

\[
\mathcal E_\perp
\le\kappa_4(C)M_2
<\frac1{84}M_2.
\]

Using the exact source-gap identity

\[
M_2-\mathcal E_\perp=\mathcal Q_W,
\]

one obtains the unconditional source-retention interval

\[
\frac{83}{84}M_2<\mathcal Q_W\le M_2
<\frac{84}{83}\mathcal Q_W.
\]

The positive theorem is that the explicit theta Born--Witten source carries more than (83/84)
of the complete reciprocal-square thermal mass.  A successful endpoint construction must carry
the remaining transverse orientation coordinate and force its saturation to zero.

## Proof mechanism

The relative ratio is increasing in (u\in[0,1/4]) and decreasing with the allowed height floor.
Its extremal upper bound is therefore reached at

\[
u=\frac14,
\qquad
v=\frac{4-C}{C}.
\]

This produces (kappa_4(C)).  The exact rational endpoint certificate makes the numerical bound
purely algebraic.  Atomwise domination and absolute summability then give the global energy
bound.

## Exact open core

The theorem is strict quantitative progress on the missing source estimate, but it does not prove
RH.  The endpoint saturation

\[
M_2\le\mathcal Q_W
\]

is still required; together with the unconditional reverse inequality it is equivalent to
\(\mathcal E_\perp=0\) and hence RH.

## Formal artifact

- `formal/GaloisForLFunctions/RHTower/XiThermalQuartetRelativeGapBound.lean`

Principal declarations:

- `xiThermalQuartetRelativeOrientationFactor`;
- `xiThermalQuartetRelativeOrientationFactor_eq_boundaryRatio`;
- `xiThermalQuartetRelativeOrientationFactor_lt_one_eightyFourth`;
- `xiThermalOrientationTerm_le_quartetRelativeFactor_node_sq`;
- `xiThermalOrientationEnergy_le_quartetRelativeFactor_secondMoment`;
- `xiThermalOrientationEnergy_lt_one_eightyFourth_secondMoment`;
- `eightyThree_over_eightyFour_thermalSecondMoment_lt_source`;
- `xiThermalSecondMoment_lt_eightyFour_over_eightyThree_source`.

The module contains no placeholders.  Axiom inspection reports only `propext`,
`Classical.choice`, and `Quot.sound`.
