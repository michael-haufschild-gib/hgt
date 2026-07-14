# Xi thermal/source relative-gap bound

- **ID:** `xi-thermal-source-relative-gap-bound`
- **Stage:** 3-formalized
- **Type:** `[PROVEN] [FORMALIZED] [NOVELTY UNVERIFIED] [RH ESTIMATE PROGRESS]`
- **Formal source:** `XiThermalSourceRelativeGapBound.lean`

## Theorem

Let

\[
C=2+\gamma-\log(4\pi),
\qquad
\lambda_\rho=-\frac1{(\rho-\tfrac12)^2},
\qquad
x_\rho=\Re\lambda_\rho,
\]

with the Xi divisor counted with analytic multiplicity.  The completed endpoint source satisfies

\[
0<C<\frac2{43},
\qquad
2<(\Im\rho)^2
\]

for every nontrivial Xi zero.  Define

\[
\kappa(C)=\frac{16C(1-C)}{(4-5C)^2}.
\]

Then

\[
0\le \kappa(C)<\frac1{20}<1
\]

and the atomwise reciprocal-square orientation estimate is

\[
(\Im\lambda_\rho)^2\le \kappa(C)(\Re\lambda_\rho)^2.
\]

Consequently, for

\[
M_2=\sum_\rho x_\rho^2,
\qquad
\mathcal E_\perp=\sum_\rho(\Im\lambda_\rho)^2,
\qquad
\mu_1=\Re\sum_\rho\lambda_\rho^2,
\]

the exact source-gap identity and the new relative estimates are

\[
M_2-\mathcal E_\perp=\mu_1,
\qquad
\mathcal E_\perp\le\kappa(C)M_2,
\]

\[
(1-\kappa(C))M_2\le\mu_1\le M_2,
\qquad
M_2\le\frac{\mu_1}{1-\kappa(C)}<\frac{20}{19}\mu_1.
\]

Equivalently,

\[
\mathcal E_\perp<\frac1{20}M_2,
\qquad
\frac{19}{20}M_2<\mu_1\le M_2<\frac{20}{19}\mu_1.
\]

In particular,

\[
M_2>0,
\qquad
\mu_1>0.
\]

## Born/Witten source form

For the exact theta Born/Witten amplitudes `chi_n`, put

\[
W_j=\sum_{n\ge1}2\pi\int_0^\infty x^{2j}\chi_n(x)^2\,dx
\]

and

\[
\mathcal Q_W=rac12\left(\frac{W_1}{W_0}\right)^2
-\frac16\frac{W_2}{W_0}.
\]

Then `W_j` is the complete theta-cusp raw moment and

\[
\mu_1=\mathcal Q_W>0.
\]

Therefore the full source/divisor incidence is

\[
M_2-\mathcal E_\perp=\mathcal Q_W,
\qquad
\mathcal Q_W\le M_2\le
\frac{\mathcal Q_W}{1-\kappa(C)}.
\]

More sharply,

\[
\frac{19}{20}M_2<\mathcal Q_W\le M_2
<\frac{20}{19}\mathcal Q_W.
\]

The exact endpoint remains

\[
\mathrm{RH}
\iff M_2=\mathcal Q_W
\iff M_2\le\mathcal Q_W
\iff M_N(1)\longrightarrow\mathcal Q_W.
\]

## Positive RH obligation

The theorem replaces the qualitative missing reverse inequality by a quantitative saturation
problem.  The exact pure-state source already retains more than nineteen twentieths of the
positive thermal moment.  A successful completion must improve the source-controlled retention
factor from `1 - kappa(C)` to one while preserving the exact source/divisor incidence.  The
unconditional result does not prove that the orientation energy vanishes.

## Principal declarations

- `xiEndpointCompletedCurvature_lt_one_third`
- `xiEndpointCompletedCurvature_lt_two_over_fortyThree`
- `xiZeroCopy_two_lt_im_sq`
- `xiThermalOrientationTerm_le_relativeFactor_node_sq`
- `xiThermalRelativeOrientationFactor_lt_thirtyTwo_over_fortyNine`
- `xiThermalRelativeOrientationFactor_lt_one_twentieth`
- `xiThermalOrientationEnergy_le_relativeFactor_secondMoment`
- `relativeFactor_complement_mul_thermalSecondMoment_le_source`
- `xiThermalSecondMoment_le_source_div_relativeFactorComplement`
- `normalizedPrimeArchMoment_one_pos`
- `xiThermalOrientationEnergy_lt_one_twentieth_secondMoment`
- `nineteen_over_twenty_thermalSecondMoment_lt_source`
- `xiThermalSecondMoment_lt_twenty_over_nineteen_source`
- `normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource`
- `xiThermalSecondMoment_sub_orientationEnergy_eq_bornWittenSource`
- `xiBornWittenThermalQuantitativeMaster`

All declarations are unconditional.  RH occurs only in the reverse directions of the displayed
endpoint equivalences.
