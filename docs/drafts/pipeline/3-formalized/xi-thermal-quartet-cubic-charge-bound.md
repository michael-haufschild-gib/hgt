# Xi thermal quartet cubic-charge bound

- **ID:** `xi-thermal-quartet-cubic-charge-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** `[PROVEN] [FORMALIZED] [NOVELTY UNVERIFIED] [RH ESTIMATE PROGRESS]`

## Statement

Let

\[
C=2+\gamma_E-\log(4\pi)
\]

be the completed endpoint curvature and let \(\mathcal E_\perp\) be the transverse
reciprocal-square thermal energy. Then

\[
\mathcal E_\perp
\le
4\left(\frac{C}{4-C}\right)^3
<
\left(\frac{86}{85}\right)^3\frac{C^3}{16}
<\frac1{150000}.
\]

Equivalently, the positive thermal second moment and the prime--Gamma source value obey

\[
0\le M_2-Q_W=\mathcal E_\perp<\frac1{150000}.
\]

## Mechanism

For one zero copy write \(u=(\Re\rho-1/2)^2\), \(v=(\Im\rho)^2\), let
\(e_q\) be its transverse reciprocal-square energy, and let \(w_q\) be its endpoint
cross charge. For an off-line copy,

\[
e_q=\frac{4uv}{(u+v)^4}
\le \frac1{v^3}.
\]

The exact quartet height theorem gives \(v>85\), while the endpoint cross-charge law gives

\[
\frac1{v+1}\le w_q,
\qquad
4w_q\le C,
\qquad
4\le C(v+1).
\]

The last inequality is equivalent to
\(v^{-1}\le(4/(4-C))(v+1)^{-1}\).

Consequently

\[
e_q
\le \left(\frac4{4-C}\right)^3 w_q^3
\le \left(\frac4{4-C}\right)^3\left(\frac C4\right)^2w_q.
\]

On-line copies have \(e_q=0\), so the last estimate holds for every copy. Summation and
\(\sum_qw_q=C\) give the exact source-dependent global cubic bound.  Finally,
\(C<2/43\) implies \(4/(4-C)<86/85\), yielding the displayed rational certificate.

## Gates

- [x] Exact paper inequality isolated.
- [x] Formalize the atomwise cubic charge estimate.
- [x] Formalize the global sum and rational bound.
- [x] Add the source-gap corollary to the master theorem.
- [ ] Audit scientific novelty.

## Formal artifacts

- `formal/GaloisForLFunctions/RHTower/XiThermalQuartetCubicChargeBound.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchExactOffLineQuartetKMSMaster.lean`

Principal declarations:

- `xiThermalOrientationTerm_le_endpointCrossCharge_cube`;
- `xiThermalOrientationTerm_le_exactEndpointCrossCharge_cube`;
- `tsum_xiEndpointCrossCharge_eq_curvature`;
- `xiThermalOrientationEnergy_le_exactCubicEndpointBudget`;
- `xiThermalExactCubicEndpointBudget_lt_cubicEndpointBudget`;
- `xiThermalOrientationEnergy_le_cubicEndpointBudget`;
- `xiThermalCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand`;
- `xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand`;
- `xiThermalSecondMoment_source_absoluteGap`.

The formal modules compile without placeholders.  This is strict progress on the missing estimate,
but it is not an RH proof: a remote off-line quartet can have arbitrarily small positive charge,
so a positive absolute upper bound does not force the gap to vanish.
