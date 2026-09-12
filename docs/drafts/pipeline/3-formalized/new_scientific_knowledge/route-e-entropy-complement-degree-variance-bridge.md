# Route E reciprocal-degree variance bridge

- **ID:** `ROUTE-E-RECIPROCAL-DEGREE-VARIANCE-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [DETERMINISTIC REDUCTION] [RATE FIREWALL]`
- **Parent:** `route-e-degree-normalized-gibbs-boundary-variation-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteEEntropyComplementDegreeVarianceBridge.lean`

## Exact bridge

Let `U(i,j)=U(j,i)≥0` be raw edge weights, let

\[
 d_i=\sum_j U(i,j)>0,
\]

and let `a_i` be any real comparison profile. Define

\[
 \mathcal E(f)=\sum_{i<j}U(i,j)(f_i-f_j)^2.
\]

Lean proves

\[
 \boxed{
 \mathcal E(1/d)
 \le 3\sum_i d_i(1/d_i-a_i)^2+3\mathcal E(a).}
\tag{1}
\]

For a constant profile `a`, the sharper bound is

\[
 \boxed{
 \mathcal E(1/d)
 \le 2\sum_i d_i(1/d_i-a)^2.}
\tag{2}
\]

For a positive degree profile `D_i`, if `delta*D_i≤d_i`, then

\[
 d_i\left(\frac1{d_i}-\frac1{D_i}\right)^2
 =\frac{(d_i-D_i)^2}{d_iD_i^2}
 \le \frac{(d_i-D_i)^2}{\delta D_i^3}.
\tag{3}
\]

Combining (1) and (3) isolates two arithmetic producers: relative degree variance around `D_i`,
and Dirichlet variation of `1/D_i`. This is the deterministic interface between local incidence
counting and the degree-normalized Gibbs boundary-variation consumer.

## Rate firewall for the raw unit shell

Suppose an unweighted shell on `X` vertices has typical degree `H`, total degree variance `V`, and
raw edge budget `B≈XH`. Equations (2)--(3) put reciprocal-degree energy at scale `V/H^3`.
The existing absolute Cauchy consumer therefore gives

\[
 \mathcal V_{\deg}^2\lesssim B\frac{V}{H^3}
 \asymp \frac{XV}{H^2}.
\tag{4}
\]

To reach `\mathcal V_deg≤X^(1/2+o(1))`, (4) requires

\[
 \boxed{V\le H^2X^{o(1)}.}
\tag{5}
\]

At `H=sqrt(X)`, even Poisson-size total variance `V≈XH` misses (5) by `sqrt(X)`. This does not
prove such a lower bound for the arithmetic degree and does not exclude cancellation before
absolute values. It rules out the direct composition
`raw unit shell → Poisson degree variance → absolute Cauchy → strict-half current`.

## Surviving attack

1. Regularize or reweight physical incidence so edge budget and degree residual couple more
   sharply than in (4).
2. Estimate signed reciprocal-normalizer flux before absolute values, preserving cancellation
   discarded by Cauchy.

## Lean theorem map

- `inverseDegreeProfileDirichletEnergy_le_profileResidual_add_profileEnergy`
- `inverseDegreeDirichletEnergy_le_two_centeredEnergy`
- `inverseDegreeCenteredEnergy_inv_le_degreeCenteredEnergy`
- `inverseDegreeProfileResidualEnergy_inv_le_relativeVarianceBudget`
- `inverseDegreeDirichletEnergy_le_relativeVariance_add_profileEnergy`

## Honest status

Finite deterministic inequalities are closed in Lean. No arithmetic variance estimate,
signed-flux estimate, all-scale Mertens bound, or RH proof is claimed.
