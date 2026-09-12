# Route E sign-complete physical degree law

- **ID:** `ROUTE-E-SIGN-COMPLETE-PHYSICAL-DEGREE-001`
- **Stage:** 3-formalized
- **Type:** `[LEAN-CERTIFIED] [EXACT DEGREE DECOMPOSITION] [SOURCE REDUCTION]`
- **Parent:** `route-e-entropy-complement-physical-incidence-fibre-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean:** `formal/GaloisForLFunctions/RHTower/RouteESignCompletePhysicalDegree.lean`

## Sign-complete relation

For a symmetric numerical shell predicate `S(n,m)`, set

\[
 U(n,m)=\mathbf 1_{\{n,m\text{ squarefree}\}}
        \mathbf 1_{S(n,m)}
        \mathbf 1_{\{\mu(n)+\mu(m)=0\}}.
\tag{1}
\]

This physical incidence is symmetric and loop-free, and every supported edge reverses Möbius
sign. On squarefree integers, opposite Möbius signs are opposite parities of prime-factor
cardinality. Unlike adjacent-grade incidence, it includes every opposite-parity physical endpoint
in the shell.

## Exact row-degree decomposition

For fixed source `n`, define

\[
 Q(n)=\sum_m\mathbf 1_{\{m\text{ squarefree}\}}\mathbf 1_{S(n,m)},
 \qquad
 M(n)=\sum_m\mu(m)\mathbf 1_{S(n,m)}.
\tag{2}
\]

If `mu(n)=±1`, raw row mass `d(n)=sum_m U(n,m)` obeys

\[
 \boxed{2d(n)=Q(n)-\mu(n)M(n).}
\tag{3}
\]

For every comparison constant `Q0`, Lean also proves

\[
 \boxed{
 \left(d(n)-\frac{Q_0}{2}\right)^2
 \le \frac{(Q(n)-Q_0)^2}{2}+\frac{M(n)^2}{2}.}
\tag{4}
\]

Equation (3) identifies the complete arithmetic producer. Degree regularity is neither an
independent graph assumption nor merely squarefree equidistribution: it contains the local Möbius
shell sum itself.

## Consequence for the proof chain

Sign-completion removes exact adjacent-grade concentration from the degree problem. In exchange,
(4) requires both squarefree-shell variance and a Möbius short-interval second moment at the rate
imposed by the reciprocal-degree consumer. Current qualitative or logarithmic-saving
short-interval mean-square bounds do not meet that raw-graph rate. Exact identity leaves
regularized incidence and signed-flux estimates open.

## Lean theorem map

- `routeESignCompleteRawIncidence_nonneg`
- `routeESignCompleteRawIncidence_comm`
- `routeESignCompleteRawIncidence_diag`
- `routeESignCompleteRawIncidence_support_reverses_moebius`
- `routeESignCompleteRowMass_eq_oppositeSignShellMass`
- `routeE_two_mul_signCompleteRowMass_eq`
- `routeE_signCompleteRowMass_deviation_sq_le`

## Honest status

Incidence properties, exact degree split, and variance reduction are closed in Lean. No required
short-interval second moment, reciprocal-load estimate, Mertens bound, or RH proof is claimed.
