# A viable Kapustin Hilbert--Pólya metric must carry a pre-divisor quantized source incidence

- **ID:** `kapustin-source-incidence-polarization`
- **Stage:** 5-failed
- **Type:** TERMINAL DIRECT HILBERT--PÓLYA ROUTE VERDICT, `[BRIDGE]`
- **Route status:** `[CLOSED IN THE AUDITED EULER-SOURCE CATEGORY]`
- **Statement:** Kapustin's exact point-spectrum carrier cannot become an independent RH producer by
  selecting another scalar analytic gauge, by a compact-open continuous FE--Schwarz regular-germ
  metric, by a continuous metric on the full Marcinkiewicz vanishing-tail/source-germ product, or by
  adjoining the Xi divisor and then imposing Hilbert positivity.  A surviving realization must
  instead construct, before divisor reconstruction, a quantized source incidence that is invisible
  to all three quotients and that canonically produces the Hilbert metric.

## Exact carrier and endpoint

Kapustin's operator on the symmetric critical-line Krein space is

```text
T_phi f(s)=f(s)/(s(1-s))-[f,u]_phi u(s),
u(s)=pi^(-s/2) Gamma(s/2) zeta(s).
```

For every nontrivial zero `rho` of `xi`, it has the eigenvalue

```text
lambda_rho=1/(rho(1-rho)).                                  (1)
```

The corresponding eigenfunction is

```text
f_rho(s)=u(s) s(1-s)/(1-lambda_rho s(1-s)),
[f_rho,u]_phi=1.
```

For `rho=beta+i gamma`,

```text
Im(rho(1-rho))=(1-2 beta) gamma.                            (2)
```

Every actual xi zero has `gamma!=0`.  Therefore

```text
lambda_rho is real  <->  beta=1/2.                          (3)
```

If a complex Hilbert-symmetric operator has a nonzero eigenvector with eigenvalue `lambda`, then
`conj(lambda)=lambda`.  Combining this elementary spectral theorem with `(3)` proves:

> `[LEAN; BRIDGE]` One Hilbert-symmetric operator containing `(1)` for every point of the actual Xi
> divisor implies RH.

This is formalized by
`RHTower.riemannHypothesis_of_kapustin_symmetric_pointSpectrum` in
`formal/GaloisForLFunctions/RHTower/KapustinHilbertEndpoint.lean`.  Thus Hilbert self-adjointness of
the exact Kapustin spectrum is the RH endpoint itself.  It is not an intermediate source theorem.

## Scalar metric class is closed

`kapustin-carrier-bilateral-polarization-law.md` proves on paper that every nonzero bounded analytic
Kapustin gauge has positive and negative weight sets of positive measure.  Its exact symmetric
carrier has index

```text
(ind_+,ind_-)=(infinity,infinity).                           (4)
```

If `J_phi` is its fundamental symmetry, `P_-` its negative projection, and a bounded self-adjoint
correction `G` satisfies `J_phi+G>=0`, then

```text
P_- G P_- >= P_-.                                           (5)
```

Hence every successful correction is noncompact, infinite-rank, outside every finite Schatten
class, and has essential norm at least one.  Another scalar half-plane analytic gauge cannot be the
metric producer.

## Euler-source incidence trichotomy

The proposed replacement was a pointed global metric

```text
G=G(weighted all-prime coefficient tail,
    archimedean completion,
    distinguished divisor/trace moments).                  (6)
```

The corpus now classifies each possible reading of `(6)`.

### 1. Regular-germ continuous reading

The unconditional Lean theorems

```text
criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_compl_finset
criticalDisc_analytic_odd_schwarz_mem_realEulerIncrementGroup_closure
criticalDisc_continuous_finiteUnitInvariant_eq_base
```

prove that every fixed-divisor FE--Schwarz regular-germ fibre is one genuine finite Euler-unit orbit
closure.  Its maximal Hausdorff continuous quotient is one point.  After restoring the principal
part, the maximal quotient is the divisor/multiplicity marking.  Consequently a compact-open
continuous metric invariant under finite Euler-unit changes cannot supply an RH sign inside the
fibre.

### 2. Weighted-tail continuous reading

`weighted-euler-tangent-global-graph-decoupling.md` proves that the joint finite Euler graph is dense
in

```text
M_0 x O(Q_+)_R,
```

and that the affine actual-source closure is

```text
(one+M_0) x O(Q_+)_R.                                      (7)
```

The only continuous coefficient quotient left is the Mertens class `[one]` in
`Q_log=M_log/M_0`; it decouples from the complete regular strip field.  Thus strengthening the germ
topology by the entire vanishing weighted tail still produces no continuous source--divisor
incidence.

### 3. Divisor-faithful reading

Retaining the translated residue function or all distinguished reciprocal-square trace moments
recovers the actual Xi divisor with multiplicity.  The Lean theorem

```text
XiCentralTraceHankelNonnegative <-> RiemannHypothesis
```

then shows that positivity of the resulting moment/Herglotz metric is exactly RH.  In Kapustin
coordinates, the same collapse is already pointwise in `(3)`: Hilbert symmetry makes every
`lambda_rho` real and therefore puts every `rho` on the line.

The third reading is a faithful target, but it is not a source producer.

## Terminal verdict

The three readings exhaust the currently defined meaning of `(6)`:

```text
regular germ       -> one-point continuous quotient,
weighted tail+germ -> product decoupling modulo [one],
divisor/moments    -> exact RH-equivalent positivity.        (8)
```

Therefore the proposed Kapustin--Xi incidence polarization is closed as an independent
Hilbert--Pólya mechanism.  Naming the three inputs in `(6)` does not construct a fourth object
between source and divisor.

## Positive reopening condition

A viable direct Hilbert--Pólya realization in this lane must construct a new object `I_src` with all
of the following properties:

1. **Pre-divisor:** `I_src` is defined from completed Euler--Gamma source data before evaluating the
   Xi divisor or reciprocal-square moments.
2. **Quantized:** it carries an integer, parity, K-class, index, or other collision-stable charge
   before graph closure.
3. **Nonlocal topology:** it does not factor continuously through the compact-open regular germ,
   `M_0 x O(Q_+)_R`, or a finite source feature space.
4. **Non-oracular:** its definition does not contain `kappa_-=0`, Herglotz/Stieltjes/Hankel
   positivity, real zero localization, or an equivalent RH predicate.
5. **Metric production:** it canonically constructs a full-sector correction satisfying `(5)` on a
   canonical arithmetic domain, rather than merely restating positivity.
6. **Divisor faithfulness:** its vanishing/positivity forces the exact Kapustin eigenvalues `(1)` to
   be Hilbert-symmetric without first reconstructing their zero labels.

Producing such an `I_src` would reopen the route as new mathematics.  No object in the current
Kapustin, regular-germ, weighted-tail, corona, residue-graph, trace-Hankel, or Herglotz interfaces
satisfies these six clauses.

## Scope

- This closes the Kapustin scalar-gauge and currently proposed Euler-source incidence
  implementations, not the Hilbert--Pólya conjecture in every possible realization.
- An exact global self-adjoint operator constructed from a genuinely new pre-divisor source
  invariant remains logically viable and would prove RH.
- CCM, Suzuki, Sonin, prolate, and finite-Weil constructions are outside this verdict.
- Cofinal finite-prime approximants carrying the Xi divisor locally uniformly with sub-log-square
  reflected-energy defect are outside this verdict.

## Scientific status

`[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Equation `(3)` and the Hilbert-symmetric eigenvalue argument
are standard complex arithmetic and spectral theory; Kapustin explicitly observes that a Hilbert
self-adjoint operator with his eigenvalues would imply RH.  The source trichotomy synthesizes the
project's proved orbit-closure, weighted graph-decoupling, and trace-Hankel equivalence results.  Its
value is a precise route closure and reopening specification, not a new scientific theorem.

## References

1. V. V. Kapustin, *Hilbert--Pólya Operators in Krein Spaces*, Siberian Math. J. 65 (2024),
   72--75, DOI `10.1134/S0037446624010087`.
2. N. Makarov and A. Poltoratski, *Beurling--Malliavin theory for Toeplitz kernels*, Invent. Math.
   180 (2010), 443--480, DOI `10.1007/s00222-010-0239-4`.

## Gates

- [x] Exact Kapustin spectral endpoint proved in Lean.
- [x] Scalar bounded-analytic gauge class classified on paper.
- [x] Compact-open FE--Schwarz regular-germ quotient classified in Lean.
- [x] Weighted `M_0` source/germ product classified on paper.
- [x] Divisor/trace-moment positivity identified exactly with RH in Lean.
- [x] Current pointed-incidence proposal assigned to the trichotomy `(8)`.
- [ ] Reopen only with an object satisfying all six positive clauses above.

## Log

- 2026-07-11 -- exact scalar and Hilbert-symmetric endpoint formalized; source-incidence metric
  audited against regular-germ orbit density, weighted graph decoupling, and trace-Hankel positivity;
  current Kapustin incidence implementation retired.
