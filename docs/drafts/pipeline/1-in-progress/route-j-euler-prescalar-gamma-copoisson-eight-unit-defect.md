# Route J full-Euler pre-scalar Gamma/co-Poisson reporter

- **Status:** division-free source object paper-proved and Lean-formalized; sharp factor-two
  positive-capacity defect open
- **Parent:** `rh-current-frontier-map.md`, Route J
- **Source paper:**
  `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
- **Formal certificate:**
  `formal/GaloisForLFunctions/RHTower/EulerPreScalarGammaCoPoissonReporter.lean`
- **Open core:** `FOUR_UNIT_PRESERVING_GAMMA_COPOISSON_COMPRESSION`

## Why this object is needed

The updated Green-descent paper identifies the first unresolved edge as a
presentation-independent infinite ordinary-prime Gamma/co-Poisson reporter retaining affine
terms before overlap division and retaining positive four-unit energy through completion.
Existing full-Euler Hilbert incidence reconstructs the continued Xi trace only through the scalar
quotient

```text
score_sigma(u) / ((sigma-1) B_sigma(u)).
```

That quotient is singular at the critical Euler boundary and therefore is not itself the required
source object.  The construction below keeps its denominator as a graph coordinate and proves the
complete affine factorization before division.

## Literal positive source

Let `epsilon=sigma-1>0`.  On the normalized positive-integer Euler Hilbert space write

```text
psi_sigma(n) = sqrt(P_sigma(n)),
phi_sigma(n) = -2 epsilon (log n-m_sigma) psi_sigma(n),
m_sigma       = E_sigma(log n).
```

The state and centered tangent satisfy

```text
||psi_sigma||=1,
<psi_sigma,phi_sigma>=0,
||phi_sigma||^2 -> 4.
```

Direct pole cancellation after graph division produces the divergent raw clock

```text
2m_sigma psi_sigma-epsilon^(-1)phi_sigma
  =2(log n)psi_sigma.
```

Moving the cancellation before division instead gives the actual source

```text
P_sigma
 =epsilon(2m_sigma psi_sigma-epsilon^(-1)phi_sigma)
 =2epsilon m_sigma psi_sigma-phi_sigma
 =2epsilon(log n)psi_sigma.                         (JPG1)
```

No Xi zero, divisor coordinate, target sign, or post hoc normalization enters `(JPG1)`.

## Exact division-free affine graph

For `u>=0`, put

```text
s_sigma(u)=sigma+u epsilon,
psi_sigma,u(n)=exp(-u epsilon log n)psi_sigma(n),
B_sigma(u)=<psi_sigma,psi_sigma,u>
            =zeta(s_sigma(u))/zeta(sigma),
D_sigma(u)=epsilon B_sigma(u).                       (JPG2)
```

The full-Euler Fisher identity gives

```text
<phi_sigma,psi_sigma,u>
 =2D_sigma(u)(F(sigma)-F(s_sigma(u))),

F(s)=-zeta'(s)/zeta(s).
```

Using `(JPG1)` before any division therefore yields

```text
<P_sigma,psi_sigma,u>
 =2D_sigma(u)F(s_sigma(u)).                          (JPG3)
```

Retain the archimedean/polar term on the same side of the graph and define

```text
N_sigma(u)=(-i/2)(
  <P_sigma,psi_sigma,u>
  -2D_sigma(u) logDeriv(archFactor)(s_sigma(u))).     (JPG4)
```

Equations `(JPG2)--(JPG4)` give the exact source identity

```text
N_sigma(u)
 =D_sigma(u) continuedPrimeArchSourceRelativeTrace(
    xiWardCenteredCoordinate(s_sigma(u))).           (JPG5)
```

This is the requested pre-scalar operation order: ordinary-integer source coefficient, affine
Gamma/polar correction, and completed source trace coexist in one graph before division by
`D_sigma(u)`.  All identities hold on the strict Euler half-plane and are unconditional.

## Sharp positive-capacity defect

The same source is not four-unit.  Its exact energy is

```text
||P_sigma||^2
 =4 epsilon^2 E_sigma((log n)^2),                    (JPG6)
```

and the full-Euler second-clock law gives

```text
||P_sigma||^2 -> 8                                   (JPG7)
```

as `sigma -> 1+`.  In particular `||P_sigma||^2>4` eventually.  This is a factor-two defect, not
an unknown estimate.  It comes from the two orthogonal critical components in `(JPG1)`:
`2 epsilon m_sigma psi_sigma` has limiting squared norm four and `phi_sigma` has limiting squared
norm four.  Positive Hilbert geometry cannot cancel their energies merely because their scalar
coefficients cancel against the archimedean current in `(JPG4)`.

## Strongest positive survivor

`[CONJECTURE] [ROUTE J OPEN]`

Construct a source-defined Gamma/co-Poisson compression of `(JPG4)` which

1. preserves the complete coefficient family `(JPG5)` before division;
2. retains ordinary-prime/prime-power labels and affine Gamma terms;
3. maps the eight-unit source into a positive carrier of squared norm at most four; and
4. lands coefficient-faithfully in the actual completed Green/Hodge sector.

A scalar contraction cannot be installed from the desired output: that would merely restate the
missing admission.  The compression must arise from the Gamma/co-Poisson source incidence itself.
The exact quantitative target is now removal of one four-unit orthogonal component without losing
`(JPG5)`.

## Formal map

| Paper item | Lean declaration |
|---|---|
| source `(JPG1)` | `eulerPositivePreScalarGammaSource` |
| affine source splitting | `eulerPositivePreScalarGammaSource_eq_base_sub_tangent` |
| energy `(JPG6)` | `norm_eulerPositivePreScalarGammaSource_sq` |
| eight-unit limit `(JPG7)` | `tendsto_norm_eulerPositivePreScalarGammaSource_sq` |
| eventual four-unit failure | `eventually_four_lt_norm_eulerPositivePreScalarGammaSource_sq` |
| overlap coefficient `(JPG2)` | `inner_eulerPositiveState_dampedState_eq_affineOverlap` |
| graph denominator | `eulerPositivePreScalarGraphDenominator` |
| prime numerator `(JPG3)` | `inner_eulerPositivePreScalarGammaSource_dampedState_eq_shiftedFlux` |
| completed numerator `(JPG4)` | `eulerPositivePreScalarGammaXiNumerator` |
| division-free factorization `(JPG5)` | `eulerPositivePreScalarGammaXiNumerator_eq_denominator_mul_continued` |

## Novelty discipline

- Individual zeta overlap, Fisher-centering, and Gamma completion identities already existed.
- New content is their literal positive-Hilbert assembly before overlap division, together with
  exact completed graph factorization and sharp eight-versus-four capacity audit.
- No external priority claim is made.  This card records new internal scientific knowledge and
  the exact narrower compression theorem still needed.
