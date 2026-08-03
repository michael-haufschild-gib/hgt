# Route R prime/depth BV--Wold curved source differential

- **ID:** `route-r-prime-depth-bv-wold-curved-source-differential`
- **Stage:** 1 — in progress
- **Type:** PRE-SCALAR SOURCE CONNECTION / NONSEPARABLE CURVED DIFFERENTIAL
- **Status:** `[CORE FORMALIZED] [NONSEPARABILITY PROVED] [ANNIHILATION OPEN] [NOT RH]`
- **Parent:** `route-r-essential-edge-occupation-det2-bv-relative-class.md`

## Frontier statement

The diagonal `det₂` construction produces two independent source records at a prime/depth cell
`i=(p,e)`:

```text
m_i = (1-p^(-1))*p^(-e),           Wold depth cell of singular BV first trace,
lambda_i = log(p^(e+1)),           Wold--Gamma depth clock.
```

Their alternating off-diagonal coupling is

```text
theta(i,j) = m_i lambda_j - m_j lambda_i.                 (1)
```

No prime, depth, or divisor coordinate is summed.  For a centered real parameter `a`, define

```text
A_a(i,j) = a theta(i,j),
U_a(i,j) = exp(A_a(i,j)).                                 (2)
```

At an Xi divisor copy `rho`, use the uniform specialization

```text
a_rho = 2 Re(rho)-1.                                      (3)
```

This gives one profile over the entire divisor support, rather than coefficients selected after
examining a zero.

## Exact source differential

For a zero-cochain `f` and one-cochain `omega` on the complete prime/depth incidence complex, set

```text
(D0_a f)(i,j)       = U_a(i,j) f(j) - f(i),
(D1_a omega)(i,j,k) = U_a(i,j) omega(j,k) - omega(i,k) + omega(i,j).   (4)
```

Direct cancellation gives the curvature-square law

```text
(D1_a D0_a f)(i,j,k)
  = (U_a(i,j)U_a(j,k)-U_a(i,k)) f(k).                     (5)
```

Thus this is a genuine discrete exterior covariant differential, with its failure to square to
zero retained as a labelled two-simplex coefficient.  It acts before scalar trace,
codiagonalization, or frequency separation.  Pointwise application in `rho` preserves divisor
provenance as well as both endpoint prime/depth labels.

## Dependency-closed nonseparability proof

Equation `(1)` is diagonal-zero and antisymmetric.  It is sign-indefinite already on the two
oriented same-prime edges between `(2,0)` and `(2,1)`.

Take

```text
i0=(2,0), i1=(2,1), i2=(2,2).
```

Using `m_(2,e)=2^(-(e+1))` and
`lambda_(p,e)=(e+1)log p`, the additive triangle curvature is

```text
theta(i0,i1)+theta(i1,i2)+theta(i2,i0)
  = -log(2)/8 != 0.                                      (6)
```

Hence there is no vertex potential `phi` satisfying
`theta(i,j)=phi(j)-phi(i)` on all prime/depth cells.  This is the precise property missing from
the previously formalized reflected incidence
`exp(a(lambda_j-lambda_i))`, whose every cycle is flat and whose finite matrices are related by a
diagonal gauge.  Formula `(6)` proves, rather than declares, that `(1)` is nonseparable and not an
endpoint gauge.

The stronger clock-difference test also passes:

```text
lambda_i1-lambda_i0 = lambda_i2-lambda_i1 = log 2,
theta(i0,i1)-theta(i1,i2) = log(2)/4 != 0.                (6a)
```

Therefore no function `F` can satisfy
`theta(i,j)=F(lambda_j-lambda_i)` on all prime/depth cells.  This rules out the larger
difference-only class, not only linear endpoint gauges.

Exponentiating `(6)` gives the multiplicative witness

```text
U_a(i0,i1) U_a(i1,i2) = U_a(i0,i2)
  iff a=0.                                                (7)
```

Therefore, for every Xi divisor copy,

```text
(D1 D0)(rho) vanishes on the witness simplex
  iff Re(rho)=1/2.                                       (8)
```

Functional-equation reflection negates `a_rho`, so it negates `A`, inverts `U`, and exchanges the
two orientations.  Equations `(5)--(8)` retain an unsquared, reflection-odd horizontal charge.

## Scientific status

This constructs the exact category left open by the Route-R no-go audit: pre-scalar,
sign-indefinite, off-diagonal, nonseparable, and prime/depth/divisor resolved.  It is not a proof
of RH.  Global flatness of this connection on all Xi divisor copies is equivalent to RH; no
source-derived theorem presently forces that flatness.  Calling `(8)` arithmetic annihilation
would be circular.

The new knowledge is narrower and concrete: the regular Wold depth record and Wold-transported
singular BV trace from the same relative `det₂` class have a canonical alternating coupling whose
curvature is provably nonzero, with exact smallest witness `-log(2)/8`.  This breaks the complete
vertex-gauge/spectral-blindness class without importing a common Xi factor.

## Novelty audit

Internal search found no BV-first-trace/Wold-depth exterior connection or the witness `(6)`.
Discrete covariant derivatives, curvature as their square, and holonomy around simplices are
standard; see:

- J. Fernandez, M. Juchani, M. Zuccalli, *Discrete connections on principal bundles: abelian
  group case*, <https://arxiv.org/abs/2109.08928>;
- D. Berwick-Evans, A. N. Hirani, M. D. Schubel, *Discrete Vector Bundles with Connection and the
  Bianchi Identity*, <https://arxiv.org/abs/2104.10277>.

Novelty is not claimed for that ambient formalism.  Candidate corpus-new content is the exact
arithmetic source one-form `(1)`, its non-coboundary witness `(6)`, and its uniform Xi-profile
specialization.

## Hostile falsifiers

1. Kill source provenance if `m_(p,0)` is not exactly the residue-one Wold--BV relative trace or
   if higher `m_(p,e)` are not its literal Wold cells.
2. Kill nonseparability if the triangle value in `(6)` is zero, if `(1)` admits a vertex
   potential, or if the equal-gap separation `(6a)` fails.
3. Kill divisor faithfulness if the construction sums divisor copies before applying `(4)`.
4. Do not call `D` a flat cochain differential away from the critical line; `(5)` is its curved
   square.
5. Do not infer global flatness from the construction.  That statement is RH-equivalent and is
   the remaining arithmetic annihilation theorem.

## Gates

- [x] exact source records frozen
- [x] internal collision audit
- [x] external ambient-formalism audit
- [x] dependency-closed paper proof
- [x] exact nonseparability witness
- [x] unconditional Lean formalization
- [ ] source-derived global curvature annihilation
- [ ] RH

## Lean realization

`GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential` proves:

- exact Wold depth transport `m_(p,e)=(1-p⁻¹)p⁻ᵉ` and its depth-zero relative spectral-zeta
  residue provenance;
- diagonal-zero, antisymmetry, and explicit positive/negative oriented edges;
- exact curvature `-log(2)/8`;
- absence of a vertex potential;
- absence of any clock-difference function, using equal gaps and coefficient separation
  `log(2)/4`;
- multiplicative witness flatness iff centered parameter is zero;
- complex-linear `D0`, `D1` and the labelled curved-square law;
- reflection inversion and divisor-profile preservation;
- witness nilpotence iff one divisor coordinate lies on the critical line;
- global differential flatness iff RH, stated only as an equivalence.

Direct `lake env lean`, targeted module build, and `#print axioms` passed.  Axiom output contains
only `propext`, `Classical.choice`, and `Quot.sound`.  Repository-wide formal lint remains red on
unrelated concurrent, umbrella-unreachable CCM/cyclic modules; this module is wired into
`RHTower.lean` and was not among the failures.
