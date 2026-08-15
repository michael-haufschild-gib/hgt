# Route P primitive Hankel depth-square intertwiner

- **ID:** `route-p-primitive-hankel-depth-square-intertwiner`
- **Label:** P-G179
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT SOURCE INTERTWINER
- **RH used:** no
- **Computation used:** no
- **Parents:** P-G177, P-G178

## Statement

For primitive cell `pe`, P-G177's cubic Euler feature is

```text
phi_pe(r)=q_pe r(exp(-lambda_pe r)-exp(-2 lambda_pe r)),
q_pe=sqrt(Lambda(n_pe)/n_pe).
```

Let `D(p,e)=(p,2e+1)` and `g(pe)=sqrt(n_pe)` as in P-G178. Then

```text
g(pe) phi_(D pe)(r) = (1/2) phi_pe(2r).                (P-G179.1)
```

The identity commutes with every finite primitive synthesis. For arbitrary `f : R -> C`, physical
half-line dilation satisfies

```text
integral_(0,infinity) |(1/2)f(2r)|^2 dr
  =(1/8) integral_(0,infinity) |f(r)|^2 dr.             (P-G179.2)
```

## Proof

P-G178 gives `lambda_(D pe)=2 lambda_pe` and `g(pe)q_(D pe)=q_pe`. Substitution into the feature
definition yields

```text
g q_D r(exp(-2lambda r)-exp(-4lambda r))
 =q r(exp(-2lambda r)-exp(-4lambda r))
 =(1/2) q (2r)(exp(-lambda(2r))-exp(-2lambda(2r))).
```

Finite-synthesis identity follows termwise. For `(P-G179.2)`, norm multiplicativity gives factor
`1/4`, and change of variables `u=2r` gives Jacobian `1/2`. Their product is `1/8`. `QED`

## New knowledge and anti-theatre audit

P-G178's arithmetic weight cancellation is not a numerical coincidence. Under the canonical
pre-divisor Hankel synthesis, it is exactly ordinary geometric dilation of physical half-line.
The three factors in `1/8` are now separated: squared half-amplitude contributes `1/4`, and radial
Jacobian contributes `1/2`.

This still does not land on Xi divisors or imply P-G176 capacity. It identifies the exact
source-space operator that any determinant-line/conormal continuation must carry. A claimed RH
advance that replaces this operator by an abstract contraction without proving its Gamma--Euler/Xi
landing remains theatre.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  RoutePPrimitiveHankelDepthSquareIntertwiner.lean
```

Capstones:

- `routePPrimitiveCubicHankelFeature_depthSquare`;
- `routePPrimitiveCubicHankelFiniteSynthesis_depthSquare`;
- `integral_normSq_half_dyadic_dilation`.

Scratch `lake env lean /tmp/pg179.lean` passed. Only exact missing leaf `.olean` was built. Axiom
audit reports `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is wired and umbrella
was not built.

## Next gate

Factor P-G177's collision feature as the defect of this physical dilation and determine whether
the resulting dyadic Calderon reconstruction supplies a source-defined two-variable continuation
or instead proves that all singular curvature must come from the Gamma--Euler landing itself.
