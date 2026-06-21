# Reciprocal Seam Admissible Domain Equals Q1

- **ID:** reciprocal-seam-admissible-domain-q1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/gpt/proof-route.md`, sections 2, 7, 8
- **Statement:** The canonical finite polynomial domain of the raw unshifted reciprocal-seam quadratic form is the ideal `y R[y]`; under `p(y)=y q(y)`, that restricted unshifted form is exactly the shifted route form `Q_1[q]`.

## Goal

Turn the "restricted quadratic-form domain" option in the `T_0` obstruction into a precise route object. This prevents a false repair of the unshifted tower: extending the form from `y R[y]` to constants requires an extra finite-part value for `T_0`, and that value is not supplied by the divisor moments.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let

```text
y_rho = -(rho - 1/2)^(-2)
```

and let the raw unshifted reciprocal-seam form be the formal expression

```text
U[p] = sum_rho m_rho p(y_rho)^2.
```

The reciprocal atoms satisfy `y_rho -> 0`, while the divisor has infinitely many nontrivial zeros. If a polynomial `p` has `p(0) != 0`, then `p(y_rho)^2 -> p(0)^2 != 0`. Hence the terms of `U[p]` do not tend to zero, so the ordinary series cannot converge. Therefore every polynomial in the ordinary finite domain of the raw unshifted form must vanish at `0`.

The polynomials vanishing at `0` are exactly the ideal

```text
y R[y].
```

Write `p(y)=y q(y)` with `q(y)=sum_i c_i y^i`. Then

```text
U[p] = sum_rho m_rho y_rho^2 q(y_rho)^2
     = sum_{i,j} c_i c_j T_{i+j+2}
     = Q_1[q].
```

All moments appearing here have index at least `2`, hence are in the finite shifted tower covered by the proof route. Thus the domain-restricted unshifted form is not a third independent object: it is exactly `Q_1` after division by the mandatory zero at the reciprocal accumulation point.

By contrast, any form on all polynomials must assign a finite value to the constant-constant entry `T_0`. Since the divisor gives `T_0=sum_rho 1=infinity`, such an extension is extra regularization data. It cannot be used as a source-built proof-route object unless the finite part and all Hankel compatibility conditions are separately proved.

## Computation

Toy model `y_n=1/n^2` verifies the algebraic reduction and the finite-part ambiguity:

- `T_0(N)=N` diverges while `T_k(N)` converges for `k>=1`;
- the unshifted form restricted to basis `y,y^2,...` equals `Q_1` entrywise;
- replacing `T_0` by a chosen finite part changes the inertia of the leading `2x2` unshifted block.

Artifacts:

- `computations/2026-06-21-conway-admissible-domain-q1.py`
- `computations/2026-06-21-conway-admissible-domain-q1.txt`

## Route Consequence

The shifted proof route has a precise form-domain reading:

```text
Q_0[p] = sum_rho m_rho y_rho p(y_rho)^2
```

is the minimal one-power localizing form that includes constants, while

```text
Q_1[q] = sum_rho m_rho y_rho^2 q(y_rho)^2
```

is the raw unshifted form on its canonical finite polynomial domain `y R[y]`.

Therefore the route should not look for a canonical unshifted `T_0` tower. The canonical domain repair is already one of the two required shifted square-test forms.

## Log

- 2026-06-21 -- Conway: created after workflow NODE "market price of risk process must satisfy integrability/admissibility conditions", using method 18 (look for the right theorem).
