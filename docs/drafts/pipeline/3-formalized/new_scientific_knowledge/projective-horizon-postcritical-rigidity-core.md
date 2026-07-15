# Projective-horizon postcritical rigidity core

- **ID:** `projective-horizon-postcritical-rigidity-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN) / PURE-FIBER SEPARATION CERTIFICATE
- **Scientific status:** `[FORMALIZED CORE] [NOVELTY PROVISIONAL] [SIGNIFICANT PARENT]`
- **Paper parent:** `projective-horizon-one-step-postcritical-rigidity`

## Formalized declarations

In `ProjectiveHorizonPostcriticalRigidity.lean`:

- `pureCriticalPostLeft`
- `pureCriticalPostRight`
- `pureCritical_postcritical_error_coeff`
- `pureCriticalPost_topEquation`
- `pureCriticalPost_rightTop_eq_neg_inv`

## Certified content

Given a pure critical factorization

```text
X_0 Y_0=1+t^(m+n),                                       (1)
```

Lean proves that the first postcritical extensions

```text
X=X_0+u t^(m+n),
Y=Y_0+v t^(m+n)                                           (2)
```

have inverse-error coefficient

```text
[t^(m+n)](XY-1)=1+u Y_0(0)+v X_0(0).                      (3)
```

Divisibility of the error by `t^(m+n+1)` therefore forces the right side of `(3)` to vanish.  Over
a field, at `u=0` and `X_0(0)!=0`, Lean solves it exactly as

```text
v=-X_0(0)^(-1).                                           (4)
```

Equation `(4)` is the explicit witness that the first postcritical reciprocal coordinate varies
across pure critical factor states.

## Verification

The module passes a targeted direct Lean check.  Scratch `#print axioms` for the three theorems is
part of the lane audit and contains only standard logical axioms.  No full build is run.

## Formal boundary

The module does not formalize finite-cover primitivity, rational function fields on an etale
fiber, or the global birational conclusion.  Those use the paper-proved full-symmetric monodromy
theorem.  No assumptions or placeholders are introduced to represent them.
