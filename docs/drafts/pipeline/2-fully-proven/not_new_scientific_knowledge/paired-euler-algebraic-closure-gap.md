# Paired Euler algebraic/closed-span gap

- **ID:** `paired-euler-algebraic-closure-gap`
- **Stage:** 2-fully-proven
- **Type:** `[THEOREM]`, `[POSITIVE COMPLETION DEFECT]`, not new scientific knowledge
- **Formal closure half:** `../../3-formalized/not_new_scientific_knowledge/fe-odd-reduced-quotient-blindness.md`
- **Route:** `../../1-in-progress/fermionic-fe-projector-lefschetz-rh.md`

## Statement

Let

```text
w_p(s) = primeEulerUnitTangent_p(s) - primeEulerUnitTangent_p(1-s)
```

be the actual FE-paired Euler-unit tangent on the open critical strip. On every positive-radius
critical disc, the transverse coordinate

```text
u(s)=2s-1
```

does not belong to the algebraic span of any finite family of the `w_p`. The Lean theorem in the
formal closure card proves simultaneously that `u` belongs to the closed span of the `w_p` after
deleting any finite set of primes. Hence

```text
u in closure(span{w_p}) \ span{w_p}.
```

The quotient of the closed span by the algebraic span therefore contains the canonical nonzero
class `[2s-1]`, while its Hausdorff reduction is zero.

## Proof of finite exact nonrepresentability

Write `L_p=log p`. The actual tangent is

```text
T_p(s)=L_p exp(-L_p s)/(1-exp(-L_p s))^2,
w_p(s)=T_p(s)-T_p(1-s).                                  (1)
```

Suppose on a nonempty open critical disc that

```text
sum_(p in P) c_p w_p(s)=2s-1                            (2)
```

for a finite prime set `P`. Both sides are analytic on the connected open strip, so the identity
theorem extends (2) throughout the strip.

Assume some `c_p` is nonzero and put

```text
b_p=2 pi i/L_p.
```

As `s` approaches `b_p` from inside the strip,

```text
exp(-L_p b_p)=1,
1-exp(-L_p s)=L_p(s-b_p)+O((s-b_p)^2),
(s-b_p)^2 T_p(s) -> 1/L_p.                              (3)
```

The reflected term `T_p(1-s)` is regular at `b_p`, because `Re(1-b_p)=1` and its denominator is
nonzero. Thus `(s-b_p)^2 w_p(s)` tends to the nonzero value `1/L_p`.

For a distinct prime `q`, a pole of `T_q` at `b_p` would imply

```text
exp(-2 pi i log q/log p)=1,
log q/log p in Z.
```

The integer is positive, hence `q=p^m`. Primality of `p,q` forces `m=1` and `q=p`, a contradiction.
The reflected `q` term is again regular on the `Re=1` boundary. Therefore `w_p` is the unique
member of the finite packet with a pole at `b_p`.

Multiplying (2) by `(s-b_p)^2` and taking the interior limit gives

```text
c_p/L_p = 0,
```

contrary to `c_p != 0`. Hence every coefficient is zero, which would make the left side of (2)
zero while `2s-1` is nonzero. This proves the claim. QED.

## Positive consequence

The previously unspecified “derived-limit defect” is unnecessary for this tangent model. The
specific algebraic quotient

```text
D_FE = closure(span{w_p}) / span{w_p}
```

already carries a canonical class `[2s-1] != 0`. Every continuous linear functional on the compact
carrier that annihilates the Euler tangents kills its representative, so the class is intrinsically
non-Hausdorff: it can only be read by boundary principal parts, coefficient-tail data, or another
discontinuous/higher-dimensional incidence.

## RH boundary

This theorem constructs a source completion defect but does not couple it to the Xi divisor. A
scalar residue reader falls under the proved singular corona/residue trilemma: it is zero,
nonclosable, or a direct divisor reader. A live successor must retain a vector-valued principal-part
module before scalarization and prove a source-defined reflection-odd annihilation there. The
class `[2s-1]` is the canonical test vector for such a construction.

## Classification

Private-pole separation and the identity theorem are standard meromorphic-function arguments. The
result is exact infrastructure and not new scientific knowledge. Lean formalization of the private
boundary-pole half remains optional; the closure half and nonvanishing representative are already
machine checked.
