# Signed period relations for every actual Mayer solution

- **Stage:** 2-fully-proven
- **Type:** Paper theorem; Lean formalization in progress
- **Parent:** [PM](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–4.

## Statement

Let `Re w>0`, `ε∈{1,−1}`, and let `f` belong to the actual Mayer disc algebra.
If `L_w f−ε f` is constant, put `P(a)=f(a−1)`. Then

```text
P(a)=ε a^(−w) P(1/a)                              (1/2≤a≤2),
P(a)=P(a+1)+(a+1)^(−w) P(a/(a+1))                 (1≤a≤2).
```

Thus every actual signed eigenfunction, and every constant-forced signed
solution, has the corresponding inversion parity and the Lewis relation.
Every negative-signed solution vanishes at the origin: `f(0)=0`.
The statement includes the assigned operator value at `w=1`: its constant
rank-one term disappears from the difference identity.

## Proof

For two adjacent points in the disc, subtract the actual branch cutoffs.
Their difference telescopes to the first branch minus the last branch.
The latter tends to zero because `Re w>0` and the disc representative is
bounded. The scalar renormalization has equal evaluations at both points;
the norm-convergent remainder therefore gives

```text
(L_w f)(a−1)−(L_w f)(a)=a^(−w) f(1/a).
```

Constant forcing cancels, and `ε²=1` gives
`P(a)=P(a+1)+ε a^(−w) P(1+1/a)`.
Apply this identity at `1/a`, multiply by `ε a^(−w)`, and use
`a^(−w)(1/a)^(−w)=1`. The resulting right side is the preceding expression
for `P(a)`, proving inversion parity. All required points lie in the disc
when `1/2≤a≤2`. For `1≤a≤2`, apply parity at `1+1/a`; multiplication of
positive-real powers converts the last term to
`(a+1)^(−w)P(a/(a+1))`. At `a=1`, negative parity gives
`f(0)=−f(0)`, hence zero. This holds for complex parameters throughout
the right half-plane; the earlier derivative-cone argument covered only
positive real parameters.

## Exact negative boundary response

The same telescoping identity gives an arbitrary-input law:
`(I+L_w)f=g` implies `f(0)=g(0)−g(1)`.
Indeed, evaluate the source equation at zero and one, subtract, and use
`(L_w f)(0)−(L_w f)(1)=f(1)`. Thus the negative inverse's boundary row is
fixed by the original source evaluations wherever that inverse exists;
no spectral inverse or regularity premise is needed for the solution law.

## Scope

Local corpus searches located these identities only for the canonical
scattering state. This extends them to every actual signed eigenfunction
and constant-forced solution. It does not assert surjectivity onto an
independently defined period space, a Hermitian form, cusp/scattering
separation, or resonance exclusion.
