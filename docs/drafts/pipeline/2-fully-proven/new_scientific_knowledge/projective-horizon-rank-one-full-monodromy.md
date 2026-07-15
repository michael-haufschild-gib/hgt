# Every rank-one projective horizon has full symmetric monodromy

- **ID:** `projective-horizon-rank-one-full-monodromy`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / GENERIC CRITICAL MONODROMY
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY PROVISIONAL] [SIGNIFICANCE LIMITED]`
- **Formal status:** reciprocal coefficient and exact cotangent cores formalized
- **Parent:** `projective-horizon-irreducible-simple-ramification`
- **Lane:** source-pure hypertranscendental geometry; static branch topology

## Theorem

Let `K` be an algebraically closed characteristic-zero field and let `n>=1`.  Fix algebraically
independent parameters `p_1,...,p_n,q`, with `p_1 q!=0`, and put

```text
X(t)=a+p_1t+...+p_nt^n,
Y(t)=X(t)^-1 mod t^(n+1).                                  (1)
```

The generic fiber equation

```text
[t^n]Y=q                                                    (2)
```

has degree `n+1` in `a`, and its geometric Galois/monodromy group over
`K(p_1,...,p_n,q)` is the full symmetric group

```text
S_(n+1).                                                     (3)
```

Equivalently, the critical horizon cover `Phi_(1,n)` has maximal symmetric monodromy.  By reciprocal
duality the same holds for `Phi_(n,1)`.

## Proof

Set

```text
R(t)=p_1+p_2t+...+p_nt^(n-1),       X=a+tR.                 (4)
```

The finite geometric-series identity for `(1)` gives

```text
[t^n]Y
  =sum_(k=1)^n (-1)^k a^(-k-1)[t^(n-k)]R^k.                (5)
```

After `j=n-k`, define

```text
c_j=(-1)^(n-j)[t^j]R^(n-j),       0<=j<=n-1.               (6)
```

Multiplying `(2)` by `a^(n+1)` gives the centered degree-`n+1` equation

```text
F(a)=q a^(n+1)-sum_(j=0)^(n-1)c_j a^j=0.                  (7)
```

There is no `a^n` term.  The parameter change in `(6)` is triangular.  Its first coordinate is

```text
c_0=(-1)^n p_1^n,                                          (8)
```

and for `1<=j<=n-1`,

```text
c_j=(-1)^(n-j)
  ((n-j)p_1^(n-j-1)p_(j+1)+H_j(p_1,...,p_j)).              (9)
```

Indeed, the only term in `[t^j]R^(n-j)` involving `p_(j+1)` chooses `p_(j+1)t^j` once and the
constant term `p_1` in every other factor.  Thus `c_0,...,c_(n-1)` are algebraically independent,
and

```text
K(p_1,...,p_n)=K(c_0,...,c_(n-1))(p_1),
p_1^n=(-1)^n c_0.                                          (10)
```

Over the centered coefficient field

```text
E_0=K(q,c_0,...,c_(n-1)),                                  (11)
```

the polynomial `(7)` is the universal centered polynomial of degree `n+1`.  Translation removes
the next-to-leading coefficient from the universal degree-`n+1` polynomial in characteristic zero,
so its geometric Galois group is `S_(n+1)`.

It remains to show that the Kummer base change `(10)` does not shrink this group.  On `c_0!=0`, the
triangular map `(8)--(9)` is a cyclic finite etale cover of degree `n`: all diagonal derivatives
are nonzero.  The universal discriminant divisor is reduced, and its pullback under an etale map
is reduced.  Therefore the discriminant of `(7)` is not a square in
`K(p_1,...,p_n,q)`.

Let `E` be the splitting field over `E_0` and let `M=K(p_1,...,p_n,q)`.  Both `E/E_0` and
`M/E_0` are Galois after adjoining no constants, because `K` is algebraically closed.  The
intersection `E intersect M` is a cyclic quotient of `S_(n+1)`.  For `n+1>=3`, the only possible
nontrivial cyclic quotient is the sign quotient of order two, whose fixed field is obtained by
adjoining the square root of the discriminant.  The preceding nonsquare result excludes it.  Hence
`E intersect M=E_0`, so base change preserves `S_(n+1)`.  When `n=1`, `(10)` is the identity and
the quadratic group is `S_2` directly.  This proves `(3)`.  Reciprocal exchange proves the final
claim.  `QED`

## Consequence for the open all-rank problem

Every boundary family with `min(m,n)=1` has maximal monodromy.  Therefore any all-rank invariant
block system must appear genuinely when both horizon packets have at least two coordinates; it
cannot be inherited from reciprocal inversion alone or from a universal cyclic/Kummer label.

This theorem does not decide whether `Phi_(m,n)` has full
`S_(choose(m+n,m))` for `m,n>=2`.  In particular, it does not justify importing the `S_(m+n)`
action on `m`-subsets from the pure-tail factorization fiber.

## Novelty and significance audit

The Galois group of a universal centered polynomial, Kummer base change, and the discriminant sign
subfield are classical.  The new candidate is their exact occurrence in the rank-one reciprocal
horizon cover through the triangular coefficient law `(6)--(10)`.  A targeted search found
classical trinomial and generic-polynomial Galois results, but no statement for reciprocal-jet
horizon fibers.  Novelty remains provisional.

The theorem is a genuine generic-monodromy result and closes an infinite family, but it is a
rank-one boundary of the all-rank problem and rests on a reduction to the universal polynomial.
Its significance is therefore limited; it does not clear the completion bar.

## Physical meaning

At rank one there is no conserved labeling of the `n+1` vacua: static continuation of the observed
tail parameters realizes every permutation.  This is topology of a branched observation cover, not
quantum time evolution.  The result rules out a hidden cyclic charge created by the reciprocal
coefficient parametrization.

## RH impact

The rank-one cover is universal and target-translation blind.  Full symmetric monodromy removes
rather than supplies a canonical state label, so it has no RH consequence.  An RH application would
need an arithmetic marking that reduces this generic symmetry in a controlled, source-specific way.

## Formal verification

`ProjectiveHorizonExactLagrangian.lean` proves the exact reversed coefficient pairing and its
positive-degree vanishing under truncated inversion; these are the coefficient identities from
which `(5)--(7)` arise.  The triangular finite-cover and splitting-field argument are paper-level.
Only targeted leaf builds are used.
