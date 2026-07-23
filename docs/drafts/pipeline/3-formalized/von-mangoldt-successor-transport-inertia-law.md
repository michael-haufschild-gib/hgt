# Von Mangoldt successor transport inertia law

- **ID:** `von-mangoldt-successor-transport-inertia-law`
- **Stage:** 3-formalized
- **Parent:** `SR-40`; `von-mangoldt-successor-principal-relative-hankel-current.md`
- **Type:** `[EXACT SIGNATURE LAW] [SR-41 COMPLETION NO-GO]`
- **Scientific status:** `[PAPER PROOF CLOSED] [LEAN CLOSED] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`

## Claim

Put

```text
w_n = Lambda(n)/n,                  x_n = log(n),

R_M(i,j)
 = sum_(n=2)^(M+1) w_n
     (x_(n+1)^(i+j+2)-x_n^(i+j+2)),
                                            0 <= i,j <= M.
```

Define endpoint-divergence weights on `m=2,...,M+2` by

```text
d_2     = -w_2 x_2^2,
d_m     = (w_(m-1)-w_m)x_m^2,       3 <= m <= M+1,
d_(M+2) = w_(M+1)x_(M+2)^2.
```

Let `V_M(m,i)=x_m^i`. Then

```text
R_M = V_M^T diag(d_2,...,d_(M+2)) V_M.                 (1)
```

The nodes `x_2,...,x_(M+2)` are distinct, so `V_M` is invertible. Consequently

```text
kappa_-(R_M) = #{m : d_m<0},
kappa_0(R_M) = #{m : d_m=0},
kappa_+(R_M) = #{m : d_m>0}.                           (2)
```

In particular:

1. `d_2<0`, hence every nonempty full-jet section `R_M` is indefinite or negative
   semidefinite and is never positive semidefinite.
2. If `p>3` is prime and `p=3 mod 4`, then `w_(p-1)=0<w_p`, hence `d_p<0`.
3. Infinitely many primes are `3 mod 4`, so `kappa_-(R_M)` is unbounded as `M` grows.
4. No positive completion can have all `R_M` as compressions.
5. No fixed-index Pontryagin completion can have all `R_M` as compatible compressions.
   Any surviving `SR-41` completion must have genuinely infinite Krein index.

## Proof

For each matrix entry,

```text
R_M(i,j)
 = sum_(n=2)^(M+1) w_n
     ((x_(n+1)^(i+1))(x_(n+1)^(j+1))
       -(x_n^(i+1))(x_n^(j+1))).
```

Collect the coefficient of each endpoint `x_m`. The left endpoint contributes `-w_2`,
an interior endpoint contributes `w_(m-1)-w_m`, and the right endpoint contributes
`w_(M+1)`. Pulling one factor `x_m` into each Vandermonde feature gives exactly `(1)`.
Strict monotonicity of the logarithm makes the Vandermonde matrix invertible. Sylvester's
law of inertia proves `(2)`.

Since `2` is prime, `w_2>0` and `x_2>0`, so `d_2<0`. Now let `p>3` be prime with
`p=3 mod 4`. The even integer `p-1` is congruent to `2 mod 4`. If it were a prime
power, its prime base would have to be `2`; but every power `2^k>2` is divisible by
`4`, while `p-1>2`. Thus `p-1` is not a prime power, so

```text
w_(p-1)=0,             w_p=log(p)/p>0,
```

and `d_p<0`. Euclid's theorem for primes in the progression `3 mod 4` supplies
arbitrarily many such negative coordinates. This proves unbounded negative index.

A compression of a positive semidefinite form is positive semidefinite, contradicting the
first negative coordinate. More generally, a compression cannot have negative index larger
than its ambient Pontryagin index. Equation `(2)` therefore excludes every fixed-index
completion.

## Why this changes `SR-41`

`SR-40` called the cofinal current signed but did not classify its finite signature. The result
above is stronger than generic indefiniteness:

```text
positive bivariate prime--jet completion             impossible,
fixed-index Pontryagin completion                    impossible,
inclusion-compatible completion of all full jets     infinite-index Krein only.
```

The coherent odd Gamma--Jacobi marginal from `SR-38` is positive. It cannot repair the jet
marginal inside a positive block completion because compression preserves positivity. Any
source connector must therefore perform an indefinite, infinite-index coupling before either
marginal is read.

This does not construct that coupling, prove the completed Euler trace, force the co-Poisson
fibre orientation, or prove RH. It removes two entire realization classes from the live
backward chain.

## Novelty boundary

The factorization of a finite signed atomic moment matrix by a Vandermonde matrix and the
resulting Sylvester-inertia count are classical. A representative modern source is D. P.
Kimsey, *On a minimal solution for the indefinite truncated multidimensional moment problem*,
especially the signed atomic representation and inertia discussion around Corollary 7.5.

Targeted corpus and literature searches found no application to the successor current

```text
sum_n Lambda(n)/n * (log(n+1)^q-log(n)^q),
```

no endpoint-divergence signature formula `(2)`, and no resulting infinite-index obstruction
for a prime--jet completion. Generic inertia is `PARENT`; exact von Mangoldt transport
composition and the `SR-41` consequence are the provisional contribution.

## Falsifiers

- endpoint collection yields a coefficient other than `d_m`;
- full jet dimension is not the number of endpoint nodes;
- logarithmic nodes collide;
- some prime `p>3`, `p=3 mod 4`, has `p-1` a prime power;
- a positive or fixed-index completion can contain compressions of unbounded negative index.

## Gates

- [x] exact paper factorization
- [x] exact finite inertia count
- [x] unbounded negative index without analytic estimates
- [x] positive and fixed-index completion no-go
- [x] internal collision audit
- [x] generic-parent literature calibration
- [x] formalize generic signed-atomic inertia interface
- [x] specialize to actual `SR-40` matrix
- [x] formalize unbounded negative index from primes `3 mod 4`
- [x] wire HTGeometry and RHTower umbrellas
- [x] targeted direct Lean, axiom, and cached leaf-module audit
- [ ] global lint baseline clean (currently blocked by unrelated pre-existing unreachable modules)
