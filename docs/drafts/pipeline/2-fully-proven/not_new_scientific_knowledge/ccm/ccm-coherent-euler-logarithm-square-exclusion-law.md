# A CCM factorization must resolve the Euler logarithm before squaring

- **ID:** `ccm-coherent-euler-logarithm-square-exclusion-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the weighted prime-shift realization, the logarithmic position commutator,
  the prime number theorem, and the arithmetic-complement carrier law
- **Statement:** The coherently summed finite-aperture Euler logarithm has exponentially large norm
  on a fixed left-boundary packet even though its prime commutator form vanishes on that packet.
  Consequently the completed Weil form cannot be a positive remainder plus one square
  `||alpha_A X_A-alpha_A^(-1)Z_A||^2`, for any aperture-dependent scalar `alpha_A>0`. A successful
  CCM Gram construction must resolve the growing arithmetic channels before squaring, or carry an
  exact prime--prime covariance cancellation.

## Unweighted aperture carrier

Put

```text
K_A=L2([0,A],dx),
(V_(A,h)f)(x)=1_(h<=x<=A)f(x-h),
(X_Af)(x)=x f(x).                                             (1)
```

The unitary removal of the critical weight in
`critical-euler-position-commutator-carrier-law.md` sends the skew Euler logarithm to

```text
Z_A
 =sum_(2<=n<e^A) Lambda(n)/(sqrt(n) log n)
    (V_(A,log n)-V_(A,log n)^*).                              (2)
```

For `n=p^k`, the coefficient in `(2)` is

```text
1/(k p^(k/2)).                                                (3)
```

The exact commutator is

```text
[X_A,Z_A]
 =sum_(2<=n<e^A) Lambda(n)/sqrt(n)
    (V_(A,log n)+V_(A,log n)^*).                              (4)
```

## Fixed boundary packet

Choose

```text
0<delta<log 2                                                   (5)
```

and a nonnegative smooth unit vector `f` supported in `(0,delta)` such that

```text
f(x)>=m>0  on [delta/3,2 delta/3].                              (6)
```

Use the same zero-extended vector in every `K_A` with `A>delta`.

Every shift in `(2)` has length at least `log 2>delta`. Hence

```text
V_(A,log n)^*f=0,
supp(V_(A,log n)f) intersection supp(f)=empty.                  (7)
```

It follows immediately from `(4)` that

```text
< [X_A,Z_A]f,f>=0.                                             (8)
```

Thus the actual prime contribution to the completed quadratic form vanishes on this packet at
every aperture.

## Coherent right-boundary amplification

For large `A`, consider the primes in the logarithmic interval

```text
P_A={p prime:A-2 delta/3<=log p<=A-delta/2}.                    (9)
```

If

```text
A-delta/6<=x<=A,
p in P_A,                                                      (10)
```

then

```text
delta/3<=x-log p<=2 delta/3.                                   (11)
```

All coefficients in `(2)` are positive and `(7)` deletes every backward-shift contribution.
Equations `(6)` and `(11)` therefore give the pointwise lower bound

```text
|Z_Af(x)|
 >=m sum_(p in P_A) p^(-1/2)                                  (12)
```

on the entire interval in `(10)`.

The prime number theorem gives constants `c_delta>0` and `A_delta` such that

```text
#P_A>=c_delta e^A/A                                           (13)
```

for `A>=A_delta`. Since every prime in `(9)` is at most `e^(A-delta/2)`, equations
`(12)`--`(13)` imply

```text
||Z_Af||_2>=C_delta e^(A/2)/A.                                (14)
```

The lower bound uses only the exponent-one prime shell. Prime-power terms can only increase the
pointwise value on the nonnegative packet.

## Exact exclusion of the coherent square

For every real `alpha>0`, self-adjointness of `X_A` and skew-adjointness of `Z_A` give

```text
(alpha X_A-alpha^(-1)Z_A)^*
 (alpha X_A-alpha^(-1)Z_A)
 =alpha^2 X_A^2-[X_A,Z_A]+alpha^(-2)Z_A^*Z_A.                  (15)
```

On the packet `f`, the vectors `X_Af` and `Z_Af` have disjoint supports by `(7)`. Therefore

```text
||(alpha X_A-alpha^(-1)Z_A)f||_2^2
 =alpha^2||X_Af||_2^2+alpha^(-2)||Z_Af||_2^2
 >=2||X_Af||_2||Z_Af||_2.                                    (16)
```

The fixed vector has `||X_Af||_2=||xf||_2>0`, independently of `A`. Combining `(14)` and `(16)`
gives

```text
inf_(alpha>0)||(alpha X_A-alpha^(-1)Z_A)f||_2^2
 >=C_f e^(A/2)/A.                                            (17)
```

Let `q_arch` be the fixed completed archimedean/pole form transported to the unweighted carrier.
The smooth compactly supported packet lies in its form domain, and aperture restriction by zero
extension does not change its value. Thus

```text
q_A(f)
 =q_arch(f)-<[X_A,Z_A]f,f>
 =q_arch(f),                                                 (18)
```

a finite constant independent of `A`.

Suppose there were positive scalars `alpha_A` and nonnegative quadratic forms `r_A` such that on a
common core

```text
q_A(g)
 =||(alpha_A X_A-alpha_A^(-1)Z_A)g||_2^2+r_A(g).              (19)
```

Applying `(19)` to `f` contradicts `(17)`--`(18)` for large `A`. Therefore no factorization of the
form `(19)` exists, even when the balancing scalar is allowed to depend arbitrarily on the aperture.

## Positive carrier law

The failure is not caused by the linear prime term. That term is exactly zero on `f`. It is caused
by squaring the **coherent sum** in `(2)`: the high-prime translates overlap on one right-boundary
packet and create large prime--prime cross terms which are absent from the completed Weil form.

Consequently every successful CCM Gram construction must perform at least one of the following
before taking positive squares:

1. map distinct prime-log directions into a growing channel space in which the relevant boundary
   outputs are separated or have a source-defined covariance;
2. retain a nontrivial covariance operator whose off-diagonal prime--prime terms cancel the
   coherent energy exactly.

In the first case, faithfulness of the source forces the channel carrier at cutoff `N` to contain

```text
A_N=V_N/(V_N intersection D)                                  (20)
```

and hence to have rational rank at least

```text
pi(N)-delta_beta-2m(n+1).                                    (21)
```

Allowing the channel carrier to be singular does not remove this cofinal cost. Under the precise
hypotheses of `singular-autonomous-ade-kolchin-frequency-law.md`, if a scalar almost-periodic
realization or a continuous equivariant observable retains `V_N` and satisfies a nonzero autonomous
implicit ADE `P_N=0`, then its compatible jet tower has Kolchin capacity

```text
kappa(P_N)>=ceil(pi(N)/2).                                   (22)
```

Thus channel resolution has two positive realizations. It may be stored in a cofinally growing
singular jet variety, or it must remain visible in an infinite-dimensional/nonautonomous carrier:
the Sonin operator algebra, the Weil test space, the determinant/divisor object, or a global
non-flow constraint. A fixed singular equation is not a third finite-state option.

The direct-sum feature maps in `ccm-compressed-prime-shift-arithmetic-complement-law.md` have the
correct channel geometry. The open theorem is not their existence; it is the completed
Gamma--prime contraction and its index-preserving transport to the true restricted-Weil form.

The Sonin three-grade carrier supplies the second possible language: its principal Calkin shell
retains the coherent symbol, while the degree-one relative functional and positive residual energy
record the covariance correction without forcing the principal shell into one Hilbert-space square.

## Attack and scope

- `[PROVED]` A single coherent position/Euler square is impossible for the actual coefficients and
  growing aperture.
- `[PROVED]` The obstruction persists under every scalar balancing `alpha_A`.
- `[PROVED]` The witness has zero prime commutator form, so the contradiction is entirely created
  by spurious quadratic prime--prime energy.
- `[NOT PROVED]` The theorem does not exclude a growing direct-sum contraction, an operator-valued
  covariance, or the three-grade relative construction.
- `[NOT PROVED]` It does not prove positivity of the completed form or RH.

## Scientific classification

The proof is an elementary boundary-packet estimate using the prime number theorem and the standard
completion-of-squares identity. It is a route bridge, not new scientific knowledge. Its value is
positive route selection: it proves that the Euler logarithm must remain channel-resolved through
the factorization rather than being coherently summed and then squared.

## Lean decision

The formal tree does not yet contain the weighted logarithmic shift carrier, the completed
archimedean form, or the aperture-dependent Euler logarithm. Formalizing only `(15)` would be a
generic algebraic wrapper and would not certify the exclusion theorem. No Lean file is added before
the actual analytic carrier is represented.

## Gates

- [x] fixed boundary packet constructed
- [x] prime commutator form proved zero on the packet
- [x] coherent Euler-logarithm norm lower bound proved
- [x] arbitrary scalar balancing excluded
- [x] positive channel-resolution alternative stated
- [x] singular autonomous jet-capacity floor attached
- [ ] construct the growing channel contraction or exact covariance cancellation
- [ ] transport its negative index to Suzuki's restricted-Weil operator
- [ ] prove RH
