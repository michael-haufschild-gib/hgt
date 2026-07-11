# The prime-log Cauchy seam has infinite renormalization rank

- **ID:** `prime-log-cauchy-seam-infinite-renormalization-rank`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** `PrimeLogHerglotz.lean`,
  `euler-log-prime-power-herglotz-half-weight-law.md`, and the prime-power-series
  convergence threshold
- **Statement:** After every positive exponential transport, the Cauchy sections of the
  prime-log carrier are finitely linearly independent modulo the prime square-summable space.
  Consequently every additive prime-side renormalization that repairs all Cauchy sections must
  have infinite-dimensional correction range.

## 1. Transported Cauchy sections

Let `P` be the set of rational primes and put

```text
S = C^P,
H = ell^2(P) subset S.
```

For `b>0` and `z` off the positive real prime-log support, define

```text
v_(b,z)(p)=p^(b-1/2)/(log p-z).                            (1)
```

The exponent `p^(-1/2)` is the square root of the exponent-one Euler weight. Multiplication by
`p^b=exp(b log p)` is positive exponential transport toward the critical center. At the CCM
half-weight, `b=1/2`.

## 2. Finite-packet divergence theorem

Let `z_1,...,z_n` be distinct points in the open upper half-plane and let
`c_1,...,c_n` be complex numbers, not all zero. Then

```text
sum_(p in P) |sum_(j=1)^n c_j v_(b,z_j)(p)|^2 = infinity. (2)
```

In particular, no nonzero finite linear combination of the transported Cauchy sections belongs
to `H`.

### Proof

Put

```text
R(t)=sum_(j=1)^n c_j/(t-z_j)=Q(t)/D(t),
D(t)=product_(j=1)^n (t-z_j),
Q(t)=sum_(j=1)^n c_j product_(k!=j)(t-z_k).               (3)
```

The numerator is nonzero. Indeed, for every `j`,

```text
Q(z_j)=c_j product_(k!=j)(z_j-z_k).                       (4)
```

Distinctness of the nodes makes the product in `(4)` nonzero, so `Q=0` would force every
`c_j=0`.

Write `q=deg Q` and `m=n-q`. Then `1<=m<=n`. Since `D` is monic of degree `n`, rational
asymptotics at real infinity give

```text
t^m R(t) -> leadingCoeff(Q) != 0.                         (5)
```

Therefore there are constants `A>0` and `T>0` such that

```text
|R(t)|^2 >= A/t^(2m),   t>=T.                            (6)
```

For every sufficiently large prime,

```text
|sum_j c_j v_(b,z_j)(p)|^2
 =p^(2b-1)|R(log p)|^2
 >=A p^(2b-1)/(log p)^(2m).                              (7)
```

Set `epsilon=b/(2m)>0`. The elementary estimate

```text
log x <= x^epsilon/epsilon                               (8)
```

implies

```text
(log p)^(2m) <= epsilon^(-2m) p^b.                       (9)
```

Combining `(7)` and `(9)` gives, outside a finite set of primes,

```text
|sum_j c_j v_(b,z_j)(p)|^2 >= A epsilon^(2m) p^(b-1).    (10)
```

The prime series `sum_p p^r` converges exactly for `r<-1`. Here `r=b-1>-1`, so the lower
bound in `(10)` is nonsummable. This proves `(2)`. `QED`

## 3. Infinite quotient rank

Let brackets denote classes in `S/H`. For every fixed `b>0`, the family

```text
{[v_(b,z)] : Im z>0}                                     (11)
```

is finitely linearly independent. Hence its span in `S/H` has infinite algebraic dimension.

This is immediate from `(2)`: a finite relation among the classes says exactly that the
corresponding finite linear combination lies in `H`.

## 4. Positive renormalization obligation

Let `F` be a linear subspace of `S`. Suppose a prime-side additive renormalization uses corrections
from `F` and repairs every upper-half-plane Cauchy section:

```text
for every z with Im z>0, there exists f_z in F such that
v_(b,z)-f_z belongs to H.                                (12)
```

Then `F` is infinite-dimensional. Indeed, `(12)` places every class in `(11)` in the image of
`F` under the quotient map `S -> S/H`, while `(11)` has infinite-dimensional span.

Thus a successful CCM seam must positively carry an infinite-dimensional correction resource.
It may take the form of

```text
an infinite prime--Gamma coupling,
a relative or indefinite completion performed before the Hilbert norm,
an infinite-dimensional operator/test space,
or a global divisor-marked constraint not representable by finite-rank additive correction.
                                                                    (13)
```

The theorem does not merely say that the naive half-weight transport fails. It says what any
prime-coordinate sewing that succeeds for the complete Cauchy family is forced to contain:
**infinite renormalization rank**.

## 5. Scope

The theorem concerns additive corrections in the common prime-sequence space modulo the ordinary
positive `ell^2` norm. It does not exclude a distributional continuation, an indefinite relative
trace, a nonorthogonal quotient completed only after prime--Gamma sewing, or the exact global CCM
determinant. Those mechanisms evade `(12)` only by changing the carrier category; they must still
exhibit the infinite resource replacing the quotient rank in `(11)`.

In particular, “finite-degree Gamma completion” is excluded only when its lift to prime coordinates
has finite-dimensional correction range. A nonlocal Gamma-sewn operator may have infinite rank;
the theorem requires that rank to be shown rather than inferred from the scalar Gamma factor.

## 6. Relation to the existing transport wall

The formal theorem

```text
not_summable_primeLogHerglotzTransportMass_of_pos
```

is the one-section case, with the normalized node `z=i`. The present theorem proves that no finite
Cauchy packet can cancel that wall. The Lean strengthening required for the analytic core is the
all-finite-order statement

```text
sum_p p^(2b-1)/(1+(log p)^2)^m = infinity
for every b>0 and m in N.                                (14)
```

Equation `(14)` is sufficient for every finite rational cancellation order after the numerator
nonvanishing and order-at-infinity steps in `(3)`--`(6)`.

## 7. Scientific classification

The exact prime-log quotient statement was not found in the initial search against the CCM,
weighted-Cauchy-transform, matrix-Herglotz, and finite-Euler-product literature. That is not enough
to certify novelty. The proof reduces to classical partial fractions, rational asymptotics, and the
prime-power-series threshold, so the parent-theory gate may ultimately classify it as a bridge.

Its route significance is sharper than the one-section wall: it excludes every finite-rank
prime-side additive seam repair and identifies the minimum carrier dimension of a successful
renormalization. Scientific novelty remains `[NOVELTY UNVERIFIED]` pending a wider exact literature
and parent-theory audit.

## Gates

- [x] finite-packet numerator proved nonzero
- [x] exact finite order at infinity isolated
- [x] every nonzero finite packet proved nonsquare-summable after positive transport
- [x] quotient family proved finitely linearly independent
- [x] finite-rank additive renormalization excluded
- [x] formalize the all-finite-order prime-series core `(14)` as
  `not_summable_primeLogHerglotzTransportMassOrder_of_pos`
- [ ] formalize the full rational-packet quotient theorem
- [ ] audit weighted Cauchy-transform and renormalized-resolvent literature more broadly
- [ ] construct the infinite marked prime--Gamma seam carrier
- [ ] transport its complete inertia into the screw spaces
- [ ] RH

## Log

- 2026-07-11 -- extracted from the line-211 prime-log pole carrier and strengthened the scalar
  positive-transport wall to an infinite renormalization-rank theorem.
- 2026-07-11 -- formalized the all-finite-order analytic core in `PrimeLogHerglotz.lean`.
