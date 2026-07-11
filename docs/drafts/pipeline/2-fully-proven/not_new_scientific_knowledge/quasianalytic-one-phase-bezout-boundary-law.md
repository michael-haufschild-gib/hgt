# A quasianalytic one-phase field has a polynomial projective boundary

- **ID:** `quasianalytic-one-phase-bezout-boundary-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [BRIDGE]`
- **Statement:** Let `E` be a meromorphic coefficient field with an injective complete Laurent
  Poincare expansion at upper infinity, and let `u_theta(s)=s^(i theta)`, `theta>0`, be transcendental
  over `E`. Every finite nonzero tuple in `E(u_theta)` has, along every sequence of upper heights, a
  nonzero polynomial functional-projective limit after a subsequence. Hence its upper projective
  boundary has the positive two-stage carrier

  ```text
  E(u_theta) -> C[z] -> C.
  ```

  Common beyond-all-orders behavior is necessarily a projective scalar; the primitive residual
  tuple is forced to expose a finite polynomial jet.

## 1. Upper Poincare coefficient fields

Let `E` be a field of meromorphic functions on an upper half-plane. Assume that every nonzero
`b in E` has a unique complete Laurent Poincare expansion

```text
hat b(s)=sum_(nu=nu_0)^infinity c_nu s^(-nu),
c_(nu_0)!=0,                                               (1)
```

with the following uniform translated meaning: for every `R>0` and every requested `L`, truncating
far enough gives

```text
b(z+iS)=T_(b,S,L)(z)+O_R(S^(-L))                          (2)
```

uniformly for `|z|<=R`, where `T_(b,S,L)` is a polynomial in `z` of degree bounded independently of
`S`. The asymptotic map `b|->hat b` is assumed injective and compatible with field operations.

These hypotheses imply that every nonzero element of `E`, and its reciprocal, has at most polynomial
growth on upper vertical tubes. Indeed its first Laurent monomial in `(1)` is nonzero. Call such an
`E` an **upper Poincare field**.

Fix `theta>0`, choose the principal logarithm in the upper half-plane, and put

```text
u(s)=s^(i theta).                                          (3)
```

Assume that evaluation embeds the polynomial ring `E[U]` into meromorphic functions by `U|->u`.
Equivalently, `u` is transcendental over `E`. Since

```text
u(z+iS)=(iS)^(i theta)(1+z/(iS))^(i theta),                (4)
```

`u` is bounded above and below on every upper vertical tube and has a complete `1/S` expansion whose
coefficients are polynomials in `z`.

## 2. Primitive phase tuples have algebraic-order survival

Let

```text
F=(F_1,...,F_r) in E(u)^r                                 (5)
```

be nonzero. Clear one common denominator:

```text
F_j=P_j(u)/Q(u),  P_j,Q in E[U],                           (6)
```

with the polynomial tuple `P=(P_1,...,P_r)` nonzero. Since `E[U]` is Euclidean, let

```text
h=gcd(P_1,...,P_r),
R_j=P_j/h.                                                 (7)
```

The residual tuple is primitive. Therefore there are `A_1,...,A_r in E[U]` with

```text
sum_j A_j R_j=1.                                           (8)
```

`[PROVED]` There are constants `C>0` and `M>=0` such that, for every sufficiently large `S`,

```text
max_j |R_j(iS)| >= C S^(-M).                               (9)
```

### Proof

Every coefficient of every `A_j` has polynomial growth by Section 1, while `u(iS)` remains on the
fixed circle of radius `exp(-pi theta/2)`. Hence

```text
max_j |A_j(u(iS))|<=C_1 S^M                               (10)
```

for suitable `C_1,M`. Evaluate `(8)` at `iS` away from the finitely many eventual poles. Then

```text
1<=sum_j |A_j(u(iS))| |R_j(u(iS))|
 <=r C_1 S^M max_j |R_j(u(iS))|,                           (11)
```

which proves `(9)`. Meromorphic identity extends the conclusion across removable exceptional
points. The content of `(9)` is positive: a primitive phase tuple always carries a component of
finite algebraic height order.

## 3. Finite-order survival forces a polynomial jet

Let `S_n->+infinity` be arbitrary. For every requested `L`, equations `(1)`--`(4)` give translated
expansions

```text
R_j(z+iS_n)=T_(j,n,L)(z)+O_R(S_n^(-L)),                   (12)
```

uniformly for `|z|<=R`, where all `T_(j,n,L)` lie in one finite-dimensional polynomial space
`C[z]_(<=d_L)`. The degree `d_L` depends on the fixed tuple and `L`, but not on `n`.

Choose `L>M+1`, with `M` from `(9)`. Let `rho_n` be the maximum absolute value of all coefficients
of the finite polynomial tuple

```text
T_(n,L)=(T_(1,n,L),...,T_(r,n,L)).                         (13)
```

By `(9)` and `(12)`,

```text
rho_n>=C_2 S_n^(-M)                                       (14)
```

for all large `n`. The normalized coefficient vectors `rho_n^(-1)T_(n,L)` lie in the unit sphere of
a fixed finite-dimensional complex vector space. After a subsequence they converge to the
coefficient vector of a nonzero tuple

```text
H=(H_1,...,H_r) in C[z]^r\{0}.                             (15)
```

Moreover `(12)` and `(14)` give

```text
rho_n^(-1) O_R(S_n^(-L))=O_R(S_n^(M-L))->0.                (16)
```

Thus

```text
rho_n^(-1)(R_1(z+iS_n),...,R_r(z+iS_n))->H(z)              (17)
```

locally uniformly.

Returning through `(6)`--`(7)`, the meromorphic functional normalization

```text
c_n(z)=Q(u(z+iS_n))/(rho_n h(u(z+iS_n)))                   (18)
```

turns the original tuple into the residual tuple in `(17)`. Therefore every finite nonzero tuple in
`E(u)^r` has a nonzero polynomial functional-projective boundary along every upper-height sequence.

## 4. The terminal polynomial carrier is one point

`[PROVED]` Every finite nonzero polynomial tuple `H in C[z]^r` has a one-point upper projective
boundary. If `d=max_j deg H_j`, then

```text
(iT)^(-d)(H_1(z+iT),...,H_r(z+iT))->(a_1,...,a_r),         (19)
```

where `a_j` is the leading coefficient of `H_j` when `deg H_j=d` and is zero otherwise. The vector
`a` is nonzero. Combining `(17)` and `(19)` gives the carrier chain

```text
E(u) -> C[z] -> C.                                         (20)
```

This is boundary depth, not a uniform degree bound: different fixed tuples can expose polynomial
jets of arbitrarily high degree.

## 5. Positive carrier law

The theorem identifies the resources rather than merely excluding a failure mode:

> **Primitive one-phase carrier law.** Finite algebraic phase degree over a quasianalytic Poincare
> coefficient field forces every primitive finite tuple to expose a finite polynomial jet. Every
> common flat or Stokes-scale factor belongs to the scalar projective normalization and contributes
> no residual projective direction.

Thus the carrier has two independent coordinates:

```text
compact logarithmic phase -> noncompact polynomial jet -> constant point.   (21)
```

The first arrow is controlled by polynomial gcd and Bezout primitivity; the second is controlled by
ordinary polynomial degree.

## 6. Attacks and sharp boundary

1. **Quasianalyticity is load-bearing.** If a nonzero coefficient can have zero Poincare expansion,
   its inverse can grow faster than every power and the Bezout estimate `(9)` disappears.
2. **One phase is load-bearing.** `E[U]` is a principal ideal domain. With two independent phases,
   a finite tuple can generate a nonprincipal ideal with a positive-dimensional exceptional set;
   ideal resolution or a genuinely multivariate replacement is then required.
3. **Finite phase degree is load-bearing.** Infinite character series need not live in one fixed
   finite-dimensional translated-jet space.
4. **Arbitrary phase synchronization is included.** No rate assumption is imposed on the cluster of
   `(iS_n)^(i theta)`; the coefficient-vector normalization absorbs every relative rate.
5. **Moving zeros and poles are included.** The normalization `(18)` is meromorphic and the identity
   is projective. Common zeros belong to `h`; common poles belong to `Q`.
6. **The polynomial degree need not be bounded across the field.** The theorem asserts finite degree
   for each finite tuple, exactly the amount needed for a second recession.
7. **The conclusion is functional.** Normalizing only at `z=0` is insufficient because cancellations
   there can expose lower-order derivatives. Normalizing the whole finite coefficient vector in
   `(13)` is what gives compact-open convergence.

## 7. Parent and novelty audit

`[BRIDGE]` The proof is a direct synthesis of three classical mechanisms:

- complete Poincare asymptotic expansions and their closure under field operations;
- polynomial gcd and Bezout identity over the one-variable Euclidean ring `E[U]`;
- compactness of the unit sphere in a finite-dimensional polynomial coefficient space.

Preliminary exact searches did not locate the functional-projective formulation `(17)`--`(21)`, but
the proof introduces no mechanism beyond these parents. It therefore fails the parent-theory gate
for new scientific knowledge and is classified as a proved bridge. Its scientific use is to remove
an unnecessary resurgent-resolution hypothesis from concrete one-phase HT fields and to isolate the
multiphase ideal as the genuine open boundary.

## 8. Lean status

The tree contains polynomial gcd/Bezout infrastructure and several finite projective-limit lemmas,
but no general upper Poincare field interface, translated complete-asymptotic jet object, or
functional-projective convergence theorem. The whole claim is not formalized, so the card remains in
stage 2.

## Gates

- [x] upper Poincare field defined
- [x] common denominator and gcd normalization proved
- [x] Bezout algebraic-order survival proved
- [x] finite translated-jet compactness proved
- [x] polynomial functional-projective limit proved for arbitrary height sequences
- [x] terminal one-point boundary proved
- [x] smallest and degenerate cases attacked
- [x] parent-theory gate applied; classified BRIDGE
- [ ] complete unconditional Lean formalization
