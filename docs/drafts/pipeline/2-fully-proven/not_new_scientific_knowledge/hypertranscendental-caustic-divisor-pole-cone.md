# A zero is a finite-width pole cone in the projective-horizon caustic tower

- **ID:** `hypertranscendental-caustic-divisor-pole-cone`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / LOCAL DIVISOR GEOMETRY / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [FORMAL CORE COMPLETE]`
- **Parents:** `projective-horizon-rectangular-schur-caustic`,
  `hypertranscendental-horizon-q-system`
- **Lane:** analytic source marking of the static projective-horizon constraint

## Statement

Let `f` be holomorphic near `rho`, not identically zero, and suppose that `rho` is a zero of exact
multiplicity `r>=1`.  Away from the zero define

```text
Z_s(t)=f(s)/f(s+t),
h_k(s)=[t^k] Z_s(t)^2,
tau_(m,n)(s)=det(h_(n+a-b)(s))_(0<=a,b<m),                 (1)
```

where `h_k=0` for negative `k`.  Assume `tau_(m,n)` is not identically zero, as is automatic when
`f` is hypertranscendental.  With `ord_rho` positive on zeros and negative on poles,

```text
ord_rho tau_(m,n)=-mn          if 1<=m<=2r,
ord_rho tau_(m,n)>-mn          if m>2r.                    (2)
```

Thus, for every fixed `n>=1`, the zero multiplicity is recovered from divisor orders alone:

```text
2r=max {m>=1 : -ord_rho tau_(m,n)=mn}.                     (3)
```

If in addition `f(s)=f(1-s)`, then the whole tower obeys

```text
tau_(m,n)(1-s)=(-1)^(mn) tau_(m,n)(s).                     (4)
```

The divisors are therefore reflection invariant even though the functions carry a parity grading.

## Proof of the pole cone

Write `s=rho+u` and factor

```text
f(rho+u)=u^r g(u),       g(0)!=0.                           (5)
```

After the source-scaled substitution `t=uz`,

```text
Z_(rho+u)(uz)^2
 =(1+z)^(-2r) (g(u)/g(u(1+z)))^2.                          (6)
```

The second factor tends coefficientwise to one as `u->0`.  Since the coefficient of `z^k` on the
left is `u^k h_k(rho+u)`, the binomial series gives

```text
lim_(u->0) u^k h_k(rho+u)
 =(-1)^k choose(2r+k-1,k).                                 (7)
```

Every determinant term in `(1)` has total weight

```text
sum_(a=0)^(m-1) (n+a-sigma(a))=mn.                         (8)
```

Multiplying `(1)` by `u^(mn)` and using `(7)` therefore yields

```text
lim_(u->0) u^(mn) tau_(m,n)(rho+u)
 =(-1)^(mn) s_((n^m))(1^(2r)).                             (9)
```

The hook-content formula specializes the last factor to

```text
s_((n^m))(1^(2r))
 =product_(1<=i<=m,1<=j<=n)
    (2r+j-i)/(m+n-i-j+1).                                  (10)
```

It is nonzero exactly when `m<=2r`: all factors are then positive, while for `m>2r` the box
`(i,j)=(2r+1,1)` contributes zero.  Equations `(9)--(10)` give `(2)`.  Non-identical vanishing makes
the order finite when the leading coefficient cancels.  Equation `(3)` follows immediately.

For a hypertranscendental `f`, non-identical vanishing follows because `tau_(m,n)` is a nonzero
rectangular Schur polynomial in the triangular reciprocal-jet coordinates.  An identity
`tau_(m,n)(s)=0` would pull back through that invertible triangular coordinate change to a nonzero
algebraic differential equation for `f`.

## Proof of reflection parity

The functional equation gives

```text
Z_(1-s)(t)=f(1-s)/f(1-s+t)=f(s)/f(s-t)=Z_s(-t),            (11)
```

so `h_k(1-s)=(-1)^k h_k(s)`.  In the determinant, every permutation has the same total weight
`mn` by `(8)`, proving `(4)`.  Equivalently, the reflected Toeplitz matrix is diagonal sign
conjugate to the original matrix with an overall scalar `(-1)^n`; this stronger matrix identity is
the Lean certificate.

## Tropical Q-system boundary

The adjacent Desnanot--Jacobi identity tropicalizes at every discrete valuation `nu` to

```text
2 nu_(m,n) >= min(
  nu_(m,n-1)+nu_(m,n+1),
  nu_(m-1,n)+nu_(m+1,n)),                                  (12)
```

with equality when the two arguments of `min` differ.  Inside the pole cone both candidate sums
equal `-2mn`.  At its boundary `m=2r`, the horizontal candidate remains `-2mn` while the vertical
candidate is strictly larger, so the Q-system selects the horizontal continuation uniquely.  The
zero is therefore a finite-width tropical rank defect of the caustic tower.

## Scientific boundary

The pole-width formula is a clean source-marked interpretation of a zero, but it does not pass the
dual novelty-significance gate.  Binomial local models, Jacobi--Trudi determinants, the
hook-content cutoff, and valuation tropicalization are classical.  Their conjunction gives useful
language for the new projective-horizon program, but `(3)` repackages local multiplicity rather
than discovering a new obstruction or classification theorem for hypertranscendental functions.

The physical content is correspondingly static: a zero is a codimension-one source singularity
whose multiplicity is the transverse width of the maximal caustic-pole cone.  No time evolution,
quantization, black-hole entropy, or holographic dynamics has been derived.

## RH impact

For the completed zeta function, `(3)` recovers the multiplicity of every zero from the caustic
divisor spectrum, and `(4)` reflects each cone through `s -> 1-s`.  RH is exactly the additional
claim that all cone apices are fixed by the conjugate-reflection symmetry.  The construction
records the zero divisor but supplies no mechanism forcing its apices onto the critical line, so it
has no positive RH consequence.

## Lean verification

`ProjectiveHorizonCausticReflection.lean` proves the diagonal-conjugation identity and the exact
determinant sign `(-1)^(mn)` over every commutative ring.  The analytic local factorization and
hook-content specialization remain paper-level.  A targeted leaf check passes; no full build was
run.
