# Critical projective-horizon ramification is a rectangular Schur caustic

- **ID:** `projective-horizon-rectangular-schur-caustic`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXACT RAMIFICATION EQUATION
- **Scientific status:** `[PROVED ON PAPER] [BRIDGE] [FORMAL CORE COMPLETE]`
- **Parents:** `projective-horizon-finite-jet-page-transition`,
  `projective-horizon-critical-binomial-multiplicity`
- **Lane:** source-pure hypertranscendental geometry; static caustic topology

## Theorem

Let `m,n>=1`, `L=m+n`, and let `Y=X^-1 mod t^L` be a unit reciprocal jet over a
characteristic-zero field.  Hold the observed raw tail `x_m,...,x_(L-1)` fixed and vary the low
source coordinates `x_0,...,x_(m-1)`.  Put

```text
c_k=[t^k]Y(t)^2,       c_k=0 for k<0.
```

The differential of the complementary reciprocal packet is

```text
delta y_(n+r)=-sum_(i=0)^(m-1)c_(n+r-i) delta x_i,
0<=r<m.                                                       (1)
```

Consequently its critical Jacobian is

```text
J_(m,n)(Y)=(-c_(n+r-i))_(0<=r,i<m),                           (2)
```

and

```text
det J_(m,n)(Y)=(-1)^m det(c_(n+r-i))_(0<=r,i<m).              (3)
```

Normalize `Y=y_0 Z`, where `Z(0)=1`, and write `h_k=[t^k]Z^2`, with `h_0=1`.  Then

```text
det J_(m,n)(Y)=(-1)^m y_0^(2m)
  det(h_(n-i+j))_(1<=i,j<=m)
=(-1)^m y_0^(2m) s_((n^m))[h].                               (4)
```

The ramification locus of the complete critical raw/reciprocal observation map on the unit-jet
chart is therefore exactly the rectangular Jacobi--Trudi divisor

```text
s_((n^m))[h]=0.                                               (5)
```

The divisor is proper: the exponential/Pascal point from the finite Page theorem has nonzero
determinant.

## Proof

Differentiate the static inverse constraint `XY=1 mod t^L`:

```text
(delta X)Y+X(delta Y)=0 mod t^L.
```

Multiplication by `Y` gives

```text
delta Y=-Y^2 delta X mod t^L.                                (6)
```

With `delta X=sum_(i<m)delta x_i t^i`, extracting coefficient `n+r` from `(6)` proves `(1)` and
`(2)`.  Equation `(3)` is the determinant scaling law.  Since every `c_k=y_0^2 h_k`, factoring
`y_0^2` from each row gives the first equality in `(4)`.  Transposing the Toeplitz matrix gives the
standard Jacobi--Trudi matrix for the rectangular partition `(n^m)`, proving the second equality.

In the full observation map, the derivative of the displayed raw tail with respect to itself is an
identity block.  Its remaining square block is `(2)`, so the full differential loses rank exactly
on `(5)`.  The already-proved reciprocal Pascal determinant supplies a point off `(5)`.  `QED`

## Physical meaning

The Schur divisor is a static observation caustic.  On it, a nonzero low source perturbation becomes
invisible to the complementary horizon packet: the kernel of `(2)` is an observation zero mode.
Higher corank strata would describe simultaneous invisible modes, but no codimension or
irreducibility theorem for those strata is claimed here.  The rectangle controlling the generic
binomial state count also controls the exact collision equation of those states.

## What is and is not new

First-order inversion, Toeplitz sections, and the Jacobi--Trudi formula are classical.  Their exact
identification as the ramification equation of the critical raw/reciprocal HT horizon map is useful
new structure for this program, but it is a parent-theory bridge and does not clear the significance
gate by itself.  The live promotion target is the geometric monodromy of the resulting cover.

## RH impact

For the zeta free jet, `(5)` identifies exactly where finite reciprocal reconstruction loses local
rank.  It remains invariant under the target-translation blindness already proved for positive
jet horizons.  Without an Euler/source marking that orients or splits the Schur caustic, it does not
select the Xi zero fiber and has no RH consequence.

## Lean verification

`ProjectiveHorizonSchurCaustic.lean` proves `(6)` as a divisibility statement in the truncated
polynomial ring, proves every entry of `(2)`, and proves `(3)`.  The identification of its matrix
with the classical rectangular Jacobi--Trudi determinant is by the displayed definition and the
paper-level index transpose.  A targeted leaf build passes; no full build was run.

