# Pure critical horizon fiber is a cyclic fermionic occupation scheme

- **ID:** `projective-horizon-pure-tail-fermionic-fiber`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXACT SPECIAL-FIBER IDENTIFICATION
- **Scientific status:** `[PROVED ON PAPER] [BRIDGE] [FORMAL CORE COMPLETE]`
- **Parents:** `projective-horizon-critical-binomial-multiplicity`
- **Lane:** source-pure hypertranscendental geometry; static spectral topology

## Theorem

Let `m,n>=1`, put `L=m+n`, and work over an algebraically closed field `K` of characteristic
zero.  Consider the critical raw/reciprocal observation whose only nonzero prescribed tail entries
are

```text
x_m=1,   y_n=1,
x_(m+1)=...=x_(L-1)=0,
y_(n+1)=...=y_(L-1)=0.                                  (1)
```

Write the unknown low pieces as `A` and `B`, with `deg A<m` and `deg B<n`.  Then the compatible
source jets are exactly the monic factor pairs

```text
X=A+t^m,  Y=B+t^n,  X Y = 1+t^L.                         (2)
```

Since `1+t^L` is separable, its `L` roots are distinct.  Consequently the fiber is canonically
identified with all `m`-element subsets of its root set:

```text
Fib_(m,n)(pure)  ~=  {S subset Roots(1+t^L) : |S|=m}.     (3)
```

In particular it has `choose(L,m)` reduced points.  Exchanging the horizons is the complement
involution `S |-> S^c`.

Let `T` be multiplication by `t` on `K[t]/(1+t^L)`.  It is semisimple with `L` distinct
eigenlines.  The set `(3)` is also canonically the set of `m`-dimensional `T`-invariant subspaces:

```text
Fib_(m,n)(pure)  ~=  {W in Gr(m,L) : T(W)=W}.             (4)
```

Thus the previously numerical equality with the Grassmannian Euler characteristic becomes an
actual Grassmannian fixed-point identification at the pure observation.

## Proof

Under `(1)` the two projective-tail polynomials are

```text
X=A+t^m,    Y=B+t^n.
```

Their product has degree at most `L`, is monic of degree `L`, and critical compatibility says that
all coefficients below `L` equal those of `1`.  Therefore

```text
(A+t^m)(B+t^n)=1+t^L,
```

which proves `(2)`.  Conversely `(2)` immediately implies the truncated reciprocal compatibility.

The derivative of `1+t^L` is `L t^(L-1)`.  In characteristic zero a common root would have to be
both zero and a root of `1+t^L`, which is impossible.  Hence the polynomial is separable.  Every
monic degree-`m` factor is the product of `t-rho` over a unique `m`-subset `S` of its roots, and the
complementary factor is forced.  This proves `(3)` and the binomial cardinality.

The Chinese-remainder decomposition

```text
K[t]/(1+t^L) ~= product_(rho in Roots(1+t^L)) K
```

diagonalizes multiplication by `t`; the coordinate axes are its pairwise distinct eigenlines.
An invariant subspace of a diagonalizable operator with simple spectrum is exactly a sum of a
subset of eigenlines.  Restricting to dimension `m` gives `(4)`.  `QED`

## Exterior-state interpretation

The standard basis of `wedge^m K^L` is indexed by the same `m`-subsets.  Over `C`, after choosing an
inner product on the one-particle eigenline space, these are the occupation states of `m`
indistinguishable fermions in `L` simple modes; horizon exchange is particle--hole complementation.
This is an exact exterior-algebra identification of the state labels, not a claim that a
hypertranscendental function evolves by a quantum Hamiltonian.  The cyclic operator comes from the
static polynomial constraint `(2)`.

## What is and is not new

Polynomial factorization, simple-spectrum invariant subspaces, Grassmannian torus fixed points,
and exterior occupation bases are classical.  The exact identification of the pure critical
raw/reciprocal horizon fiber with all four objects is useful structural knowledge, but it is a
parent-theory bridge rather than a dual-gate new result.  Its significance is that it supplies a
non-metaphorical spectral model against which the generic critical monodromy can be measured.

## RH impact

For a free zeta jet, `(3)` provides a canonical model fiber at a deliberately chosen observation,
not at zeta's actual source-marked data.  It does not orient a zeta fiber or select the Xi zero set.
An RH-useful refinement would need the Euler data to select, weight, or break the complement
symmetry of the occupation states; no such refinement is proved here.

## Gates

- [x] exact pure-tail factorization proved
- [x] separability and subset classification proved
- [x] invariant-Grassmannian identification proved
- [x] exterior occupation and complement dictionary stated without dynamical overclaim
- [x] Lean core complete and targeted verification passed

## Lean verification

`ProjectiveHorizonPureTailFiber.lean` proves the exact factorization equivalence, separability of
`1+X^L` in characteristic zero, and the cardinality of the occupation-label type.  The root-subset
and invariant-Grassmannian equivalences remain at paper level rather than importing a new finite
spectral-geometry library.  The targeted leaf build passes; no full build was run.
