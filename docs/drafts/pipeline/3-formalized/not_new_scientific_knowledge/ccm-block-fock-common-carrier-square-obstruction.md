# CCM block--Fock common-carrier square obstruction

- **ID:** `ccm-block-fock-common-carrier-square-obstruction`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** KNOWN `2x2` PSD TEST / LOCAL SOURCE-CARRIER AUDIT
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parent:** `../../5-failed/ccm-first-clock-direct-positive-factorization-attack.md`
- **RH used:** no
- **Computation used:** no

## Frontier corrected

The ax+b block-subdivision route proved two exact appearances of

```text
F(r)=sum_(j>=0) r^(4j+1)=r/(1-r^4),       0<r<1.
```

For two block scales `m,n`, their normalized seed overlap is

```text
c(m,n)=sqrt(min(m,n)/max(m,n)),
```

and the claimed Gamma sewing is `F(c(m,n))`.  Independently, the radial vector attached to one
integer atom `q` has squared norm `F(q^(-1/2))`; deleting its first grade leaves the critical
defect `q^(-1/2)`.

Those two scalar identities do not define one common Hilbert carrier.  The theorem below proves
that no positive-kernel completion can combine them even on the two source atoms `q,q^2`.

## Theorem

### `CCM-BLOCK-FOCK-COMMON-CARRIER-SQUARE-OBSTRUCTION`

For every integer `q>=2`, put

```text
D(q)=F(q^(-1/2)),
G(m,n)=F(c(m,n)).
```

Then

```text
G(q,q^2)=D(q),                         (1)
D(q^2)<D(q),                           (2)
```

and therefore the symmetric two-node matrix

```text
M_q = [[D(q),   G(q,q^2)],
       [G(q,q^2), D(q^2)]]

    = [[D(q), D(q)],
       [D(q), D(q^2)]]
```

is not positive semidefinite.  More sharply, for `v=(1,-1)`,

```text
v^T M_q v = D(q^2)-D(q)<0.              (3)
```

Equivalently, there do not exist two vectors `x_q,x_(q^2)` in any real or complex Hilbert space
such that

```text
||x_q||^2=D(q),
||x_(q^2)||^2=D(q^2),
<x_q,x_(q^2)>=G(q,q^2).                 (4)
```

This is dimension-free and excludes real, complex, finite-dimensional, infinite-dimensional,
separable, nonseparable, ordinary Fock, and completed direct-sum realizations.

## Proof

For `q>=2`, both `q` and `q^2` are positive and `q<q^2`.  Hence

```text
c(q,q^2)
 =sqrt(q/q^2)
 =q^(-1/2).                             (5)
```

Applying `F` proves `(1)`.

The series for `F` has strictly positive coefficients, so it is strictly increasing on `(0,1)`.
Equivalently, from its rational form,

```text
F'(r)=(1+3r^4)/(1-r^4)^2>0.             (6)
```

Since `q>1`,

```text
0<q^(-1)<q^(-1/2)<1.                    (7)
```

But `(q^2)^(-1/2)=q^(-1)`, so `(6)--(7)` give `(2)`.  Equation `(3)` is now direct matrix
multiplication.  A Gram matrix must be positive semidefinite, so `(3)` excludes `(4)`.

No limit, prime estimate, zero sum, RH premise, or numerical check occurs.

## Strongest positive survivor: forced square-chain capacity

The obstruction exposes an exact replacement law.  Suppose a positive kernel `K` retains the
literal Gamma off-diagonal

```text
K(q,q^2)=G(q,q^2)=D(q)
```

and is normalized by `K(q,q)=D(q)`.  Positivity on the vector `(1,-1)` forces

```text
K(q^2,q^2)>=D(q).                       (8)
```

Thus a genuine common positive carrier cannot use the decaying radial diagonal `D(q^2)`.
Gamma sewing forces at least the previous-square capacity at the next square:

```text
common Gamma off-diagonal + positive Gram
  ==> diagonal capacity does not decay along q -> q^2.  (9)
```

This is the exact carrier datum missing from the first-clock AES proposal.  A surviving
construction must add a source-derived diagonal counterterm satisfying `(8)` before taking a
Schur complement, or retain an indefinite/Krein relation and prove that its negative index is
cancelled by the polar boundary.  Reusing the finite radial odd-Fock energy as diagonal is
formally impossible.

The sharp repair law is stronger.  Add a second-diagonal counterterm `delta`:

```text
M_q(delta) = [[D(q), D(q)],
              [D(q), D(q^2)+delta]].
```

Then, exactly,

```text
M_q(delta) is positive semidefinite
  iff
delta >= D(q)-D(q^2).                  (10)
```

Thus the obstruction is not only qualitative.  It determines the unique minimal square-scale
capacity debt, and `(2)` proves this debt is strictly positive at every integer scale `q>=2`.

## Canonical source fracture and saturation

The capacity debt is not an unspecified polar correction.  Squaring preserves the von Mangoldt
mark:

```text
Lambda(q^2)=Lambda(q).
```

Write `w(q)=Lambda(q)q^(-1/2)` and `T(r)=F(r)-r`.  Then the marked capacity debt has the exact
source decomposition

```text
Lambda(q)[D(q)-D(q^2)]
 = [w(q)-w(q^2)]
   + Lambda(q)[T(q^(-1/2))-T(q^(-1))].                 (11)
```

Both summands on the right are nonnegative for `q>=2`.  On an actual von Mangoldt atom, dividing
by `Lambda(q)` shows that the canonical source innovations supply exactly, not merely at least,
the threshold in `(10)`.  The repaired matrix is

```text
[[D(q),D(q)],
 [D(q),D(q)]],
```

so its determinant vanishes.  Hence the source-counterterm problem is closed, but the minimal
repair has no two-dimensional Schur innovation.

## Consequence for the RH route

The existing Lean theorem
`ccmFirstClockPrimeHalfWaveDominance_iff_rh` remains the right endpoint.  This theorem does not
prove its dominance law.  It removes a false predecessor:

```text
radial prime defect
  + cross-block Gamma odd-Fock kernel
  -> one positive Hilbert Schur carrier
```

cannot exist.  Moreover, canonical square source reaches only rank one. Any next live
predecessor must therefore contain strict capacity surplus:

```text
construct a source-complete carrier with positive determinant
whose compression is proved to equal the first-clock half-wave.
```

Companion cubic calculation supplies strict rank only on each local `q,q^3` radial block.
It does not supply a source-complete carrier: cubing stays inside one prime-power tower, misses
exponent-one prime atoms, and transports neither hard first-clock cutoff nor sine sign. Thus it
cannot serve as first clause of this predecessor. Its former triadic-assembly route is retired.

## Collision and novelty audit

Internal searches found the two scalar identities and the separate radial codiagonal saturation
no-go, but no theorem testing their joint `2x2` Gram compatibility.  The parent card incorrectly
described them as one common Hilbert carrier.

External searches checked:

- Brownlowe--an Huef--Laca--Raeburn, *Boundary quotients of the Toeplitz algebra of the affine
  semigroup over the natural numbers*, arXiv:1009.3678, for the ax+b/transfer-operator parent;
- Laca--Sehnem, *Toeplitz algebras of semigroups*, arXiv:2101.06822, for right-LCM and
  semigroup-Toeplitz parent structure;
- Connes--van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*,
  arXiv:2511.23257;
- Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form*, arXiv:2607.02828;
- exact-formula searches for `r/(1-r^4)`, the `1 mod 4` Fock ladder, and the logarithmic block
  overlap.

No separate priority claim is warranted. Obstruction is direct `2x2` Cauchy--Schwarz/PSD test
after substituting two already-formalized scalar normalizations. Exact collision is useful route
audit, not new scientific law.

## Gates

- [x] exact incompatible interfaces identified
- [x] two-node paper proof
- [x] no-RH/no-computation audit
- [x] classified as known-parent specialization
- [x] formalize `(1)--(3)` and exact counterterm threshold `(10)` in Lean
- [x] wire formal module into both RH frontier umbrellas
- [x] derive source-forced diagonal counterterm satisfying `(8)`
- [x] prove canonical square repair saturates at determinant zero
- [ ] first-clock dominance and RH
