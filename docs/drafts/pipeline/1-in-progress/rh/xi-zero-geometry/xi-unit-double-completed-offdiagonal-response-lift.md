# Xi unit--double completed off-diagonal response lift

- **ID:** `xi-unit-double-completed-offdiagonal-response-lift`
- **Stage:** `1-in-progress`
- **Type:** conjecture / new completed response object / RH-facing source lift
- **Scientific status:** `[ORIENTATION FALSIFIED] [OLD UD8 RETIRED]`
  `[CORRECTED OBJECT PAPER-PROVED] [AC25 IDENTIFICATION OPEN]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Sources:** `XiAperturePoissonEulerLogDerivCompletion.lean`,
  `XiCompletedApertureReflectionKernel.lean`,
  `XiAperturePhysicalEndpointResponseRenormalization.lean`, and
  `XiPhysicalPrimeLogApertureHilbertMetric.lean`
- **Open consumer:** corrected response saturation `(AC28)`

## Discovery: do not diagonalize the completed current

> **2026-07-19 correction.** The kernel below has the coarse-minus-fine orientation.  The actual
> unit-to-double refinement is `-K_12`, and the physical endpoint requires the unique
> valuation-resolved correction proved on paper in
> `xi-physical-endpoint-valuation-correction-odd-shuttle.md`.  Thus the old identification and
> `(UD8)` with `K_12` are retired.  The Hermitian and balanced-coupling theorems remain valid for
> the object they state, but that object must be negated and corrected before comparison with
> the physical response.

Write

```text
S(s)=-xi'(s)/xi(s).
```

Complete valuation fusion at aperture `a>1`, including the prime clock and archimedean current,
is exactly `a S(a)`.  The unit--double prime shuttle was previously restricted to its diagonal
prime coefficient

```text
j_p=log(p)[2/(p^2-1)-1/(p-1)]=-log(p)/(p+1).            (UD1)
```

That diagonal restriction is support-blind and cannot be the RH response.  Before taking the
diagonal, the same completed scalar current has the canonical translation-invariant lift

```text
K_12(x,y)=2 S(2+i(x-y))-S(1+i(x-y)).                    (UD2)
```

Equivalently, in the existing transverse completed kernel `K_u`,

```text
K_12(x,y)=2 K_(3/2)(x,y)-K_(1/2)(x,y).                 (UD3)
```

Schwarz reality gives

```text
K_12(y,x)=conj(K_12(x,y)),                              (UD4)
```

so every finite packet is Hermitian.  On the diagonal,

```text
K_12(x,x)=2S(2)-S(1),                                  (UD5)
```

independently of `x`; all source interaction has been erased there.  Off diagonal, however, the
Euler-side formal expansion is

```text
sum_(p,e>=0) log(p)
 [2 p^(-2(e+1))-p^(-(e+1))]
 exp(-i(e+1)(x-y)log(p))
 + archimedean completion.                              (UD6)
```

At `x-y=0`, summing the fixed-prime valuation fibre in `(UD6)` recovers `(UD1)`.  At nonzero
`x-y`, the valuation phases survive and prevent coefficientwise cancellation.

## Prime-ratio sampling

The physical aperture carrier attaches the node `ell_p=log p` to prime `p`.  Therefore

```text
K_12(ell_p,ell_q)
 =2S(2+i log(p/q))-S(1+i log(p/q)).                    (UD7)
```

This is the first source-defined completed response object in the current chain which couples the
same unordered prime-ratio knots reconstructed losslessly by the true aperture width tomography.
It passes the existing obstruction tests:

1. it is not diagonal in prime coordinates;
2. it uses the infinite completed Xi flux and the archimedean factor;
3. it retains sign and phase before any Gram square;
4. it is invisible to finite differential-algebraic coordinate changes;
5. it is not defined from the desired smallness of the endpoint carrier.

## Forced finite signed joining

For a finite physical packet `P`, let

```text
b_P(p,q)=w_p w_q Re K_12(log p,log q),                 p != q.       (UD7a)
```

A real symmetric response coupling whose off-diagonal source is `(UD7a)` and whose one-prime
marginal is the unit--double current `(UD1)` has no remaining freedom.  Its diagonal is forced to
be

```text
C_P(p,p)=j_p-sum_(q in P, q!=p)b_P(p,q),
C_P(p,q)=b_P(p,q),                                    p!=q.         (UD7b)
```

Therefore

```text
C_P(p,q)=C_P(q,p),
sum_(q in P) C_P(p,q)=j_p.                              (UD7c)
```

Conversely, every real coupling on `P` with the off-diagonal values `(UD7a)` and marginals
`(j_p)` equals `(UD7b)` entrywise.  Thus `(UD7b)` is the unique finite signed joining compatible
with the completed seam source, the physical pair weights, and the source-forced linear
countercurrent.

This uniqueness is the positive replacement for the failed diagonal response.  It also exposes
the next possible no-go cleanly: if the forced diagonal in `(UD7b)` has no cofinal
Hilbert--Carleman renormalization, this completed seam packet cannot be the AC25 response.  If it
does, its finite quadratic form is the unique object to compare with `(PI8)` and `(HGS29)`.

## Cofinal size audit

Fix a physical packet with

```text
M exp(-A)<p<exp(c)M.
```

On the resulting compact ratio interval, `Re K_12(log p,log q)` is bounded by a constant
`B_(A,c)`: the completed flux is analytic on the compact real-part-one and real-part-two
segments, using the classical zero-free boundary at real part one.  Put

```text
W_1=sum_(p in P)w_p,       W_2=sum_(p in P)w_p^2.
```

The finite coupling satisfies the elementary bounds

```text
sum_(q!=p)|b_P(p,q)| <= B_(A,c) w_p W_1,
|C_P(p,p)| <= w_p(1+B_(A,c)W_1),

sum_p |C_P(p,p)|^2 <= (1+B_(A,c)W_1)^2 W_2,
sum_(p!=q)|C_P(p,q)|^2 <= B_(A,c)^2 W_2^2.              (UD7d)
```

Without any prime-distribution input, comparison with all integers gives

```text
W_1 <<_(A,c) log M,
W_2 <<_(A,c) log(M)^2/M.                                (UD7e)
```

Hence the balanced response packet has Hilbert--Schmidt square

```text
||C_P||_HS^2 <<_(A,c) log(M)^4/M.                       (UD7f)
```

This is the correct RH power scale for the **operator itself**, but it is not yet the AC25 scalar
estimate.  Contracting against the full aperture Gram can amplify a Hilbert--Schmidt packet by
the packet dimension.  A valid completion therefore needs both:

1. exact identification of `(UD7b)` with the joined source response; and
2. a stable signed contraction which retains the seam phases and avoids a dimension loss.

Calling `(UD7f)` alone an RH estimate would be false.

## Euler negative-type theorem

Before the archimedean boundary completion, the unit--double seam difference has the exact
ordinary Dirichlet spectral coefficient

```text
c_n=Lambda(n)(2/n^2-1/n)=Lambda(n)(2-n)/n^2.            (UD7g)
```

For every `n>=2`,

```text
c_n<=0,
c_n=0  iff  n=2 or n is not a positive prime power.     (UD7h)
```

Consequently every finite truncation is a negative-type translation kernel.  For arbitrary real
nodes `x_i` and weights `a_i`, put

```text
U_n=sum_i a_i cos(log(n)x_i),
V_n=sum_i a_i sin(log(n)x_i).
```

Then

```text
sum_n c_n sum_(i,j)a_i a_j cos(log(n)(x_i-x_j))
  =sum_n c_n(U_n^2+V_n^2)<=0.                            (UD7i)
```

Thus the finite Euler part of the completed off-diagonal response has no positive Jordan mass at
all.  Its only null spectral channel on prime-power support is the literal `n=2` mode.  Every
remaining sign obstruction is forced into the archimedean/boundary completion and the passage to
the real-part-one limit.

This is the strongest positive survivor of the earlier signed-Jordan no-go: do not estimate two
large Euler Jordan masses separately.  The unit--double response orients the complete finite Euler
source before completion, leaving one completed boundary kernel to control or cancel against the
joined physical response.

## Paper theorem and Lean target

Define `xiUnitDoubleCompletedOffDiagonalResponseKernel` by `(UD3)`.  Prove unconditionally:

1. the seam-flux formula `(UD2)`;
2. Hermitian symmetry `(UD4)`;
3. the constant diagonal `(UD5)` and reality of that diagonal;
4. the exact prime-ratio sampling law `(UD7)`;
5. the finite sampled matrices are Hermitian;
6. the weighted real packet `(UD7b)` is symmetric, has exact marginals `(UD7c)`, and is the unique
   finite coupling with those off-diagonal entries and marginals.

These statements use only the already-proved completed-flux reflection laws and elementary
complex arithmetic.  No RH assumption or response estimate enters.

## Hostile audit

- `(UD2)`--`(UD7)` construct the missing candidate object; they do not prove its sign or identify
  its quadratic pairing with the actual joined response.
- Taking `abs`, a norm square, or a Hilbert--Schmidt determinant of `K_12` before the full source
  joining would again destroy the signed response and is forbidden.
- The diagonal alone is the already-retired support-blind current.  Every viable theorem must use
  `p != q` samples or an operator action retaining `x-y`.
- The term at real part one is a completed analytic value, not an absolutely convergent prime
  series.  Formula `(UD6)` is a source interpretation, not permission to split the completed
  kernel into separately divergent sums at the boundary.

## Retired conjecture and corrected frontier

The old assertion

```text
R_M^sharp = Q_12(P_M) + O(polylog(M)/M)                 (UD8)
```

with `Q_12` built from `K_12` is **retired by coefficient orientation**.  At `p=2`, the correct
phase-preserving endpoint correction begins with coefficients `+1/2,-1/8`; the uncorrected
coarsening kernel fails this two-term test.

The refinement-oriented pairing and the fully corrected endpoint pairing are now both forced and
formalized in
`XiCompletedBalancedResponseDirichletDecomposition.lean`:

```text
Q_P^ref
 =sum_p [log(p)/(p+1)] ||kappa_p||^2
  -(1/2) sum_(p,q) C_P^ref(p,q)||kappa_p-kappa_q||^2,  (UD9-ref)

Q_P^end
 =sum_p [log(p)/p] ||kappa_p||^2
  -(1/2) sum_(p,q) C_P^end(p,q)||kappa_p-kappa_q||^2.  (UD9-end)
```

The first remaining gate is a coefficient-by-coefficient identification of `(UD9-end)` against
`(PI8)`/`(HGS29)`; `(UD9-ref)` is only its trace-class comparison current.  If the corrected
identity matches, the actual new analytic conjecture is the cofinal upper bound on its indefinite
signed Dirichlet term recorded as `(PVC12)`; another unspecified `Q_12` is no longer admissible.
