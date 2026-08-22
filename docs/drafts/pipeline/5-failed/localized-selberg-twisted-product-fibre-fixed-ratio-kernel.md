# Localized Selberg and twisted product fibres do not bound the fixed-ratio kernel

- **ID:** `localized-selberg-twisted-product-fibre-fixed-ratio-kernel`
- **Stage:** 5-failed / analytically retired; positive-salvage Lean closure pending
- **Type:** FALSIFIED RH PRODUCER / POSITIVE-SALVAGE CLASSIFICATION
- **Parent:** the Selberg half-density audit `(ER13)`--`(ER21)` in
  `../1-in-progress/critical-multiplicative-compensated-cancellation-rh.md`
- **Positive survivor:**
  `../2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/localized-half-density-mobius-curvature-semiprime-fibre-law.md`
- **Statement:** Neither the real Möbius boundary germ, its imaginary half-density continuation,
  nor regrouping the triangular fixed-ratio kernel by product `R=mn` supplies an estimate stronger
  than the known RH-equivalent covariance.  Exact all-grade cancellation removes the centring on
  a complete product fibre; restoring the active block forces an indefinite endpoint correction.
  Every ordinary semiprime fibre contains only the two orientations of one prime pair, so product
  regrouping has no internal cancellation.

## Proposed route

The route tried to combine three exact features.

1. For `sigma>0`, the coefficients

   ```text
   b_sigma(n)=product_(p|n)(1-p^(-sigma))
   ```

   are nonnegative and have boundary derivative `Lambda` at `sigma=0`.
2. The imaginary continuation produces a finite-tangent Gram representation of the von Mangoldt
   fixed-ratio covariance.
3. Grouping the triangular B-spline kernel by `R=mn` turns its ratio dependence into the twisted
   convolution `(Lambda_t*Lambda_(-t))(R)`, suggesting a localized Selberg symmetry inside each
   product fibre.

The hoped-for theorem was a source-side upper bound on the curvature that survived the
support-grade cancellation `(35m21)` and was strictly easier than `(35m20)`.

## Exact killing mechanism

### 1. Removing the second-grade leakage forces the already-known flat quotient

For

```text
b_sigma^(a)(n)=n^(a sigma)b_sigma(n),
```

the exact first two jets are

```text
(b^(a))'_0=Lambda,
(b^(a))''_0=Lambda*Lambda+(2a-1)Lambda log.              (N1)
```

The pure convolution-square jet occurs if and only if `a=1/2`.  This is the symmetric shifted
Euler quotient

```text
e_sigma(n)=n^(sigma/2)b_sigma(n),
sum_n e_sigma(n)n^(-s)=zeta(s-sigma/2)/zeta(s+sigma/2),
e_sigma*e_(-sigma)=epsilon.                              (N2)
```

Thus the normalization that repairs `(35m21)` is uniquely forced into an exact convolution
coboundary already classified by the corpus.  It contributes no new uncompressed curvature.

### 2. Localization exposes an endpoint correction, not positivity

Let

```text
T_c(x)=(c-|x|)_+,          alpha=c^2/A,
K^int(x)=T_c(x)-alpha.
```

For `R>1`, `log R>=c`, and real `tau`, exact convolution inversion gives

```text
sum_(mn=R; m,n>1)
 e_(i tau)(m)e_(-i tau)(n)K^int(log(m/n))

 =sum_(mn=R)e_(i tau)(m)e_(-i tau)(n)T_c(log(m/n))
  +alpha[e_(i tau)(R)+e_(-i tau)(R)].                   (N3)
```

The full product fibre cancels the constant centring identically.  Deleting the two trivial
factorizations `(R,1)` and `(1,R)`, as the active fixed-ratio block does, restores it through the
last term of `(N3)`.  That term changes sign already on `R=pq`:

```text
e_(i tau)(pq)+e_(-i tau)(pq)
 =-8sin(tau log p/2)sin(tau log q/2).                    (N4)
```

Its half-curvature at zero is exactly `-(Lambda*Lambda)(R)`.  It cannot be discarded,
absolutized, or replaced by a positive measure without deleting the rank-one aperture centring.

### 3. A semiprime fibre has no room to average

For

```text
C_t(R)=(Lambda_t*Lambda_(-t))(R),
Lambda_t(n)=Lambda(n)n^(it),
```

unique factorization gives

```text
C_t(p^a q^b)
 =2log(p)log(q)cos(t(a log p-b log q))       (p!=q),     (N5)
```

and `C_t(R)=0` when `R` has at least three distinct prime divisors.  Hence an ordinary semiprime
`R=pq` carries exactly one unordered prime pair, two ordered orientations, and one real cosine
mode.  The orientations reinforce under every even ratio kernel.

On the unclipped interior, its complete centered coefficient is

```text
2log(p)log(q)
 [T_c(a log p-b log q)-c^2/A],                           (N6)
```

with sharp sign boundary

```text
|a log p-b log q|=c(1-c/A).                             (N7)
```

For the exact clipped kernel the product layer is still just

```text
2log(p)log(q)/(pq) K_(A,c)(u_p,u_q).                    (N8)
```

Therefore grouping ordinary prime pairs by `R` is a bijective relabeling.  Any cancellation must
occur between different products, which is the original aggregate covariance problem.

### 4. The remaining estimate is circular

The finite imaginary tangent is a nonnegative Gram family.  The desired theorem is a tiny upper
bound on its second curvature.  Positivity gives the opposite one-sided information.  A uniform
bound that can be divided by `tau^2` is `(35m12)`; on one fixed-ratio block it is `(35m20)`, which
the corpus already proves paper-level equivalent to RH.

Using a nonzero `tau` does not bypass this.  Higher support grades return for every nonzero
`tau`, and the only unconditional non-split Taylor bound is `(35m22)`, forcing an
ultra-microscopic tangent window.  Estimating the endpoint correction in `(N3)` separately loses
the cancellation one was trying to prove.

Finally, Selberg positivity has the wrong orientation.  It controls causal product indices
`log m+log n=log R` and the square of a Laplace transform.  The aperture Gram needs reflected
difference lags `log m-log n` and an absolute square.  The explicit obstruction `(ER19)` survives
this localization; `(N5)` only diagonalizes the same mismatch product fibre by product fibre.

## No-go closure

- **Exact killing theorem/mechanism:** `(N1)` forces the unique half-density into the flat inverse
  family `(N2)`; the active aperture then differs from the flat complete fibre by the indefinite
  endpoint term `(N3)`.  Equations `(N5)`--`(N8)` show that ordinary semiprime fibres have no
  internal averaging.  Any bound after summing different `R` is the RH-equivalent covariance
  `(35m20)`.
- **Strongest positive survivor:** the unique half-density normalization `(N1)`--`(N2)`, exact
  finite-parameter endpoint-deletion law `(N3)`, complete twisted product-support classification
  `(N5)`, and sharp interior sign boundary `(N7)`.  Full proofs are in the Stage-2 card linked
  above.
- **New insight:** the obstruction is sharper than “Selberg has the wrong sign.”  The all-grade
  inverse law itself deletes the fixed-ratio centring on a complete product fibre.  The centring
  lives entirely in the two deleted trivial factorizations, while every unresolved ordinary-prime
  fibre is spectrally one-dimensional.  A viable theorem must therefore correlate **different
  semiprime products** through a source-selected Type-II aperture Stokes law; no intra-product
  Selberg completion can work.
- **Status:** paper proof dependency-closed and parent-theory/anti-circularity audited.  The
  two-prime orientation and symmetrization core is already formalized and axiom-audited in
  `formal/GaloisForLFunctions/HTGeometry/PrimeCollisionConvolution.lean`.  The localized
  second-jet/endpoint-deletion package remains selected for Lean but unimplemented because the
  shared one-process Lean slot was occupied.  Under the project no-go discipline, the analytic
  route is retired but its closure is **not formally complete** until that exact package compiles
  and passes the axiom audit.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The shifted half-density, inverse cocycle, unique factorization,
and triangular kernel all belong to known parent theory or the existing corpus.  The localized
endpoint law and fibre classification are genuine new internal deductions and materially sharpen
the route boundary, but they do not yield a new estimate, invariant, or external number-theoretic
result.

No web search and no numerical computation were used in deriving this verdict.

## Gates

- [x] real and imaginary Möbius tangents derived coefficientwise
- [x] `(35m21)` absorbed by the uniquely forced half-density normalization
- [x] exact finite-parameter endpoint-deletion law proved
- [x] complete product-fibre support and semiprime spectral law proved
- [x] sharp triangular sign chambers proved
- [x] Selberg-orientation and RH-circularity attacks passed
- [x] strongest positive structural core located in existing unconditional Lean
- [ ] localized second-jet and endpoint-deletion survivor formalized and axiom-audited
- [ ] route closure eligible to be marked fully formal
