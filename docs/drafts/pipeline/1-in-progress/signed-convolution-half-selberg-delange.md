# Signed convolution-half Selberg--Delange

- **ID:** SCH-SD-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** multiplicity-parity-ladder-route.md · convolution-half analytic frontier
- **Statement:** For the canonical coefficient half `a = squarefreeConvolutionHalf`, prove
  `sum_{n < N} a(n) ~ N / sqrt (pi * zeta(2) * log N)`, by factoring `a` into the positive
  coefficient half of `zeta` and an absolutely summable square-supported correction.

## Goal

Supply the signed Tauberian input needed to control convolution-half heat/Laplace schedules.  The
theorem is source-pure: coefficients come from the normalized Dirichlet-convolution half and no Xi
zero, RH statement, continuation of that half past `Re s = 1`, or divisor-parity premise occurs.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted `lake build` green, public axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Claim labels

- `[KNOWN]` Ordinary Wiener--Ikehara in `PNTPlus/Wiener.lean` requires nonnegative coefficients
  and a simple pole; it does not apply to `squarefreeConvolutionHalf`.
- `[KNOWN]` Fractional Ikehara--Delange for nonnegative coefficients gives
  `sum_{n≤x} b(n) ~ A x / (Gamma(alpha) log(x)^(1-alpha))` when the Dirichlet series has pole
  order `alpha`; Kato's `l/m` theorem includes `alpha = 1/2`.
- `[PROVED HERE]` Unrestricted signed Wiener--Ikehara is not the needed theorem: signed pole data
  alone allow cancellation.  Signed coefficients enter only after convolution with an absolutely
  summable correction.
- `[PROVED HERE]` Put `b = convolutionHalf zeta` and
  `c = mPart 2 (convolutionHalf moebius)`.  Then `b*b = zeta`, `c*c = mPart 2 moebius`, and
  `(b*c)*(b*c) = squarefreeIndicator`; normalized-half uniqueness forces `a = b*c`.
- `[PROVED HERE]` `b(n) ≥ 0`; locally its prime-power coefficients are
  `(-1)^k choose(-1/2,k) = centralBinom(k)/4^k`.
- `[PROVED HERE]` `c` is square-supported and absolutely summable at every real exponent
  `sigma > 1/2`, since dilation gives `L(c,s) = L(convolutionHalf moebius,2s)` and the undilated
  coefficients have norm at most one.
- `[PROVED HERE]` The positive zeta half has the exact fractional pole law
  `sqrt(t) B(1+t) -> 1`; this follows in Lean from `B(s)^2 = zeta(s)`, coefficient positivity,
  and the residue of zeta at one.
- `[PROVED HERE]` A reusable complex signed-convolution transfer theorem follows from the exact
  hyperbola swap and Tannery domination.  Its limit is `A * L(c,1)` with no sign condition on `c`.
- `[PROVED HERE]` The square-supported correction constant is the positive branch
  `L(c,1) = 1 / sqrt(Re zeta(2))`.
- `[OPEN CORE]` Prove fractional Wiener--Ikehara/Karamata inversion at order `1/2`: turn
  `sqrt(t) B(1+t) -> 1` and `b(n) >= 0` into the fixed-dilation summatory limit packaged as
  `ZetaBinomialHalfWienerIkehara`.
- `[OPEN CORE]` Discharge the concrete Tannery majorant from the zeta-half summatory bound and
  `LSeriesSummable_squareDilatedMoebiusBinomialHalf` at an exponent in `(1/2,1)`.

## Paper proof

Let `B(s)=sum b(n)n^{-s}` be the positive normalized convolution half of the constant-one
arithmetic function.  Absolute convergence for `Re s>1`, coefficient convolution, and uniqueness
give `B(s)^2=zeta(s)` and select the positive real branch on `s>1`.  Fractional
Ikehara--Delange with `alpha=1/2` therefore gives

`sum_{n≤x} b(n) ~ x / (sqrt pi * sqrt(log x))`.

Let `u=convolutionHalf moebius` and `c=mPart 2 u`.  Power dilation commutes with Dirichlet
convolution, hence `c*c=mPart 2 moebius`.  The standard `m=2` free-indicator identity is

`squarefreeIndicator = zeta * mPart 2 moebius`.

Thus `(b*c)^2=squarefreeIndicator`, and normalized square-root uniqueness yields `a=b*c`.
The correction is supported on squares and `sum |c(d)| d^{-sigma}<∞` for every `sigma>1/2`.
In particular its logarithmic moments at exponent one are finite.

For `B_0(x)=sum_{n≤x}b(n)` and `a=b*c`, exact hyperbola rearrangement gives

`sum_{n≤x}a(n) = sum_{d≤x} c(d) B_0(x/d)`.

Uniform convergence of the slowly varying factor on bounded `d`, Potter domination on the tail,
and absolute convergence of `sum |c(d)|/d^(1-epsilon)` permit dominated convergence after division
by `x/sqrt(log x)`.  The limit is

`(1/sqrt pi) * sum_d c(d)/d = (1/sqrt pi) / sqrt(zeta(2))`.

Therefore

`sum_{n≤x} squarefreeConvolutionHalf(n)
   ~ x / sqrt(pi * zeta(2) * log x)`.

This is Selberg--Delange for the concrete signed half.  It uses a positive fractional-Ikehara base
plus an `l1` signed correction; no false signed Wiener--Ikehara principle is invoked.

## Approach

1. Add reusable power-dilation/convolution and explicit half-coefficient algebra.
2. Add a precise nonnegative order-`1/2` Ikehara--Delange theorem, reusing corpus Fourier/Wiener
   infrastructure and proving the missing BV decay lemma.
3. Add a general slowly-varying convolution-transfer theorem.
4. Instantiate both at `squarefreeConvolutionHalf`; then derive shifted heat-profile consequences.

## Novelty search

- Internal corpus search found ordinary nonnegative Wiener--Ikehara, Karamata uniformity/Potter,
  power dilation, squarefree-half Euler summability, and Perron/zero-free contour tools, but no
  fractional Ikehara--Delange or Selberg--Delange theorem.
- R. Kato, *A remark on the Wiener--Ikehara Tauberian theorem* (2014), Theorem 3.1, supplies the
  nonnegative rational-order statement and constant.
- R. de la Bretèche and G. Tenenbaum, *Remarks on the Selberg--Delange method* (2020), confirms the
  standard `zeta(s)^rho G(s)` framework and signed/complex coefficient scope.

## Log

- 2026-09-04 — created in 1-in-progress after internal-corpus and primary-source audit.
- 2026-09-04 — formalized coefficient factorization, positive local formula, square-supported
  correction, fractional pole law, reusable signed Tannery transfer, exact correction constant,
  and conditional explicit Selberg--Delange assembly.  Targeted builds green; fractional
  Tauberian inversion and its concrete majorant remain open.
