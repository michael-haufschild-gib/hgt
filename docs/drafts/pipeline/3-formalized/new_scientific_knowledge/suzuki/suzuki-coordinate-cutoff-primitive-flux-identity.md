# Suzuki's first-order cutoff defect is an exact primitive flux

- **ID:** `suzuki-coordinate-cutoff-primitive-flux-identity`
- **Stage:** 3-formalized
- **Type:** EXACT DIFFERENTIATED CUTOFF IDENTITY / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiCoordinateCutoffPrimitiveFlux`
- **Inputs:** `suzuki-coordinate-cutoff-covariance-classification.md`,
  `suzuki-gamma-wall-block-hardy-and-derivative-scattering.md`

## 1. Result

The coordinate-cutoff obstruction does not force abandonment of the differentiated normal
equation. It forces the cutoff defect to be kept in its correct **primitive** source class.

`[LOCAL-RESEARCH]` The predecessor Gamma-wall card already proves its identity `(51)` for a single
scalar cutoff \(\chi\), where prime transport commutes with \(\chi\). The theorem here is the
noncommuting valuation-coordinate extension required by event-adapted cutoffs.

Let \(X\) be a Hilbert space. Let \(R\) be the translation-invariant Gamma remainder on
\(L^2(\mathbb R;X)\), let \(B\in\mathcal B(X)\) act only in orbit coordinates, and put

```text
C=R-B.                                                   (1)
```

Both \(R\) and \(B\) commute with \(\partial_L\). Let \(M=M(L)\) be any strongly differentiable
coordinate multiplier and let \(F\) be smooth first. Then

```text
(2L I+C) partial_L(MF)
 -M(2L I+C)partial_L F

=partial_L([C,M]F)
 +M'(2L I+C)F.                                          (2)
```

If \(Z\) is any zero-order operator, then for

```text
N=(2L I+C)partial_L+Z
```

one has

```text
N(MF)-M N(F)

=partial_L([C,M]F)
 +M'(2L I+C)F
 +[Z,M]F.                                               (3)
```

For the paired Suzuki normal system,

```text
Z=I-KJ+Q_exp,                                            (4)
```

where \(KJ\) is the logistic orientation coupling and \(Q_{\rm exp}\) contains exponentially
small diagonal terms. Thus every coordinatewise boundary-event cutoff defect splits exactly into

```text
primitive source:
  G_cut=[R-B,M]F;

zero-order event source:
  H_cut=M'(2L I+R-B)F+[Z,M]F.                           (5)
```

No \(F'\) remains in either source datum. The apparent derivative loss in
\([M,B]F'\) is real if treated alone, but cancels against the product-rule part of the full cutoff
equation.

This is the positive survivor required by the cutoff-covariance no-go.

## 2. Proof

Since \(C\partial_L=\partial_L C\),

```text
partial_L([C,M]F)

=partial_L(CMF-MCF)

=CM'F+CMF'-M'CF-MCF'.                                   (6)
```

Also,

```text
M'(2L I+C)F=2L M'F+M'CF.                                (7)
```

Adding `(6)` and `(7)` cancels the two \(M'CF\) terms and gives

```text
CM'F+CMF'-MCF'+2L M'F.                                  (8)
```

On the other hand,

```text
(2L I+C)(MF)'-M(2L I+C)F'

=(2L I+C)(M'F+MF')-2L MF'-MCF'

=2L M'F+CM'F+CMF'-MCF',                                (9)
```

which is `(8)`. This proves `(2)`. Adding

```text
ZMF-MZF=[Z,M]F
```

proves `(3)`. `QED`

The identity extends to graph-domain profiles in distributions: approximate in the joint graph
norm of \(C\) and \(\partial_L\), use boundedness of \(M,M'\), and pass through `(2)`. Equivalently,
take `(6)` as the distributional product rule. No spatial derivative of the original weak Suzuki
mode is assumed.

## 3. Why the primitive source is the correct Gamma datum

The differentiated forced Gamma equation is naturally written

```text
(2L I+R-T)F'+F=G'+H.                                    (10)
```

Under Fourier transform,

```text
G' -> i z g(z).                                         (11)
```

The regular-singular division by \(2z\) cancels this \(z\), so the primitive contributes the
holomorphic forcing

```text
-(i/2)g(z),                                              (12)
```

not the singular term \(-h(0)/(2z)\) produced by a zero-order source with nonzero moment. This is
exactly the source class in `suzuki-forced-gamma-upper-strip-gluing.md`.

Consequently an estimate of \(G_{\rm cut}\), rather than \(G_{\rm cut}'\), is sufficient for strip
gluing. The high-frequency family used to disprove

```text
||[M,B]F'||_2 <=C||F||_2
```

does not attack `(10)` because the relevant datum is the zero-order primitive \([R-B,M]F\).

## 4. Finite-recurrence event bounds

Let \(M\) be diagonal in valuation labels:

```text
(MF)_nu=chi_nu F_nu,                                    (13)
```

where \(\chi_\nu'\) is supported on one unit block about event time \(\tau_\nu\). Let

```text
w(nu)=exp(-kappa|nu|_1).                                (14)
```

### Prime primitive

For one weighted shift

```text
(S_s F)_nu=alpha_(s,nu)F_(nu+s),
```

the exact commutator is

```text
([S_s,M]F)_nu
 =alpha_(s,nu)[chi_(nu+s)-chi_nu]F_(nu+s).              (15)
```

Completed modes are bounded, so every coordinate of the physical difference profile is bounded
by \(2w(\nu)\|u\|_\infty\). The shift ratios are fixed exponentials in \(|s|_1\). Therefore
\([B,M]F\) has on every event block a bound

```text
C_(a,kappa)||u||_infinity w(nu).                        (16)
```

If event times obey

```text
tau_nu<=C_a(1+|nu|_1),                                  (17)
```

then for every \(\sigma<1\)

```text
sum_nu exp(2sigma tau_nu)
 ||([B,M]F)_nu||_(L2(block tau_nu))^2<infinity          (18)
```

as soon as \(\kappa>\sigma C_a\), with a larger fixed \(\kappa\) absorbing finite prime steps.

### Gamma primitive

The proved Gamma cutoff-commutator theorem gives exponentially decaying off-block tails:

```text
||[R,chi_nu]F_nu||_(block j)
 <=C exp(-|j-tau_nu|)
   ||F_nu||_(local Gamma graph blocks).                 (19)
```

The literal undifferentiated paired fixed-window equation solves the local Gamma graph term as

```text
R F
=physical source
 -(2L+q)F
 +integral_0^L F
 +C_logistic JF.                                        (20)
```

On a unit event block, boundedness of the completed physical source and of \(F\), together with
the \(L^1\) mass of the logistic kernel, bounds `(20)` by a fixed polynomial in \(1+\tau_\nu\).
Combining `(17)`, `(19)`, and exponential valuation weight gives

```text
exp(sigma L)[R,M]F in L2(L;ell2_nu)                     (21)
```

for every prescribed \(\sigma<1\) after increasing \(\kappa\).

### Zero-order remainder

The factor \(M'\) localizes to the same unit event blocks. Formula `(20)` gives

```text
M'(2L I+R-B)F in exp(-sigma L)L2(L;ell2_nu).             (22)
```

The logistic commutator \([KJ,M]F\) has the same exponentially decaying block matrix as `(19)`,
because its kernel decays like \(e^{-|L-L'|}\). The remaining diagonal exponential terms commute
with \(M\) or are smaller. Hence

```text
exp(sigma L)G_cut in L2,
exp(sigma L)H_cut in L2,        sigma<1.                 (23)
```

This proves that finite recurrence type controls the **correct** primitive-plus-zero-order source.

## 5. What is and is not closed

The previous false inference was

```text
finite recurrence
 -> [M,B]F' is a zero-order L2 source.                   [FALSE]
```

The exact replacement is

```text
finite recurrence
 -> [R-B,M]F is a weighted primitive source
    and M'(2L+R-B)F+[Z,M]F is a weighted zero-order
    source.                                              [PAPER-PROVED]       (24)
```

This restores differentiated finite-type assembly at the source-norm level. The two endpoint
cosets, exterior events, exact rooted signs, and physical primitive term are now assembled in
`../../../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-literal-paired-source-assembly.md`.
That theorem also identifies the total antisymmetric source moment with the continuous physical
seam jump. The nonnormal derivative issue is handled by the primitive-flux graph reduction.
Remaining obligations are arbitrary finite-order expansion and compact-middle coverage.

## 6. Hostile audit

1. **The earlier no-go remains true.** Raw \([M,B]F'\) has no zero-order estimate.
2. **No contradiction.** `(2)` retains it as a derivative of a zero-order primitive.
3. **No unproved derivative norm.** Bounds `(18)`--`(23)` use \(F\), \(RF\), and physical source
   blocks, never \(F'\).
4. **No recurrence overclaim.** Event times must still have finite linear type.
5. **No moment deletion.** Literal source assembly retains the physical primitive and proves
   that the total antisymmetric moment is the continuous physical seam jump.
6. **No nonnormal Hardy claim.** Primitive source control alone does not bound
   \(\exp(-ixB/2)\); the later graph reduction avoids requiring that bound.
7. **No RH claim.** Even finite-type trace-zero \(H^1_0\) would leave exceptional apertures and raw
   Evans positivity.

## 7. Novelty boundary

Product-rule commutators and derivative forcing are classical. The scalar-cutoff specialization is
already local research in Gamma-wall identity `(51)`. Candidate-new source knowledge is the exact
extension to noncommuting, event-adapted valuation-coordinate cutoffs:

```text
unavoidable noncovariant terminal cutoff
 -> first-order prime defect
 -> exact primitive flux
 -> finite recurrence controls primitive Gamma datum
 -> literal two-coset source assembly.                   (25)
```

Suzuki's 2026 source paper does not introduce valuation-orbit terminal cutoffs. The audited
logarithmic-Laplacian literature treats scalar bounded sources, not the \([B,M]\ne0\) extension
`(2)`--`(5)`. External priority for that source-specific extension remains unverified.

## 8. Lean target

`SuzukiCoordinateCutoffPrimitiveFlux.lean` proves the exact pointwise operator identities
`primitiveCutoffFlux_pointwise` and
`primitiveCutoffFlux_with_zeroOrder_pointwise`. The predecessor module formalizes the
weighted-shift commutator and transport-covariant adapted-cutoff obstruction.

The analytic block estimates `(18)`--`(23)` and their two-coset extension require actual Gamma
convolution and weighted Bochner spaces. They remain paper-proved; the new Lean module
`SuzukiLiteralPairedSourceAssembly.lean` formalizes rooted transport, literal cutoff support, and
the complete physical-plus-cutoff source algebra without replacing analytic estimates by
hypotheses.

## Gates

- [x] derive exact primitive cutoff identity
- [x] include arbitrary zero-order paired coupling
- [x] identify derivative forcing as regular at frequency zero
- [x] prove prime primitive event summability at finite recurrence type
- [x] prove Gamma primitive event summability from exact commutator decay
- [x] bound zero-order event remainder without \(F'\)
- [x] formalize exact primitive operator identity in Lean
- [x] assemble total two-coset physical source with exact signs
- [x] prove total antisymmetric moment equals physical seam jump
- [ ] prove finite-type trace-zero \(H^1_0\)
- [ ] pass recurrence-infinite apertures
- [ ] prove RH or a genuine whole-Connes no-go
