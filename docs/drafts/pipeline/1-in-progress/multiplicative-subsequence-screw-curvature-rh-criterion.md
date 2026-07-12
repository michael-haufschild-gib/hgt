# Multiplicative-subsequence screw curvature criterion

- **ID:** `multiplicative-subsequence-screw-curvature-rh-criterion`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / SOURCE-ARITHMETIC DETOUR
- **Scientific status:** `[CONJECTURE] [DIVISOR-SIDE PAPER PROOF OUTLINE] [LEAN OPEN] [NOT YET AN RH PROOF]`
- **Formal glue:**
  `formal/GaloisForLFunctions/RHTower/CCMMultiplicativeScrewCurvature.lean`

## Exact object

Fix an integer `m>=2` and put `L=log m`.  At aperture
`a=log(m^2 n)/2`, the rectangular detector is exactly

```text
2[Psi(log(m^2 n))+Psi(log n)-2Psi(log(mn))+2Psi(log m)],       (1)
```

where `Psi=xiScrewDivisor`.  Thus one fixed-width Weil detector
becomes a multiplicative midpoint curvature on the integer triple

```text
n, mn, m^2 n.                                                (2)
```

Identity `(1)` is proved in Lean by
`xiWeilPolarization_rectangular_log_mul_sq_eq_screwCurvature`.

## Divisor-side subsequence theorem

`[CONJECTURE, WITH COMPLETE PROOF OUTLINE]` For every fixed `M>=1`,
false RH forces the rectangular values at apertures

```text
a_n=log(Mn)/2
```

below every real level cofinally in `n`.  Consequently RH is equivalent
to eventual lower boundedness on this one multiplicative subsequence.

The existing Landau proof extends without a new analytic mechanism.  If

```text
S_L(n)=2 sum_q c_q n^(w_q),
```

then

```text
S_(L,M)(n)=S_L(Mn)=2 sum_q (c_q M^(w_q)) n^(w_q).             (3)
```

The new weights remain absolutely summable, respect Schwarz pairing, and
are nonzero.  Their Dirichlet series is

```text
2 sum_q c_q M^(w_q) zeta(s-w_q).                             (4)
```

At every shifted pole the extra factor `M^(w_q)` is nonzero, so the exact
pole order and Xi-cancellation contradiction are unchanged.  The bounded
rectangular remainder is also unchanged.  Therefore the current Landau
argument applies verbatim after parameterizing the fixed multiplier `M`.

This outline must be formalized; until then the subsequence equivalence is
not promoted to `[PROVED]`.

## Positive source target

After taking `M=m^2`, the missing RH theorem has the arithmetic form:

```text
for one fixed integer m>=2, the multiplicative midpoint curvature (1)
is eventually bounded below as n tends to infinity.                         (5)
```

This is strictly more structured than an arbitrary Weil lower bound.  It
has an exact source-side form.  Put

```text
R(h)=4sinh(h/2)
  -sum_(q<=exp(h)) Lambda(q)q^(-1/2).
```

The rectangular critical-Mellin tent law proves that, up to a fixed term and
an `n`-uniformly bounded Gamma term, `(1)` is twice

```text
integral_[log(mn),log(m^2n)] R(h)dh
 -integral_[log n,log(mn)] R(h)dh.                         (6)
```

Thus the missing positive statement is a finite lower floor for the imbalance
of two adjacent equal logarithmic blocks.  This invites a source construction
from a multiplicative conditional-negative-type kernel, a coupled renewal
projection, or an all-prime Euler--Gamma covariance.  A valid construction
must retain the signed prime--polar incidence in `R`; a Born-temperature phase
label or projective Fisher metric is insufficient, because the corpus proves
those data are phase-blind.

The fixed-multiple subsequence theorem is not load-bearing for this source
attack.  At every original rectangular sample `X=N`, the same law reads

```text
integral_[N/m,N] R(log x)d*x
 -integral_[N/m^2,N/m] R(log x)d*x.                        (7)
```

The endpoints need not be integers.  A lower floor for `(7)` over all large
integer `N` feeds the already formalized full-sample rectangular criterion
directly.  The subsequence formalization remains useful only if one wants the
three screw arguments themselves to be logarithms of integers.

## Attacks

1. `[REJECTED]` Finite-prime KMS covariance cannot identify `Psi`: finite
   prime-local sources are divisor-blind in the open strip.
2. `[REJECTED]` Coarse Chebyshev or PNT bounds do not prove `(5)`.  The
   continuous polar main term and the prime midpoint mass cancel at leading
   order; any fixed relative error leaves an unbounded `sqrt(n)` residual.
3. `[PROVED POSITIVE DUAL]` The cancellation no-go leaves the exact adjacent
   block imbalance `(6)`.  No global Weil form or pointwise sign of `R` is
   needed; one fixed-scale lower bound is sufficient.
4. `[LIVE]` Construct an all-prime, Gamma-completed covariance whose
   multiplicative parallelogram defect reads `(6)`, retaining the continuation
   seam before scalarization.
5. `[LIVE]` Alternatively prove a source identity expressing `(1)` as a
   squared norm plus an `n`-uniform boundary term.  The boundary term, not
   bulk positivity, is the positive datum demanded by the Wigner and screw
   no-go theorems.

## Gates

- [x] exact multiplicative midpoint identity formalized
- [x] finite-prime and coarse-PNT shortcuts attacked
- [x] exact adjacent critical-Mellin block readout proved on paper
- [x] full-sample adjacent-block route shown to bypass fixed-multiple Landau
- [ ] parameterize the Landau pole-jet chain by the fixed multiplier `M` (optional integer-triple refinement)
- [ ] prove the multiplicative-subsequence RH equivalence in Lean (optional integer-triple refinement)
- [ ] construct the all-prime Gamma-completed covariance or norm-square law
- [ ] prove its boundary term is uniform in `n`
- [ ] compose with the subsequence criterion and verify RH
