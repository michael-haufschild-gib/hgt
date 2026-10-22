# Hedenmalm autocorrelation-path boundary

- **ID:** `hedenmalm-autocorrelation-path-boundary`
- **Stage:** 3-formalized
- **Type:** BRIDGE / POSITIVE SOURCE-ORIENTATION LAW
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [SIGN OPEN]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmAutocorrelationPath.lean`

## Unconditional theorem

Let `k` be the normalized theta-cusp source and, for `|a|<1`, put

```text
f_a(x)=exp(-a x)k(x).
```

Let `C_a` be the autocorrelation of `f_a`, and let `dot C_a` be its first variation in the
direction `-x f_a(x)`.  The actual Hedenmalm horizontal tangent is `dot C_a`.  For every real
displacement `x`, the exact center/difference change of variables gives

```text
dot C_a(x)
 = integral_0^infinity r sinh(a r)
     k(r/2+x/2)k(r/2-x/2) dr
 = M_(k,a)(x/2).                                         (1)
```

The proof is absolute, not formal differentiation under an unevaluated integral.  It unfolds both
cross-correlations, applies the affine substitution `r=2y-x`, uses evenness of `k`, and pairs the
two radial halves exactly.

Consequently the actual center-mixed density is integrable and continuous throughout the full
Fourier--Laplace aperture

```text
|a|<1,                                                    (2)
```

which strengthens the earlier direct domination range `0<=a<1/2`.

On the critical aperture `0<a<1/2`, the source is strictly positive, hence

```text
Re dot C_a(x)>0 for every real x.                         (3)
```

At the same time, the already formalized spectral-propagation obstruction gives

```text
dot C_a is not a finite sum of autocorrelations of
constant-coefficient polynomial differential filters of f_a.  (4)
```

Thus the actual tangent lies strictly inside the pointwise-positive cone while lying outside every
finite local differential autocorrelation-frame cone.

## Positive Hilbert--Polya obligation

Equation `(1)` separates two orders which must not be conflated:

```text
pointwise positivity of dot C_a              -- unconditional;
positive definiteness of dot C_a             -- orientation-bearing.
```

The second statement is Loewner monotonicity of the canonical autocorrelation path.  Through the
Fourier identity already proved for `dot C_a`, it is the source-coordinate form of horizontal Xi
modulus monotonicity.  A successful Hedenmalm construction must therefore produce a genuinely
nonlocal positive-definite factorization or an equivalent cofinal matrix inequality.  Pointwise
positivity, a finite differential Gram frame, or bulk coercivity cannot supply that order.

## Parent-theory and significance verdict

The mechanism behind `(1)` is classical correlation calculus and an affine change of variables.
The distinction between pointwise-positive and positive-definite functions is standard harmonic
analysis.  The exact theta-source instantiation is useful route compression, but it does not add a
new sign theorem and does not prove RH.

Honest score: **58/100**.  The theorem removes an ambiguity in the source architecture and enlarges
the rigorous analytic aperture, but it is a bridge rather than publication-level new science.

## Formal certificate

The axiom-clean theorem surface is:

```text
thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity
integrable_thetaCuspCenterMixedDensity_of_abs_lt_one
continuous_thetaCuspCenterMixedDensity_of_abs_lt_one
thetaCuspHorizontalAutocorrelationTangent_re_pos
thetaCuspHorizontalAutocorrelationTangent_strictlyPositive_not_finiteFrame
```

The exact module build passes.  No RH, Fourier-sign, positive-definiteness, zero-location, or
abstract source hypothesis occurs in these declarations.

## Gates

- [x] exact center/difference change of variables
- [x] actual theta autocorrelation-tangent identity
- [x] full-aperture integrability and continuity
- [x] strict pointwise positivity on the critical aperture
- [x] finite differential-frame exclusion
- [ ] positive definiteness of the tangent
- [ ] source-side Loewner monotonicity
- [ ] RH
