# Theta-cusp likelihood strict cooling law

- **ID:** `theta-cusp-likelihood-strict-cooling-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / THETA LIKELIHOOD RESPONSE
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [LOCAL-RESEARCH] [NOVELTY UNVERIFIED]`
- **Parent:** `theta-cusp-reflected-likelihood-cumulant-obstruction.md`

## Statement

Let

```text
M_j(B)=integral t^j exp(-B t) dmu(t),
Z(B)=1+M_0(B),
m(B)=M_1(B)/Z(B),
v(B)=M_2(B)/Z(B)-m(B)^2,
```

where `mu` is the fixed positive theta-cusp higher-likelihood spectral measure.  For every
`B>0`,

```text
v(B)>0,                                                   (1)
m'(B)=-v(B)<0.                                            (2)
```

Thus `m` is strictly decreasing on `(0,infinity)`.  At the modular coordinate

```text
B_0=pi-3/2
```

the exact seam barycenter law gives

```text
2*pi*m(B_0)=ell_1,                                        (3)
ell_1=9/2-2*pi+6/(2*pi-3)>0.
```

Consequently, for every `x>=0`,

```text
0 < 2*pi*m(pi*exp(2x)-3/2) <= ell_1,                      (4)
```

with strict upper inequality when `x>0`.

## Corpus reuse inventory

- `thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef` and
  `det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos` provide the strict order-two moment
  determinant of the fixed tilted measure.
- `hasDerivAt_thetaCuspLikelihoodMean` gives the exact derivative `m'=-v`.
- `thetaCuspHigherLikelihoodSpectralMoment_seam_barycenter` gives the modular calibration.
- `thetaCuspFirstAtomBoundaryLogSlope_pos` gives positivity of `ell_1`.

No moment identity or seam calculation is rederived.

## Proof

For `B>0`, positivity of the measure and its support on the nonnegative half-line gives
`M_2(B)>=0`.  Strict order-two Hankel positivity gives

```text
M_0(B)M_2(B)-M_1(B)^2>0.
```

Since `Z(B)=1+M_0(B)>0`,

```text
Z(B)^2 v(B)
 =Z(B)M_2(B)-M_1(B)^2
 =M_2(B)+(M_0(B)M_2(B)-M_1(B)^2)>0.
```

This proves `(1)`.  The already derived quotient differentiation identity gives `(2)`.
The derivative is strictly negative at every point of the convex interval `(0,infinity)`, so the
mean-value theorem makes `m` strictly decreasing there.

The zeroth tilted moment is the higher likelihood response:

```text
M_0(B)=thetaCuspHigherLikelihoodSpectralResponse(B).
```

Therefore `Z(B)=1+M_0(B)`, and dividing the existing seam barycenter identity by the positive
partition gives `(3)`.

Finally `x>=0` implies

```text
B_0 <= pi*exp(2x)-3/2,
```

strictly for `x>0`.  Monotonicity of `m`, `(3)`, positivity of `M_1`, and `Z>0` give `(4)`.

## Hostile checks

1. A one-point higher-tail measure would make its own Hankel determinant zero, but the added
   first-atom mass at spectral coordinate zero could still create variance.  The proof does not
   rely on that weaker observation: the actual theta higher-tail measure has infinite support,
   hence strict Hankel determinant.
2. Nonnegative support alone gives only `v>=0`; strict cooling uses the corpus's infinite-support
   theorem.
3. The modular upper bound is unavailable for a generic Laplace family.  It uses the exact
   theta seam barycenter and therefore does not extrapolate to arbitrary positive measures.
4. The theorem does not determine the sign of the third cumulant or of the two-temperature
   reflected Riccati correction.  It removes the mean as a free obstruction and leaves variance
   and skewness as the remaining likelihood data.

## Novelty boundary

The exponential-family identity `m'=-v` is classical.  Potential novelty is only the exact
theta-specific combination of strict infinite-support cooling with the modular seam calibration
`2*pi*m(B_0)=ell_1`.  No external novelty claim is made.

## Formalization target

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodStrictCooling.lean`

- [x] zeroth moment equals spectral response;
- [x] every tilted moment is nonnegative;
- [x] total likelihood variance is strictly positive;
- [x] likelihood mean is strictly antitone on positive temperature;
- [x] exact modular-seam mean calibration;
- [x] nonnegative-source upper bound and strict positive-source form.
