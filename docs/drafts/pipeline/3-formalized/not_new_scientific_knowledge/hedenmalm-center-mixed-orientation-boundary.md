# Hedenmalm center-mixed orientation boundary

- **ID:** `hedenmalm-center-mixed-orientation-boundary`
- **Stage:** 3-formalized
- **Type:** BRIDGE / EXACT SOURCE-ORIENTATION NORMALIZATION
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [SIGN OPEN]`

## Theorem

Let `Q_theta(a,b)` be the value of the split rank-four Hankel--Krein form on the actual theta/Xi
orbit.  For `a>0`,

```text
B_Xi(b+ia,b-ia)=Q_theta(a,b)/(2a).                       (1)
```

At every regular point of the critical aperture `0<a<1/2`, the Bezoutian reconstructed by the
pointed Hedenmalm moment germ satisfies the same identity:

```text
B_M(b+ia,b-ia)=B_Xi(b+ia,b-ia)=Q_theta(a,b)/(2a).        (2)
```

No positivity assumption enters either equality.  The Fourier transform of the canonical
center-mixed theta autocorrelation tangent is exactly `Q_theta(a,b)`.  Consequently,

```text
Q_theta(a,b)>=0 for every 0<a<1/2 and b in R
iff the center-mixed theta Fourier current is nonnegative there
iff RH.                                                   (3)
```

## Positive obligation

The pointed moment module is source-determining but orientation-neutral.  It reconstructs the
unique current in `(2)`; it does not place that current in the nonnegative Krein chamber.  A
successful Hedenmalm--Hilbert--Polya proof must therefore establish one source-specific global
statement:

```text
the actual theta orbit avoids the negative chamber throughout 0<a<1/2.
```

Equivalently, it must prove positive definiteness of the concrete pointwise-positive center-mixed
density.  Reconstruction, pointwise positivity, ambient operator coercivity, and finite local
autocorrelation frames stop before this order statement.

## Formal certificate

File:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCenterMixedOrientationBoundary.lean`.

Theorem surface:

```text
xiHedenmalmBezoutian_upper_conj_eq_krein_div
xiHedenmalmBezoutian_upper_conj_re_eq_krein_div
xiHedenmalmPointedMomentBezoutian_upper_conj_eq_krein_div
thetaXiHankelOrbitNonnegative_iff_riemannHypothesis
thetaCuspCenterMixedFourierNonnegative_iff_thetaXiHankelOrbit
thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis
```

The module builds without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.  The final two
biconditionals are exact boundary theorems and must not be cited as proofs of the sign.

## Significance

The normalization closes a formal gap between the pointed moment, Bezoutian, theta-source, Krein,
and Fourier descriptions.  The RH equivalence is a bridge to horizontal Xi-modulus monotonicity,
not new scientific knowledge.  Honest score: **48/100**.  Publication-level significance still
requires a source theorem proving the sign in `(3)`.

## Gates

- [x] pointed moment to actual Bezoutian normalization
- [x] actual Bezoutian to theta Krein current normalization
- [x] center-mixed Fourier current incidence
- [x] exact RH equivalence
- [ ] source-specific chamber avoidance
- [ ] RH
