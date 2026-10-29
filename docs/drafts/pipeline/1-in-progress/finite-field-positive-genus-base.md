# A finite-field elliptic function field and its zeta zeros

- **ID:** `finite-field-positive-genus-base`
- **Stage:** 1-in-progress
- **Type:** CLASSICAL BRIDGE
- **Target:** the nonsingular projective cubic `Y²Z = X³ − XZ²` over `F₃`, its actual
  function field, genus one, and its point-count zeta function with two numerator zeros.
- **Correction:** `HTGeometry/PositiveGenusBaseField.lean` has complex constants and does
  not meet this arithmetic target. Retain its true complex theorem without claiming otherwise.

## Internal and external audit

Corpus searches found `RHTower/HyperellipticRiemannHypothesis.lean`,
`HyperellipticDescent.lean`, and `ArithmeticEffectivityTheory/TheHyperellipticCalibration.lean`.
These prove the degree `m−1` Frobenius polynomial, Weil root bounds, and point counts of
`y²=f(x)` over every finite extension when `f` is squarefree of odd degree `m`.
`ArithmeticCastelnuovoSeveri/WittIntegralityIsNotPurity.lean` constructs the zeta series and
its unique logarithmic derivative. Mathlib supplies an actual Weierstrass coordinate ring,
fraction field, nonsingularity, and projective-point presentation; its `IsElliptic` condition
is nonvanishing discriminant. No geometric-genus API was found.

Classical reference: J. S. Milne, *Elliptic Curves*,
https://www.jmilne.org/math/Books/EC2.pdf. A nonsingular projective plane cubic has genus one;
its zeta function is `P(T)/((1−T)(1−qT))`, with `deg P=2` and reciprocal roots of norm `√q`.
Verdict: **BRIDGE**, no claim of new mathematics.

## Exact paper proof and formalization plan

Set `k=F₃` and `f=X³−X`. Its derivative is `−1`, so `f` is squarefree; its degree is three.
The short Weierstrass model with `a₄=−1`, other coefficients zero, has discriminant
`−a₄³=1` in characteristic three. The projective cubic is smooth and has the rational
point `[0:1:0]`. Use mathlib's actual coordinate ring and its fraction field.

Over every finite extension `E/k`, mathlib's point equivalence identifies projective points
with the disjoint union of infinity and pairs satisfying `y²=aeval x f`. The corpus
hyperelliptic theorem therefore gives `N_n=1+3^n−Σᵢωᵢ^n`, with exactly two reciprocal
roots and `|ωᵢ|=√3`. Consequently `P(T)=∏ᵢ(1−ωᵢT)` has degree two and
`Z(T)=P(T)/((1−T)(1−3T))`. The identity `T Z'(T)=Z(T)Σₙ≥₁N_nTⁿ` and constant term
one identify this with the actual point-count zeta series, not an unrelated spectral datum.
Its numerator zeros have modulus `1/√3`, hence neither pole cancels.

For a direct differential certificate of genus, use the charts `Z≠0` and `Y≠0`.
On the first, `dy` freely generates regular differentials since `∂(y²−x³+x)/∂x=1`.
On the second write `t=X/Y`, `u=Z/Y`, so `t³−tu²−u=0`. Set
`η=(1+tu)dt−t²du`. The relation gives `dt=(1−tu)η` and `du=−u²η`;
on the overlap `η=dy`. Thus the canonical sheaf is trivial. Regular global coefficients
are constants: for `a(x)+b(x)y`, the degree of its norm is
`max(2 deg a, 2 deg b+3)`, already proved in mathlib. The infinity valuation has
`v(x)=−2`, `v(y)=−3`, so regularity there forces `b=0` and `a` constant.
This makes the full regular differential space one-dimensional. Chart gluing and its
valuation identification still require formalization; they are not assumed as hypotheses.

## Status

- [x] Corrected the complex construction's scope claim.
- [x] Concrete finite field and curve selected; relevant corpus machinery located.
- [x] `ArithmeticEffectivityTheory/FiniteFieldEllipticBase.lean`: actual finite-field
  Weierstrass curve, discriminant one, fraction field, transcendence degree one; leaf check passed.
- [ ] Nonsingularity and positive-genus certificate.
- [x] `pointsEquiv` and `card_points`: actual projective points over every extension,
  identified with affine solutions plus infinity.
- [ ] Zeta-series identity and degree-two numerator; its zeros and noncancellation.
- [ ] Foreground leaf checks and transitive axiom audit; umbrella import.

No numerical experiments or finite point enumeration. All stated inputs must be discharged
symbolically. Do not replace geometric genus by a renamed root count or hide chart regularity
in an unproved interface.
