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

### Direct chart certificate

Work inside the actual fraction field `K`. Let `A` be the existing affine coordinate ring,
and let `B=k[x/y,1/y]⊂K` be the chart `Y≠0`. These charts cover: a projective point with
`Y=Z=0` has `X³=0`, hence is not a projective point. Their coordinates satisfy
`t³−tu²−u=0`; inverting `u` identifies their overlap with the localization of `A` at `y`.

Write `d(a)=deg Norm(A/k[x])(a)`, using `−∞` for zero. The proved norm-degree formula
gives `d(ab)=d(a)+d(b)`, `d(a+b)≤max(d(a),d(b))`, and
`d(a)≤0` exactly when `a` is constant. The fractions `a/b` with `d(a)≤d(b)` form a
subalgebra `V⊂K`: clear denominators and apply these two inequalities. Since `d(x)=2`
and `d(y)=3`, both `t=x/y` and `u=1/y` belong to `V`, so `B⊂V`. If `a∈A` also
lies in `V`, clearing its denominator and cancelling its finite norm degree gives
`d(a)≤0`. Thus `A∩B=k`, without assuming an infinity valuation as an input.

Use the actual universal module `Ω[K/k]`. For each chart `C`, regular rational
differentials on that chart are the image of `Ω[C/k]→Ω[K/k]`; global regular
differentials are the intersection of these two images. Differentiating the equation
in characteristic three gives `dx=y dy`. The affine image is therefore `A dy`.
On the second chart `dt=(1−tu)dy`, `du=−u²dy`, and
`(1+tu)dt−t²du=dy`, so its image is `B dy`. These images include differentials of
all chart functions, by the Leibniz rule and algebra generation, not just the displayed
coordinate differentials. Their intersection is consequently `k dy`.

Finally `dy≠0`: the assignments `x↦(x,y)` and `y↦(y,1)` into the dual numbers
respect `y²−x³+x=0`, since the linear coefficient is `3y=0`. They give a derivation
of `A` with `δ(y)=1`, which extends by the quotient rule to `K`. The universal
property of Kähler differentials sends `dy` to one. Thus multiplication by `dy`
is a linear equivalence `k≃H⁰(Ω)`, proving geometric genus one directly.

## Status

- [x] Corrected the complex construction's scope claim.
- [x] Concrete finite field and curve selected; relevant corpus machinery located.
- [x] `ArithmeticEffectivityTheory/FiniteFieldEllipticBase.lean`: actual finite-field
  Weierstrass curve, discriminant one, fraction field, transcendence degree one; leaf check passed.
- [ ] Nonsingularity and positive-genus certificate.
- [x] `FiniteFieldEllipticCharts.lean`: actual coordinates and cubic relation; norm-degree
  product/addition laws; infinity regularity subalgebra; intersection of the two chart rings
  is exactly the constants; homogeneous chart-cover theorem. Full scratch check passed.
- [ ] `FiniteFieldEllipticDifferentials.lean`: actual Kähler images on both charts,
  nonzero `dy`, equality of global forms with `k dy`, and dimension one.
- [x] `pointsEquiv` and `card_points`: actual projective points over every extension,
  identified with affine solutions plus infinity.
- [x] `ArithmeticEffectivityTheory/FiniteFieldEllipticZeta.lean`: point-count ghost identity,
  uniqueness, rationality, numerator degree/root count two, zero modulus `1/√3`, and
  noncancellation at `1,1/3`. Complete scratch check passed; final leaf audit pending.
- [ ] Foreground leaf checks and transitive axiom audit; umbrella import.

No numerical experiments or finite point enumeration. All stated inputs must be discharged
symbolically. Do not replace geometric genus by a renamed root count or hide chart regularity
in an unproved interface.

## Working state

`FiniteFieldEllipticBase.lean` passed its source check and has an olean for the dependent leaves.
`FiniteFieldEllipticZeta.lean` is copied from the fully passing `/tmp/hgt_finite_zeta.lean`.
`FiniteFieldEllipticCharts.lean` is copied from the fully passing
`/tmp/hgt_finite_genus_norm.lean`; its olean is being built for the differential leaf.
The differential proof draft is `/tmp/hgt_finite_differentials.lean`.
No umbrella edit or final transitive axiom audit yet. All own `/tmp/hgt_finite_*` files
must be removed after the final audit. Preserve unrelated concurrent worktree edits.
