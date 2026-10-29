# A finite-field elliptic function field and its zeta zeros

- **ID:** `finite-field-positive-genus-base`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CLASSICAL BRIDGE
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

## Exact paper proof `[PROVED HERE]`

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
respect `y²−x³+x=0`, since the linear coefficient is `3y−3x²y=0`. They give a derivation
of `A` with `δ(y)=1`, which extends by the quotient rule to `K`. The universal
property of Kähler differentials sends `dy` to one. Thus multiplication by `dy`
is a linear equivalence `k≃H⁰(Ω)`, proving geometric genus one directly.

## Status

- [x] Corrected the complex construction's scope claim.
- [x] Concrete finite field and curve selected; relevant corpus machinery located.
- [x] `ArithmeticEffectivityTheory/FiniteFieldEllipticBase.lean`: actual finite-field
  Weierstrass curve, discriminant one, fraction field, transcendence degree one; leaf check passed.
- [x] Nonsingularity and positive-genus certificate.
- [x] `FiniteFieldEllipticCharts.lean`: actual coordinates and cubic relation; norm-degree
  product/addition laws; infinity regularity subalgebra; intersection of the two chart rings
  is exactly the constants; homogeneous chart-cover theorem. Source compilation passed.
- [x] `FiniteFieldEllipticDifferentials.lean`: actual Kähler images on both charts,
  nonzero `dy`, equality of global forms with `k dy`, and dimension one.
  `chart_overlap` identifies both localizations on the overlap. Source compilation passed.
- [x] `pointsEquiv` and `card_points`: actual projective points over every extension,
  identified with affine solutions plus infinity.
- [x] `ArithmeticEffectivityTheory/FiniteFieldEllipticZeta.lean`: point-count ghost identity,
  uniqueness, rationality, numerator degree/root count two, zero modulus `1/√3`, and
  noncancellation at `1,1/3`. Source compilation and transitive axiom audit passed.
- [x] `FiniteFieldPositiveGenusBase.lean`: unconditional combined certificate,
  `numerator_degree_eq_twice_genus`, and `zeta_zero_count_eq_twice_genus`.
- [x] Foreground leaf checks and transitive axiom audit; umbrella import.

No numerical experiments or finite point enumeration. The geometric genus is independently
proved from all regular Kähler differentials; the root count then equals twice that genus.
No chart regularity or counting input is supplied through an unproved interface.

## Lean certificate and validation

Modules: `formal/GaloisForLFunctions/ArithmeticEffectivityTheory/FiniteFieldEllipticBase.lean`,
`FiniteFieldEllipticCharts.lean`, `FiniteFieldEllipticDifferentials.lean`,
`FiniteFieldEllipticZeta.lean`, and `FiniteFieldPositiveGenusBase.lean`.
Namespace: `GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase`.

`positiveGenusBaseField_spec` has no parameters, premises, or extra typeclass assumptions.
It certifies constants of cardinality three, an elliptic curve, its function field of
transcendence degree one, geometric genus one, and its actual point-count zeta series.
The numerator has degree and root count `2 * geometricGenus`; roots are counted with
multiplicity. Each root gives a zero of `zetaFunction` of modulus `1/√3` with nonzero
denominator.

All four dependency modules passed source compilation; their oleans were created only for
the dependent modules. The capstone passed the final foreground, non-output check from
`formal/`, with exit 0 and no diagnostics:

```sh
lake --old env lean GaloisForLFunctions/ArithmeticEffectivityTheory/FiniteFieldPositiveGenusBase.lean
```

The independent transitive audit copied the capstone source, synthesized the field,
constant algebra, finiteness, characteristic, and elliptic instances, and checked 28
declarations with `#print axioms`. Every declaration, including
`positiveGenusBaseField_spec`, reports only `[propext, Classical.choice, Quot.sound]`.
The audit exited 0. Its complete output is preserved in
[finite-field-positive-genus-base-audit.txt](finite-field-positive-genus-base-audit.txt).

The existing `ArithmeticEffectivityTheory.lean` umbrella imports the capstone. No full or
umbrella build, existing-olean rebuild, proof placeholder, new axiom, kernel bypass, or
increased Lean limit was used.

## Outcome

The requested arithmetic base is available: the function field of
`Y²Z = X³ − XZ²` over `F₃`, with independently proved genus one and its point-count
zeta function. Its numerator has exactly `2g=2` zeros counted with multiplicity.
This supplies the arithmetic zeros that a separate series may inherit as poles;
inheritance by a particular series requires its own identity with this zeta function.
