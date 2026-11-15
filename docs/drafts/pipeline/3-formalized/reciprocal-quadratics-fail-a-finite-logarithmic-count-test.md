# Four even prime-power counts detect every reciprocal quadratic

- **Stage:** 3-formalized
- **Obstacle:** O11
- **Connection:** reciprocal scattering factors, Newton power sums and Euler logarithmic coefficients.
- **Count:** strengthening of the positive-passive-twin candidate; not a separate contribution.

## Statement

For a prime `p`, real `A`, and roots `α+β=−A`, `αβ=p`, at least one Euler logarithmic coefficient of `ζ(s)(1+A p⁻ˢ+p p⁻²ˢ)` at `p²,p⁴,p⁶,p⁸` is negative. This includes factors whose added zeros lie on the critical line. Nonnegative logarithmic counts therefore exclude the whole reciprocal quadratic class, independently of ringdown rates.

## Proof

Put `q=p²≥4` and `x=α²+β²=A²−2p`, which is real. Newton identities give the even power sums

`S₂=x`, `S₄=x²−2q`, `S₆=x³−3qx`, `S₈=(x²−2q)²−2q²`.

The corresponding logarithmic coefficient is `(1−Sₖ)/k`. Suppose `S₂,S₄≤1`; then `x≤1` and `x²≤2q+1`. If `x≤−1`,

`S₆=(−x)(3q−x²)≥q−1≥3>1`.

Otherwise `−1<x≤1`, hence `x²≤1`, and

`S₈≥(2q−1)²−2q²=1+2q(q−2)>1`.

Thus one of the four coefficients is negative. The argument uses only exact local coefficient identities; no zero estimate enters.

## Internal audit

`PositiveFiniteEulerBound.not_strictEulerBound` already excludes strict square-root growth through an asymptotic doubled-power identity. The present claim is a finite sign obstruction, requiring neither a growth bound nor an off-line zero. Corpus searches found the logarithmic coefficient formula and critical-circle classification, but no four-exponent sign test. No external literature checks; axiom checks skipped.

## Lean

`SelbergClass/PositiveFiniteEulerLogarithmicSigns.lean`, theorem `exists_negative_even_eulerLogCoeff`. Verified with `lake --old env lean GaloisForLFunctions/SelbergClass/PositiveFiniteEulerLogarithmicSigns.lean`; imported by the Selberg-class umbrella. No axiom checks.
