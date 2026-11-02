# Interior jumps of odd prime-free cycles

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Π11h: interior-jump count on the prime-free window; Σ7: odd sector.
- **Statement:** For every odd real compact smooth test supported in `[-a,a]`,
  `a>0`, with mass `M=∫f²` and autocorrelation `A`,
  `∫_0^(2a) (M−A(t))/t dt ≥ (log 2+7/5)M`.

## Mechanism

After scaling to `[-1,1]`, fold onto the positive half-interval and use
the positive gauge `h(x)=x(1−4x²/5)`. The logarithmic jump generator sends
`x` to `x` and `x³` to `(11/6)x³−x/2`. Exterior killing contributes
`log 2−½log(1−x²)`. The required potential bound reduces to

`−½log(1−v) ≥ (26/75)v/(1−4v/5)`, `0≤v<1`.

The folded remainder is a nonnegative integral of squared gauge differences.
This counts interior jumps directly; existing small-window Weil positivity
is not an input.

## Remaining proof obligations

Prove the scalar logarithmic inequality, justify the folded integral identity
at the diagonal and origin, and transfer the bound to the actual Gamma jump
weight. Combine its exterior tail and the exact odd pole term to obtain a
prime-free count bound. The whole-window sign is not yet proved.
