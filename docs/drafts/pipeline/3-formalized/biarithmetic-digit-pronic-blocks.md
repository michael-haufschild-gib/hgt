# Two-sided pronic bounds on every complete digit block

- **ID:** biarithmetic-digit-pronic-blocks
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Digital energy and payment](../2-fully-proven/biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** For arbitrary real digit weights, the pronic energy on `5^M<=n<5^(M+1)` is at least `x_M^2/5^(M+1)` and at most `(64/5)5^(-M)(sum_(i<=M)|x_i|)^2`.

## Exact block proof

Let `W_x(n)` be the ordinary base-five readout with coefficient `x_i` on digit `i`.
The exact annular second moment is at least `5^(M+1)x_M^2`, independently of
all other signs. Every denominator `n(n+1)` in that block is at most
`5^(2M+2)`, so division gives the lower bound.

Each digit is at most four, hence `|W_x(n)|<=4 sum_(i<=M)|x_i|`.
The exact reciprocal telescope gives

`sum_(5^M<=n<5^(M+1)) 1/[n(n+1)] = 4/(5*5^M)`.

Multiplying this mass by the squared pointwise bound gives the upper constant
`64/5`. Both estimates are finite and retain the ordinary integer observation
measure. Their global sum is handled separately by geometric convolution.

## Verification

Lean: `BiarithmeticGeometry/DigitPronicBlocks.lean`.
Main declarations: `fiveBlock_pronic_mass`, `fiveDigitPronicBlock_lower`,
and `fiveDigitPronicBlock_upper`.

- [x] Dependency-closed exact paper estimates.
- [x] Direct repository source check and umbrella import.
- [x] Three transitive axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
