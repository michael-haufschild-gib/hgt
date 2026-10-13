# Finite Weil covariance information deficit

Status: formalized and verified, 2026-10-12. Increment complete; corpus research continues.

## Claim

Let `N=r+1`, let `W` be the finite probability law of the explicit positive
quadratic-tilt weights, and let `U` be the uniform law on `Fin N`. Let

`M_r = (product_i product_{j>i} (j-i)^2/N) * (1/N)^N`.

For every finite `r,k` and all real tilt coefficients, the maximal power
covariance determinant is exactly

`M_r * exp(-N * KL(U || W))`.

Consequently it is at most `M_r`, equals `M_r` exactly when all actual atom
weights are `1/N`, and is at most `M_r * exp(-N * TV(U,W)^2)`.
The cost uses uniform-to-tilted KL, not the opposite direction. The benchmark
is sharp across probability laws on this support. Attainability by a quadratic
tilt at each particular `r,k` is not asserted.

## Local corpus evidence

- The preceding `WeilLogShiftPowerCovarianceProduct` root already separates the
  support product from the product of actual tilted weights.
- `PaperFourierLLogL.Finite.Entropy` defines finite-law KL, proves nonnegativity
  under support domination, and evaluates uniform entropy.
- `PaperFourierLLogL.Finite.Comparison` proves `tv_sq_le_kl` and the exact
  finite expectation formula for KL. Reuse these results.
- The cached lexical `product entropy` search covered all 59 declarations over
  three pages. Relevant finite-law, cold-Gibbs product, and uniform-KL sources
  were inspected; remaining names concern tensor products, rates, or unrelated
  thermodynamic observables. Focused source searches found no existing
  product/exponential/uniform-KL identity or finite Weil determinant benchmark.
- This is a local corpus audit; no external papers or novelty claims.

## Closed paper proof

For any positive finite probability law `P`, write `N=card(alpha)` and
`S=sum_x log(P(x))`. Unfold the existing finite-law KL definition and uniform
entropy: `KL(U||P)=-S/N-log(N)`. The existing logarithm-of-product theorem and
positivity give

`product_x P(x) = (1/N)^N * exp(-N * KL(U||P))`.

The finite-law zero criterion follows from the existing Pinsker bound. If KL
vanishes, TV squared is zero. The sum of nonnegative absolute coordinate
differences is therefore zero, so both laws coincide. The converse follows
directly from the KL definition.

Construct `W` from the already verified positive normalized tilt weights.
Substitute the generic product identity into the existing determinant product
formula. The support product and uniform factor are strictly positive: every
index pair `j>i` has positive squared gap, and `N>0`; empty products handle `r=0`.

KL nonnegativity gives the upper bound. Positivity of `M_r` and injectivity of
the real exponential reduce equality to zero KL, hence to uniform weights.
Finally, `TV(U,W)^2 <= KL(U||W)` and exponential monotonicity give the stated
quantitative bound. Positivity, normalization and support domination are all
discharged at the concrete finite Weil roots.

## Lean files

- `HTGeometry/FiniteLawProductEntropy.lean`
- `RHTower/WeilLogShiftPowerCovarianceEntropy.lean`
- `RHTower/WeilLogShiftPowerCovarianceMaximum.lean`

## Verification

- Three native leaf builds passed with empty logs and fresh `.olean` files.
- Nine declarations (seven theorems and two definitions) passed the final
  root-import axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Twenty-two API checks passed in the same final native scratch audit.
- All four direct project imports are fresh; both umbrellas are wired. Source
  whitespace and umbrella `git diff --check` passed.
- Formal lint snapshot: 367 existing size warnings and one unrelated missing
  umbrella import, `RHTower.WeilDecayClassRHCriterion`. No finding concerns the
  new files; unrelated source was not modified.
- Artifacts: `/tmp/hgt-covariance-information-final-audit.lean` and `.log`,
  `/tmp/hgt-covariance-information-audit.py`, API scratch and log,
  `/tmp/hgt-covariance-information-lint.log`, and three native leaf logs.

## Exact gain and premise audit

Maximal-degree covariance volume now has an exact finite-information meaning.
The uniform-to-tilted cost averages log weights over every support point; it is
not the tilted law's Shannon entropy deficit. Every actual root quantifies over
all finite `r,k` and all real `a,b,d`, with positivity, normalization and support
domination discharged from the concrete weights.

The equality test is conditional only in the ordinary sense of an iff: the
benchmark is reached exactly when the actual weights are uniform. No existence
of a quadratic parameter triple attaining uniformity was smuggled into the proof.

## Next conjectures

- Can the corpus's Gaussian-regime moment control, together with escape of the
  uniform law on the expanding index grid, force `TV(U,W)` toward one and a
  quantitative decay of determinant divided by benchmark?
- Can polynomial interpolation explicitly realize the uniform benchmark, or
  every positive target law, by a scalar polynomial tilt of the base law?

Neither next conjecture has been searched or formalized in this increment.
