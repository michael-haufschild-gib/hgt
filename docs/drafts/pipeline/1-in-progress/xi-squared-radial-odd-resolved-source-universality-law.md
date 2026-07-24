# Xi squared-radial odd resolved-source universality law

Status: **Stage 2 — dependency-closed paper proof**

## Discovery

Whole-corpus posting closure joined two terminal uses of
`iteratedDeriv_xiLogDeriv_split`:

- `SquaredXiRadialJetSourceAlignment` supplies the reverse-Bessel-weighted alternating radial
  Xi jet polynomial; and
- `CompletedPrimeGammaResolvedMomentColligation` resolves every normalized odd Xi logarithmic
  jet into the exact prime + Gamma − polar source.

## Universal law

On every real base point `x > 1` and at every depth `k`,

`iteratedDeriv (2k+1) xiLogDeriv x
  = (2k+1)! · completedPrimeGammaResolvedMoment x k`.

Both appearances of `(-1)^k`—one in the analytic completed moment and one in the resolved
source theorem—cancel exactly. Consequently every odd term in the alternating squared-radial
Xi jet has one common negative sign:

`odd radial Xi sector = - odd resolved prime–Gamma–polar source sector`.

This is not the existing full rational–Gamma-minus-prime split: it extracts all odd radial
coefficients and resolves them into the completed three-leg moment carrier.

## Dependency-closed paper proof

1. Expand `completedOddLogDerivMoment x k` as
   `(-1)^k D^(2k+1)(xi'/xi)(x)/(2k+1)!`.
2. Apply `completedOddLogDerivMoment_ofReal_eq_resolved hx k`; its right side is
   `(-1)^k completedPrimeGammaResolvedMoment x k`.
3. Cancel the nonzero parity factor and factorial.
4. In each odd radial summand, substitute the derivative identity.
5. Since `(-1)^(2k+1) = -1`, normalize every summand to the same negative source sign.
6. Sum over all odd indices lying in the radial polynomial's triangular range.

No RH assumption, computation, or extra analytic hypothesis is used beyond `x > 1`.

## Formal targets

- `iteratedDeriv_xiLogDeriv_odd_ofReal_eq_factorial_mul_resolved`
- `squaredXiOddRadialJetPolynomial_eq_neg_resolvedSource`

## Novelty audit

Deferred until exact Lean proof.
