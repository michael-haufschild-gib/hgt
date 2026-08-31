# HB finite multipoint-jet positive-clock no-go

- **ID:** HB-FINITE-JET-POSITIVE-CLOCK
- **Stage:** 3-formalized
- **Type:** ROUTE KILL + POSITIVE SURVIVOR
- **Date:** 2026-08-31
- **Lean module:** `GaloisForLFunctions.RHTower.HBFiniteCrossFrequencyJetPositiveClockNoGo`

## Result

For every finite real frequency packet `S` and every finite depth `N`, there are distinct entire
zero-free responses `A+` and `A-` such that:

- `|A±(x)| = 1` for every real `x`;
- `A±(-conj z) = conj(A±(z))` for every complex `z`;
- `Im(A±'(x)/A±(x)) > 0` for every real `x`; and
- the actual analytic iterated derivatives of `A+` and `A-` agree through order `N` at every
  point of `S`.

Lean closes the maximal finite-data statement as
`not_hbFiniteCrossFrequencyJetAllPassUnique`. No symmetry or nonemptiness condition on `S` is
needed.

## RH proof chain killed

The theorem kills the first arrow in

`finite source-frequency jets determine all-pass phase`
`→ all-pass/minimum-phase identification`
`→ source-predeclared FE--Schwarz clock covariance`
`→ source-clock extinction`
`→ canonical left-branch covariance`
`→ shared Ward cancellation`
`→ RH`.

The prior value-only obstruction left finite frequency jets as a survivor. This theorem closes
that survivor at every finite packet and every finite derivative depth, including arbitrary
post-processing of the resulting finite jet vector. It does not kill HB itself.

## New mathematical core

Set

`H(X) = X * ∏_{a∈S} (X²-a²)^(N+1)`.

This is a nonconstant odd real polynomial, flat to order `N` at every `a∈S`. Let `K` be the odd
part of a real antiderivative of `1+(H')²`, and define

`A±(z) = exp(i(K(z) ± H(z)))`.

Oddness and real coefficients give exact FE--Schwarz symmetry; real phases give unit boundary
modulus; the exponential makes both responses entire and zero-free. Their boundary clocks are

`1+(H')²±H' = (H'±1/2)²+3/4 > 0`.

The exponent difference after shifting to any sampled point factors as
`z^(N+1) W(z)` with analytic `W`. Corpus theorem `iteratedDeriv_exp_congr_of_flat` therefore gives
equality of the actual response jets, not merely formal phase divisibility. Monicity of `H` and
infinitude of `ℝ` force `H'` to be nonzero somewhere; at such a point the two clocks differ, so the
responses are distinct.

## Strongest positive survivor

Any surviving HB producer must use information outside every finite local jet vector. Exact
survivors are:

1. a bounded Hardy/Schur or comparable global growth class strong enough to exclude these entire
   exponential witnesses;
2. values or jets on an infinite uniqueness set;
3. an external time-bilocal phase reference; or
4. a literal Einstein--Teukolsky source theorem deriving global minimum phase or winding.

This is now the source-side burden before FE--Schwarz clock covariance can reach the already
formalized Ward receivers.

## Novelty audit

Higher-order Caratheodory--Julia boundary interpolation
(https://arxiv.org/abs/math/0701106), boundary Caratheodory--Fejer interpolation in the Schur class
(https://arxiv.org/abs/1011.1399), and finite-Blaschke boundary interpolation
(https://arxiv.org/abs/1609.09843) already cover broad finite boundary-jet problems. The novelty
claim is restricted to this explicit HB route classification: arbitrary finite multipoint and
finite-depth blindness simultaneously with entire zero-free continuation, exact FE--Schwarz law,
unit boundary modulus, and everywhere-strict positive clock. Internal and external hostile search
located no prior theorem packaging these conditions or drawing this RH-chain no-go.

## Lean certificate

- `evalRealPolynomial_finiteJetOddFlatPolynomial_shift_factorization`
- `finiteJetPositiveClockAllPass_pair_iteratedDeriv_eq`
- `finiteJetPositiveClockAllPassPlus_neg_star`
- `finiteJetPositiveClockAllPassMinus_neg_star`
- `finiteJetPositiveClockAllPassPlusClock_pos`
- `finiteJetPositiveClockAllPassMinusClock_pos`
- `finiteJetPositiveClockAllPass_pair_ne`
- `exists_finiteJetSchwarzPositiveClockAllPass_pair`
- `not_hbFiniteCrossFrequencyJetAllPassUnique`

Validation: foreground scratch and tree checks with `lake env lean`, targeted module build, axiom
audit, umbrella wiring, and formal lint all PASS.
