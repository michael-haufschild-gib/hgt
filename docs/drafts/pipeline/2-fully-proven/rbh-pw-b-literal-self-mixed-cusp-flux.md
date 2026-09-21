# Literal self-copy mixed cusp-flux coefficient

- **ID:** RBH-PW-B-SMCF
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · RBH/PW-B shared polarized-current chain
- **Statement:** If an Xi copy `q` lies left of the critical line, then for either
  physical source branch the lower self-copy coefficient
  `fluxCoefficient q q branch 2` of the literal mixed cusp flux is nonzero.

## Goal

Discharge source-side possibility that the unique lower Weyl channel of the
actual mixed particular flux disappears before B2 transport.  In the common
RBH/PW-B/FZZ-P chain, any off-line copy supplies this nonzero channel; the
remaining load-bearing premise is transport through a complementary-rate,
metric-valued causal cap/contact boundary comparison.  The same-rate scalar
Peierls pairing is identically zero and cannot carry this coefficient.

## Paper proof

For `i = 2`, expand the literal coefficient:

`fluxCoefficient q q b 2 = (parameter q b / 2) · sourceCoefficient q 2 ·
readerCoefficient q · sourcePower q 2 · readerPower q ·
(readerPower q − sourcePower q 2) / denominator q b 2`.

Every factor is nonzero.

- `denominator q b 2 ≠ 0` is the source resonance exclusion.
- `parameter q b = (physicalRate q b + 1)(physicalRate q b + 2) ≠ 0`, since
  `Im q ≠ 0` makes either shifted physical rate nonzero.
- `sourceCoefficient q 2 = reflectedCompletedLambda (2q−1)^2 ≠ 0`: a zero
  contradicts the already proved left-half affine zero exclusion.
- `readerCoefficient q = reflectedCompletedLambda (q−1) ≠ 0` and
  `readerPower q = 1−q/2 ≠ 0` are literal reader facts.
- `sourcePower q 2 = 2−2q ≠ 0` and
  `readerPower q−sourcePower q 2 = −1+3q/2 ≠ 0`, because each hypothetical
  equality forces `Im q = 0`.

Thus their product quotient is nonzero.

## Gates

- [x] 0 → 1 in-progress: source-pure, exact B2 chain and factor audit fixed.
- [x] 1 → 2 fully-proven: complete paper proof from closed literal source identities.
- [ ] 2 → 3 formalized: source written as
  `fluxCoefficient_self_lower_ne_zero` in
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux.lean`; local
  dependency `.olean` is unavailable, so no Lean audit is claimed.
- [ ] 3 → 4 publication-ready: requires complementary-rate causal/contact
  transport; same-rate scalar transport is retired.

## Boundary

This does **not** prove the full residual boundary nonzero: the cap angular
flux and complete complementary-rate metric/current transport must still be
compared coefficientwise.  It removes only disappearance of the actual
particular lower channel.
