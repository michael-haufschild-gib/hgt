# Logarithmic energy detects interval length

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A finite-energy source supported in an interval of width `0<h≤1` has logarithmic energy at least `log(1/h)‖f‖²`. The literal constant interval source has energy at most `h(log(1/h)+3)`.

## Proof

Translations beyond the support width have disjoint supports, so their
squared loss is `2‖f‖²`. Integrating these losses over `[h,1]`, together
with the mass term, proves the lower bound. Constant interval sources have
exact squared loss `2 min(t,h)`. Splitting the jump integral at `h` and `1`
proves integrability and the matching upper bound. Translation preserves
the complete form and places these tests at arbitrary endpoints.

## Lean

`CanonicalSystemOfTheWindowTower/TheLogarithmicFormDetectsIntervalLength.lean`:
`logarithmicFullForm_ge_log_inverse_width`,
`logarithmicIntervalSource_translation_loss`,
`hasLogarithmicEnergy_logarithmicIntervalSource`,
`logarithmicFullForm_intervalSource_upper`,
`logarithmicFullForm_intervalSource_upper_at`.

Plain Lean audit passes without warnings. All five printed declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. Wired into the umbrella.
