# Positive Euler twins preserve real-axis nonvanishing

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; auxiliary clarification of ECS Q8.
- **Statement:** Beyond every finite zeta coefficient prefix, a positive bounded
  multiplicative Euler twin has a prescribed off-critical real part for a zero,
  while its entire reflected completion is nonzero at every real point.

The existing twin has local factor `1+A p⁻ˢ+p p⁻²ˢ`, with `A≥0`, and completed
multiplier `pˢ+A+p¹⁻ˢ`. At real `s=x`, this multiplier is strictly positive.
The completion therefore retains ξ's real-axis nonvanishing while adding
nonreal off-critical zeros. Nonnegative logarithmic coefficients still fail.

This tests a specific Q8 candidate: real-axis nonvanishing together with
functional equation, Euler product and positive ordinary coefficients does
not select zeta. It does not construct a model critical state or transfer
the ECS sign law to that model.

## Proof route

Use the existing positive passive twin; its coefficient at the edited prime
recovers `A≥0`. Real powers give positivity of the completed multiplier.
Combine with the corpus theorem `RHTower.XiGlobalKummer.xi_real_pos`.
Retain the off-line zero, finite prefix and negative logarithmic coefficient
from the same existing twin. No additional contribution counted.
