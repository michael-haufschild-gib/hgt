# Positive Euler twins preserve real-axis nonvanishing

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); auxiliary clarification of ECS Q8, strengthening accepted contribution 1.
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

## Proof

The existing positive passive twin supplies a prime `p>N`, its parameter `A`,
bounded positive multiplicative coefficients, the prescribed off-line zero,
and failure of every nonnegative logarithmic representation. At the edited
prime the ordinary coefficient is `1+A`; its lower bound by one gives `A≥0`.
For every real `x`, both `p^x` and `p^(1-x)` are strictly positive. The completed
multiplier is consequently a positive real number. Multiplying it by the
strictly positive real value of ξ (`RHTower.XiGlobalKummer.xi_real_pos`) proves
positivity of the twin's completion on the entire real axis. The remaining
properties belong to this same twin.

## Lean and boundary

`ExclusionOfTheCriticalState/Models/ThePositiveEulerTwinsHaveNoRealZero.lean`
passed its final plain `lake --old env lean` check and is umbrella-wired.
Main theorem: `exists_positive_euler_twin_without_real_zeros`.

This rules out real-axis nonvanishing as a sufficient separator even after
positive bounded ordinary coefficients, reflection, Euler structure, passive
scattering and arbitrary finite coefficient agreement are retained. It does
not prove that nonnegative logarithmic coefficients exclude an actual critical
state. No additional contribution counted; Q8 remains open.
