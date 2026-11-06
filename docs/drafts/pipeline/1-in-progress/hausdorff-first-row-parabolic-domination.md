# First Hausdorff row by parabolic suppression

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ73
- **Statement:** Every endpoint-calibrated difference `D(0,r)` is nonnegative.

## Mathematical route

Write `D(0,r)=Σ_q x_q(R−x_q)^r`, with `x_q` the reciprocal-square Xi atom.
Existing proofs give finite initial signs and eventual positivity. A negative real part
requires a large accumulated complement phase. The critical-strip parabola forces such
an atom to have enough real size that `(R−x_q)^r` is exponentially suppressed. A band
of higher zeros should dominate this negative contribution.

## Missing estimate

A quantitative positive-band lower bound overlapping the known finite initial range.
The fixed-order large-shift theorem alone does not close this interval. No wall-status
change is justified without this estimate and its Lean proof.
