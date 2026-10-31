# Euler completion along growing source cutoffs

- **ID:** euler-completion-along-growing-source-cutoffs
- **Stage:** 3-formalized
- **Statement:** At source cutoff `M`, coordinate horizon
  `ceil((M+1)²/δ)` gives completion error at most `δ>0`, uniformly in
  `1≤X<M`. In particular the horizon `T_n=(n+1)(M_n+1)²` makes the
  full-source and completed finite-source energies differ by at most
  `1/(n+1)`, for arbitrary growing or irregular source schedules.

## Proof

The proved full-source comparison bounds the absolute error by
`(M+1)²/(T+1)`. Substitute either horizon; positivity of the denominators
gives the stated bounds. The latter upper bound tends to zero, so the two
energy sequences have the same finite limit whenever either has one.
This transfers an upper estimate once proved; it supplies no covariance
cancellation itself. The exact free-terminal Schur bound transfers with
the same allowance and retains its negative mass-discrepancy square.

## Verification

`CompletedArithmeticForms/EulerCompletionAlongGrowingSources.lean` passed
direct `lake --old env lean` verification. The explicit-horizon bound,
schedule bound, signed Schur bound and limit equivalence have transitive
axioms exactly `[propext, Classical.choice, Quot.sound]`; umbrella wired.
