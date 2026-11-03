# The half-charge boundary in finite dilation energy

- **Stage:** 3-formalized
- **Statement:** The coherent prime-charge packet has a uniform boundary correction
  `−t²/2` after subtraction of logarithmic adjunction energy. At cutoff horizon
  `N = Q`, its dilation energy tends to `t²/2`.

Write `w_p = log p/p`, `B_Q = Σ_(p≤Q) w_p`, and `H_M = Σ_(n≤M) 1/n`.
The harmonic-centered packet has exact energy

`J_N = (t/B_Q)² Σ_(p≤Q) w_p H_(⌊N/p⌋)`.

The triangular identity

`2Σ_(p≤Q) w_p B_p = B_Q² + Σ_(p≤Q) w_p²`

gives

`J_N − (t²/B_Q)log N + t²/2 = (t/B_Q)² R_(Q,N)`,

where

`R_(Q,N) = Σ_(p≤Q) w_p(H_(⌊N/p⌋) − log N + B_p) − ½Σ_(p≤Q) w_p²`.

For `N ≥ Q`, the floor-harmonic error is at most `4p/N ≤ 4`.
The prime Mertens error `B_p − log p` is uniformly bounded, so each
parenthesis defining `R` is uniformly bounded. Since `0 ≤ w_p ≤ 1`,
`|R_(Q,N)| ≤ C B_Q`. Consequently the renormalized error is at most
`Ct²/B_Q`, uniformly over all such horizons. The prime Mertens theorem
gives `B_Q → ∞` and `log Q/B_Q → 1`, proving both limits.

Lean module:
`CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeBoundaryCorrection.lean`.
Declarations: `primePoleScale_triangular`,
`harmonicPrimeCharge_jumpEnergy_boundary`, `abs_primeChargeBoundaryError_le`,
`harmonicPrimeCharge_boundary_error_le`, `tendsto_harmonicPrimeCharge_boundary`,
`tendsto_harmonicPrimeCharge_cutoff_energy`.

Individual `lake --old env lean` check passed. Transitive axioms exactly
`propext`, `Classical.choice`, `Quot.sound`. Integrated into
`CriticalScaleArithmeticRigidity.lean`.

The theorem concerns dilation energy. Cancellation or survival in the
complete Weil form remains a separate obligation.
