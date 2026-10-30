# Growing-conductor reciprocal-shell transfer

- **ID:** growing-conductor-reciprocal-shell-transfer
- **Stage:** 2-fully-proven
- **Statement:** For each `A≥0` and each natural `k`, one base horizon gives
  `|actual affine shell correction − signed mean|≤Cφ c/(log Y)^k`
  simultaneously for `1≤q≤(log Y)^A`, `c≥1`, `X≥2cY`, and all shifts and
  affine multipliers. The positive constant `Cφ` depends only on the profile.
- **Scope:** The growing-modulus shell transfer in A15; no square-root modulus range.

## Proof

The conductor-uniform residue Mertens theorem bounds each finite-part remainder
by `2(log Y)^(-j) Σ|F|` at every endpoint at least `Y`, for all
`q≤(log Y)^A`. The exact weighted Abel identity transfers this bound with
weight cost `|W(1)|+∫|W′|`.

For the reciprocal autocorrelation weight `W_a(u)=G(a/u)`, the existing
variation theorem gives `|W_a(1)|≤M=∫φ²` and `∫|W_a′|≤2L`, independently
of `a`. It vanishes below `1/(2c)` for active shells. Thus `X≥2cY`
keeps every nonzero derivative contribution inside the uniform Mertens range.

The affine Ramanujan residue pattern has `Σ|F|≤qϕ(q)`.
There are at most `2c` active shells; multiplying by the original `2/M`
normalization gives

`error ≤ [8(M+2L)/M] qϕ(q)c/(log Y)^j`.

Take `b=ceil(A)` and `j=k+2b`. Since `log Y>1`,
`qϕ(q)≤q²≤(log Y)^(2b)`. Cancel this factor to obtain the stated bound.
All constants and the single horizon are uniform over the allowed conductors.
The tilted spline discharges every profile condition.

## Inputs

`eventually_conductor_uniform_residuePrimeRealError_log_bound`,
`weightedResiduePrimeReading_sub_mean_eq`,
`exists_reciprocalShellWeight_variation_bounds`, and the exact shell decomposition.

## Verification

Lean formalization in progress.
