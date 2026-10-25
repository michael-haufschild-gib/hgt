# Uniform logarithmic cancellation in the undamped Vaughan convolution

- **ID:** uniform-undamped-vaughan-convolution-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** For every integer `q≥0`, the summatory truncated convolution `μ_U*μ_V*1` equals `n H_U H_V + O_q(n/(log n)^q)`, uniformly over all cutoffs `U,V≥0`.

## Finite estimate

Write `S_UV(n)=Σ_(d≤n)(μ_U*μ_V*1)(d)` and `h(n)=Σ_(k≤n)1/k`.
If `D≤n`, `|M(x)|≤Lx` and `|H_x|≤K` for every `x≥D`, then

`|S_UV(n)-n H_U H_V|≤D²+D+3Ln+2Ln h(n)²+Kn`.

If both cutoffs are below `D`, expand the exact double floor rectangle; rounding
costs at most `UV≤D²`. Otherwise swap the cutoffs so `V≥D` and use the exact identity

`S_UV(n)=M(min(U,n))+M(min(V,n))-M(n)+R_UV(n)`.

The three Mertens terms cost at most `D+3Ln`. Reversing the both-large convolution
sums expresses its remainder in Mertens blocks and bounds it by `2Ln h(n)²`.
The mean costs at most `Kn`, since the actual harmonic Möbius sums satisfy
`|H_U|≤1` at every cutoff, including zero.

## Uniform logarithmic rate

The existing arbitrary logarithmic Mertens and harmonic estimates provide
`L=B/(log D)^(q+2)` and `K=C/(log D)^(q+2)` once `D` exceeds a common threshold.
Take `D=floor(n^(1/4))`. Eventually `log D≥(log n)/8`, `h(n)≤2log n`,
and `D²+D≤2sqrt(n)`. Since `(log n)^q≤sqrt(n)` eventually, the claimed error is
bounded by

`[2+8^(q+2)(11B+C)] n/(log n)^q`.

All constants and thresholds are independent of the cutoffs. This gives no
fixed power saving and does not resolve Q-I.

## Lean status

`UniformCancellationInTheUndampedVaughanConvolution.lean` contains ten audited
targets, including the finite logarithmic specialization. Its scratch,
olean-producing, and final direct checks passed. `UniformLogarithmicCancellationInTheVaughanConvolution.lean`
contains the full uniform asymptotic theorem; its scratch, producing, and final
direct repository checks passed.
All eleven transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both modules are wired into the BVI umbrella. Final direct checks used
`lake --old env lean` on each leaf, without compiling the umbrella or raising limits.
The temporary audit files have been removed.
