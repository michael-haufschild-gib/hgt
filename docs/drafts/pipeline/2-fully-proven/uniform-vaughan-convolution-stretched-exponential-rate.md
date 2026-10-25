# Uniform stretched-exponential cancellation in the Vaughan convolution

- **ID:** uniform-vaughan-convolution-stretched-exponential-rate
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** A common stretched-exponential bound controls the summatory truncated Vaughan convolution, uniformly in both cutoffs; consequently one threshold controls all logarithmic orders with factorial growth.

## Source audit

`RHTower/EulerDeletionStretchedEnergy.lean`, theorem `harmonic_rate`, proves
`|H_N|≤C exp(-(log N)^(1/3)/216)` eventually. Its proof uses the actual Mertens
estimate `deningerMertensM_rate`, whose saving is the square of this function.
These are unconditional bounds for the actual Möbius sequence. The source also
proves a factorial logarithmic envelope for the complete primitive energy; the
statement here concerns the uniform two-cutoff Vaughan convolution instead.
The corpus search for uniform truncated Vaughan convolution with stretched-exponential
summatory cancellation found the new finite and logarithmic bounds, but no existing
theorem with this rate. No external novelty claim is made.

The checked finite convolution estimate is

`|S_UV(n)-n H_U H_V|≤D²+D+(3B+2B h(n)²+C)n s(D)`

whenever `1≤D≤n` is beyond the common source threshold, with
`s(x)=exp(-(log x)^(1/3)/216)`. Indeed, `s` decreases on `[1,∞)` and is at most
one, so the Mertens saving `s(x)²` is bounded by `s(D)` for every `x≥D`.
The harmonic bound has the same envelope. The constants are independent of
`U,V,D,n`.

## Paper proof [PROVED HERE]

Put `D=floor(n^(1/4))`. The already verified cutoff inequalities give, eventually,
`D²+D≤2sqrt(n)`, `log D≥(log n)/8`, and `h(n)²≤4(log n)²`.
Write `u=(log n)^(1/3)` and `c=(1/8)^(1/3)/432>0`. Then

`s(D)≤exp(-2cu)`.

Let `t=cu`. For `log n≥1`, the inequalities `c≤1/432` and `u≤log n` give
`t≤(log n)/2`, hence `sqrt(n)≤n exp(-t)`.
Since `t^6≤6! exp(t)` and `(log n)²=c^(-6)t^6`,

`(log n)² exp(-2t)≤c^(-6)6! exp(-t)`.

The finite bound therefore gives, simultaneously for every `U,V`,

`|S_UV(n)-n H_U H_V|≤K n exp(-c(log n)^(1/3))`,

where `K=2+3B+C+8B c^(-6)6!`. This is a common constant and threshold.

For every integer `q≥0`, the exponential-series inequality
`t^(3q)≤(3q)! exp(t)` then yields, at that same threshold,

`|S_UV(n)-n H_U H_V| (log n)^q≤K n c^(-3q)(3q)!`.

Thus the arbitrary logarithmic estimates admit explicit factorial growth in their
order, with no order-dependent threshold. This still gives no fixed power saving:
the proved envelope has exponent proportional to `(log n)^(1/3)`, not `log n`.

## Lean status

Dependency-closed paper proof. Lean draft pending. The finite convolution and
arbitrary logarithmic rate have passed scratch, producing, and final direct checks;
their audits are tracked on
`../3-formalized/uniform-undamped-vaughan-convolution-cancellation.md`.
The source stretched-exponential theorem has been read, but its transitive axiom
audit must be included when this consequence is formalized. No full Q-I answer
or positive fixed-strip width is asserted.
