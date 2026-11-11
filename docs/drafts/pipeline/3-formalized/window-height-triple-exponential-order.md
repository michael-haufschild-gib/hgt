# The triple-exponential order of the verified window height

- **ID:** A79-A81-A93-window-height-order
- **Stage:** 3-formalized
- **Lean:** `VerifiedHeightRungs/TheGapScaleControlsTheVerifiedHeight.lean`
- **Status:** Direct Lean check passed; umbrella wired.
- **Theorem:** `tendsto_log_log_log_windowHeight_sub_rpow`.

## Exact limit

Let `m=gapMass`, `E=gapEnergy`, `c=18·48⁴`, and
`C=[32(400m)²·5760·c⁴/E]^(1/3)`. Then

`log log log(windowHeight(a)) − C a^(4/3) → log 138`.

## Proof

At interpolation spacing `σ=1/(ca)`, the gap scale is
`Y=max(ca,Ca^(4/3))=Ca^(4/3)` eventually.
Dilation of `g=gapTestC 1` gives
`gapTail(Y)=16[Y∫‖g‖+Y⁻¹∫‖g''‖]²=O(Y²)`.
Consequently the exact exponential branch

`gapHeight(σ)=128 exp(138 exp Y−2 exp(−Y)−4Y+20)`

dominates its tail branch. Hence `log(gapHeight σ)/exp Y→138`.

The auxiliary horizon satisfies `log(winT₁)=O(exp a)` and `winD₀≤winT₁⁴`.
Since `Y≥2a`, the gap-height branch determines `winN` eventually:
`N=⌈gapHeight(σ)/nodeStep(a)⌉`. Rounding has relative error tending to zero,
and `log(1/nodeStep)=O(log a)`, so `log N/exp Y→138`.

Let `B₀=(e·400²)(24·240 log 3)1000`. Eventually

`exp((log 2)N)≤windowHeight(a)≤exp((B₀+1000)N)`.

Indeed `winT₁≤N`, `winD₀≤N⁴`, `a≤N`, and `nodeStep≤1` control the
prefactors, while `winK=2(N+1)48^(2N)` supplies the exponential growth.
The reciprocal smoothing width is at most `exp(116N)` and at least `2^N`.
Taking two logarithms and dividing by `exp Y` squeezes the result to `138`.
One further logarithm gives the stated refined limit.
