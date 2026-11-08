# Prime mass required by an almost-closed Euler approximation

- **ID:** AAL-EPM
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean verification pending)
- **Statement:** A finite Euler head approximating a function with a central zero on an almost-closed circle must spend logarithmic prime mass proportional to the inverse omitted angle.

## Target

Put `P_y(σ)=Σ_{p≤y} log(1+p^(−σ))`. Let `R>0`, `σ=c.re−R>0`, and let `f` be analytic near the closed disc, with `f(c)=0`. Choose a uniform circle bound `B≥|f|`. For `0<δ≤2π`, a relative approximation by `E_y(·+iτ)` with error `η∈(0,1)` on angles `[δ,2π]` implies

`(2π−δ)(−log η) ≤ δ (log(1+B)+P_y(σ))`.

At `δ≤1/log(2+|τ|)`, this gives

`2π(−log η) log(2+|τ|) ≤ −log η+log(1+B)+P_y(σ)`.

## Mathematical role

The existing small-value detector applied to `f·M_y` and the constant function `1` forces large mollifier norm on the omitted arc. Its Euler product bounds that norm by `exp P_y(σ)`. This yields a necessary growing-cut condition, not a producer of actual zeta returns. Fixed-cut phase recurrence cannot meet arbitrarily large heights at this gap scale through Euler-head approximation alone.

## Dependencies

`HTGeometry.zero_or_shortArc_small_value`; entire Euler mollifier and its finite-product formula. The zeta specialization obtains its circle bound by compactness, with no analytic return input assumed beyond the approximation whose cost is being bounded.

## Proof

**[PROVED HERE]** On the disc, `|M_y(z+iτ)|≤∏_{p≤y}(1+p^(−σ))=exp P_y(σ)`. Each factor follows from the triangle inequality and `Re z≥σ`. Since `P_y(σ)≥0`, its exponential is at least one.

Multiply the relative Euler-head error by `|M_y|`. Since `E_y M_y=1`, the long-arc condition becomes `|1−f M_y|≤η`. Apply the existing short-arc detector to the analytic function `f M_y`, which vanishes at the centre, and the constant function `1`. The latter has no zero, so some omitted-arc point satisfies `exp K−1≤|f M_y|≤B exp P_y(σ)`, where `K=(2π−δ)(−log η)/δ`.

Consequently `exp K≤1+B exp P_y(σ)≤(1+B)exp P_y(σ)`. Taking logs and multiplying by `δ>0` proves the first inequality. Write `L=−log η>0` and `A=L+log(1+B)+P_y(σ)>0`; then `2πL≤δA≤A/log(2+|τ|)`, proving the second.

For an actual zeta zero and a fixed disc contained in `0<Re s<1`, analyticity away from `1` and compactness supply `B≥0`. Thus a constant depending only on the fixed disc and accuracy bounds `2πL log(2+|τ|)−P_y(σ)` for every such Euler-head approximation. No zero density or return existence assertion enters the proof.
