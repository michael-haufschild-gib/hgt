# Sub-Weyl source bounds lower the heat floor

- **Stage:** 3-formalized
- **Type:** THEOREM

## Results

Unconditionally, for `t ≥ 8`,

\[
|\zeta(1/2+it)|\le C t^{33/200}\log t,
\qquad
|\zeta(5/6+it)|\le 10^7 t^{2/53}\log t
\]

for some absolute `C > 0`. There exists `t₀ ≥ 80` such that, for every
`|t| ≥ t₀`, `λ ≥ (133/200)/log|t|` and natural `m`,

\[
0<\operatorname{xiSliceHeatTransfer}(\lambda,0,t,2m).
\]

Thus both source exponent `33/200 < 1/6` and order-uniform heat coefficient
`133/200 < 2/3` improve their Weyl thresholds.

## Proof

Put `T=t/(2π)`. The actual stationary phase dual of the differenced
logarithmic phase has fifth derivative comparable to `N⁹/(Th)⁴`.
The fifth derivative test and stationary phase weights bound its correlation
by a constant times

\[
(Th)^{11/30}N^{-1/5}+(Th)^{5/8}N^{-13/16}
 +Th/N^2+(N^3/(Th))^{1/2}+(Th)^{2/5}N^{-2/5}.
\]

Weyl differencing with `H=ceil(N^(36/41)T^(-11/41))` gives the required
critical-line prefix bound on `T^(97/200) ≤ N ≤ T^(101/200)`.
Below this interval use trivial bounds through `t^(33/100)`, the direct
fourth derivative test through `t^(2/5)`, then the fourth derivative dual
bound. Every resulting weighted prefix is `O(t^(33/200))`.

Apply the exact two-series Gaussian approximate functional equation at scale
`sqrt(t)`. For both actual weights, finite Abel summation costs at most a
constant times `min(1,sqrt(t)/N)`. The dual-weight variation follows from
positive and negative Mellin contours: differentiating the Mellin power
cancels the kernel denominator. Above `T^(101/200)`, this saving makes the
classical `O(t^(1/6))` prefix bound `O(t^(33/200))`.

Use `R=Nat.log 2 ceil(t²)+1` and truncate at `2^R-1 ≥ t²`. There are at most
`4 log t` blocks, each within the proved Weyl range. Both actual series have
majorant `C sqrt(t)n^(-3/2)`, giving tails `O(t^(-1/2))`; the pole residue is
at most one. This proves the critical-line estimate. The existing Weyl
bound covers `8 ≤ t < 1024π`.

For `Re s=5/6`, take trivial head `ceil(t^(12/53))+3`. The fifth derivative
estimate applies through `t^(15/53)`, the fourth derivative estimate through
`sqrt(t)`, and the critical-line Weyl estimate with extra decreasing weight
`n^(-1/3)` thereafter. Every block is at most `10^6 t^(2/53)`.
Euler–Maclaurin truncation above `t²`, with `O(log t)` blocks, proves the
stated `5/6` estimate.

Phragmén–Lindelöf interpolation through
`(1/2,33/200)`, `(11/18,1/9)`, `(5/7,1/14)`, `(5/6,2/53)` and absolute
convergence gives four xi-slice profiles. Their limiting `(intercept,slope)`
pairs are `(31/200,3/100)`, `(1/13,3/13)`, `(1/53,23/53)`, `(0,29/53)`.
Cauchy's estimate at radius `N/(log t+2E)` controls all orders
`1 ≤ N ≤ log t`. Completing the Gaussian square gives rates
`β+c/2−κc²/2`.

At `κ=133/200`, the four limiting gaps over the Euler-window loss are
`8803/4000000`, `6/845`, `161/28090`, `459/70225`, all positive.
The explicit choices `η=1/100000` and window width `1/1000` preserve all
four gaps. The Euler window therefore dominates every low even order.
The existing low-order transfer, reflection and heat propagation theorems
supply every even order, both height signs, and every larger heat.

## Lean

- `ArithmeticHarmonicAnalysis.exists_norm_riemannZeta_half_le_subWeyl`
  in [ZetaCriticalLineSubWeylBound.lean](../../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/ZetaCriticalLineSubWeylBound.lean).
- `ArithmeticHarmonicAnalysis.norm_riemannZeta_fiveSixths_le`
  in [ZetaFiveSixthsSubconvexity.lean](../../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/ZetaFiveSixthsSubconvexity.lean).
- `RHTower.DeBruijn.exists_xiSliceHeatTransfer_pos_heat_subWeyl`
  in [SubWeylSourcesLowerTheHeatFloor.lean](../../../../formal/GaloisForLFunctions/RHTower/Heat/SubWeylSourcesLowerTheHeatFloor.lean).

The arithmetic namespace is prefixed by `GaloisForLFunctions`.
All 21 modules passed direct Lean checks. Transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
