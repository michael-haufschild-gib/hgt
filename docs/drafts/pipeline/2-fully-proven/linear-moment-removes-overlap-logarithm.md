# Linear moment removes the overlap logarithm

- **Stage:** 2-fully-proven; Lean written, checks pending.
- **Type:** THEOREM (paper).
- **Wall:** Σ1d.
- **Target:** A profile-dependent positive multiple of `log log N` is coercive on every `V_floor(N^θ)`, `0<θ<1/1080`.

## Quadratic estimate

The overlap kernel has magnitude at most `Cφ log N` on its near band.
Near-row geometry gives `|j−n|≤C c n/N`, rather than merely `|j−n|≤C c`.
Integer separation makes each nonempty near row contain at most `C' c n/N` indices.
Put `r(c)=2c exp(2)`. The exact bound is
`#near(n)≤2r(c)n/N`.
For the symmetric near relation, summing
`2|u_nu_j|≤u_n²+u_j²` gives
`Σ_near |u_nu_j|≤Σ_n #near(n)u_n²`.
Hence a kernel bound `Mφ log N` gives
`|⟨overlap u,u⟩|≤2r(c)Mφ log N Σ_n(n/N)u_n²`.

A conductor packet satisfies the linear-moment bound
`Σ_n n|u_n|²≤4 N/log N ‖u‖²` when `R⁴≤N` and the frame inequality holds.
This is `sum_linear_moment_sq_le_four_div_log` in
`ConductorBandPrimeAndCenterBounds.lean`.
Combining these estimates gives
`|⟨overlap u,u⟩|≤16 exp(2)Mφ c‖u‖²`, removing `1+log c` entirely.
The previous proof bounds both arguments only by total terminal mass, discarding
the factor `n/N` in the row count.

## Positivity consequence

Use the exact quadratic identity
`W=prime+self+center−separated−overlap+2(near−downward)`.
For a unit packet, the terminal coefficient `T≤1` bounds the near pairing by
`Eadj/32+8(Cnear+1)+1/16`; its double therefore costs at most
`Eadj/16+16(Cnear+1)+1/8`.
The prime lower bound retains `Eadj/8+log Q/4−(log 4+4)`.
The center costs at most `600c`, the separated term is bounded because
`(c²/log N)²≤T`, and self-energy loses only a constant plus `log c`.
Thus `W≥Eadj/16+log Q/4−Cφc` for a fixed `Cφ>0`.

Write `L=log N`, `t=log L`. For `R=floor(N^θ)`, `θ<1/1080`, and `c≤t`,
`T≤(1+θ)[t⁶/L+L⁶/N^(1−2θ)]→0`; all finite geometry conditions hold.
Take `Q=floor(L^(1/8))` and let `γ>0` lie inside the universal exponential
low-block interval with `2Bγ≤1/4`. Set
`bφ=min(1,γ,1/[128(Cφ+1)])`.
Then `Cφc≤t/128`, while `log Q/4≥t/32−log 2/4`, so the high gap exceeds one.
The low-block margin `e=aφ exp(-Bc)≤1` and raw budget `≤e²/128` control the
mixed pairing by `e‖p‖‖z‖/8`. Orthogonal splitting retains `e/2` on `V_R`.

The proof of `nearRow_geometry_small_width` already derives
`|j−n|≤n*linearNearRowRadius(c)/N` before weakening it.
Applying `card_near_le` with that radius gives the required sharp row count.
Both source statements and the stronger intermediate distance inequality have been checked.
## Lean boundary

- `TheLinearMomentRemovesTheOverlapLogarithm.lean`:
  `exists_overlapMatrix_self_inner_le_linear` directly checked; transitive audit
  contains only `propext`, `Classical.choice`, `Quot.sound`.
- `TerminalSupportLeavesOnlyALinearHighConductorLoss.lean`:
  `exists_profile_highConductor_linear_loss_of_terminal_budget` written, unchecked.
- `EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans.lean`:
  `exists_universal_loglog_polynomial_span_coercivity` written, unchecked.

The terminal weighted pairing is supplied by
`TerminalSupportSharpensTheWeightedNearPairing.lean`; direct check passed,
with only `propext`, `Classical.choice`, `Quot.sound` in its transitive axiom audit.
