# Quadratic collar payment on polynomial conductor spans

- **Stage:** 3-formalized.
- **Wall:** Σ1d; near Gamma/downward-prime payment.
- **Theorem:** Every nonzero compact real `C²` profile admits `bφ>0` and an exponential coercivity margin on `V_floor(N^θ)`, `0<θ<1/1080`, uniformly for `1≤c≤bφ sqrt(log log N)`. This includes every `c≤(log log N)^β`, `β<1/2`.

## Weighted terminal pairing

Write `L=log N`, `u=Σ_(m≤R)a_m v_m`, and
`G=Σ_(m≤R)(1+log m)a_m²`. The existing packet estimate is

`‖(overlap−downward)u‖² ≤ Cφ c⁴(1+log R)[(1+log c)/L+R²L/N]G`.

The output vanishes below `N/(linearNearRowRadius c+1)`. A unit conductor
packet has at most `20(1+log c)/L` squared mass in that terminal interval.
Cauchy–Schwarz therefore gives the stronger quadratic pairing estimate

`|⟨(overlap−downward)u,u⟩|² ≤ 20Cφ c⁴(1+log R)[(1+log c)²/L²+R²(1+log c)/N]G`.

For polynomial `R` and `c` bounded by any fixed power of `log L`, this
coefficient tends to zero. Young's inequality then pays the near term
with a fixed fraction of prime adjunction and a bounded loss. The existing
center and separated bounds cost `Oφ(c²)`; the upward loss also fits this
bound. The resulting high gap is

`W(u)≥Eadj/16+(log Q)/4−Cφc²`.

With `Q=floor(L^(1/8))`, a sufficiently small `bφ` keeps this gap above one.
The existing exponential low-block floor and raw mixed residual budget
then complete the orthogonal split.

## Horizon and assembly

`ConductorBandQuadraticCancellation.lean` proves the exact support cutoff
and the terminal-mass mechanism. `WeightedConductorCrossBounds.lean`
supplies the logarithmically weighted norm estimate. Their combination
avoids a new pointwise-to-packet transfer.

Put `t=log L` and choose `bφ=min(1,1/sqrt(128(Cφ+1)))`.
For `c≤bφ sqrt t`, the terminal coefficient is bounded by
`(1+θ)[t^6/L+L^6/N^(1−2θ)]→0`.
Also `Cφc²≤t/128`, whereas `(log Q)/4≥t/32−(log 2)/4`.
Thus the high gap exceeds one eventually. The geometric conditions
follow from `1080θ<1` and `2θ,6θ<1`.

Since `sqrt t=o(t)`, the existing universal exponential low-block floor
and its summed raw residual bound both apply. Orthogonal splitting retains
half that floor. The constants `aφ,bφ` are independent of `θ`.

## Lean boundary

The terminal weighted pairing passed a direct Lean check; its transitive axiom audit
contains only `propext`, `Classical.choice`, `Quot.sound`.

Lean status:

- `TerminalSupportLeavesOnlyALinearHighConductorLoss.lean`: stronger linear loss;
  direct check and transitive axiom audit passed. The quadratic bound follows
  from `c≤c²` for `c≥1`.
- `EveryProfileIsPositiveAtSquareRootLogLogOverlapOnPolynomialSpans.lean`:
  `exists_universal_sqrt_loglog_polynomial_span_coercivity` directly checked;
  transitive audit contains only `propext`, `Classical.choice`, `Quot.sound`.

The square-root capstone is written as a restriction of the stronger fixed log-log
theorem in `EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans.lean`.
