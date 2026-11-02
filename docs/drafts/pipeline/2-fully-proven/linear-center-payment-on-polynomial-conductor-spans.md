# Linear center payment on polynomial conductor spans

- **Stage:** 2-fully-proven; Lean capstone written, checks pending.
- **Type:** THEOREM (paper).
- **Wall:** Σ1d.
- **Statement:** Every nonzero compact real `C²` profile admits `aφ,bφ>0` and a universal `B>0` such that, for every `0<θ<1/1080`, eventually `Wφ,c,N(x)≥aφ exp(-Bc)‖x‖²` on `V_floor(N^θ)` uniformly for `1≤c≤bφ t/sqrt(1+log t)`, where `t=log log N`.

## Mechanism

The weighted terminal pairing pays the merged near term with a fixed fraction of
prime adjunction and bounded loss when its explicit terminal coefficient is at most one.
The quadratic center estimate gives `600c(1+log R)/log N`, rather than a quadratic
Young loss. The separated quadratic estimate gives `Cφ c²/log N`.
The upward estimate costs `Cφ c sqrt(1+log c)`; this is the remaining dominant term.

Write `L=log N`, `H=1+log R`, and `G=Σ(1+log m)a_m²` for a unit packet.
The terminal coefficient is
`T=c⁴H[(1+log c)²/L²+R²(1+log c)/N]`.
When `T≤1`, the near pairing has square at most `Cnear G≤Cnear(2+Eadj)`;
Young's inequality pays it with `Eadj/32+8(Cnear+1)+1/16`.
Moreover `(c²/L)²≤T`, so the separated cost is bounded.
The center cost is at most `600c` under the frame geometry.
Combining these bounds with the prime lower bound and self-energy identity gives
`W≥Eadj/16+(log Q)/4−Cφ c sqrt(1+log c)` for a fixed `Cφ>0`.

For `R=floor(N^θ)` and `c≤t`,
`T≤(1+θ)[t⁶/L+L⁶/N^(1−2θ)]→0`.
All finite horizon conditions hold since `θ<1/1080`.
Take `Q=floor(L^(1/8))` and
`bφ=min(1,1/[128(Cφ+1)])`.
If `c≤bφ t/sqrt(1+log t)`, then `c≤t` and
`Cφ c sqrt(1+log c)≤t/128`, while
`log Q/4≥t/32−log 2/4`. Thus the high-block gap eventually exceeds one.

The overlap bound is `o(t)`. Fix the universal exponential rate `B` and choose
`γ>0` with `2Bγ≤1/4` inside the existing low-block interval. Eventually `c≤γt`.
The all-polylogarithmic coercivity theorem supplies `e=aφ exp(-Bc)` on `V_Q`,
with `0<e≤1`; the raw residual budget is at most `e²/128` and bounds the mixed
pairing by `e‖p‖‖z‖/8`. Orthogonal splitting retains margin `e/2` on `V_R`.

## Exact inputs

- `TerminalSupportSharpensTheWeightedNearPairing.lean`: weighted terminal estimate; direct check passed with a clean transitive axiom audit.
- `abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace`: center quadratic estimate, verified source statement.
- `abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace`: separated quadratic estimate, verified source statement.
- `exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace`: upward norm bound.

- `TerminalSupportLeavesOnlyALinearHighConductorLoss.lean`: stronger linear finite bound
  written; unchecked.
- `EveryProfileIsPositiveAtNearlyLogLogOverlapOnPolynomialSpans.lean`: capstone
  `exists_universal_nearly_loglog_polynomial_span_coercivity` written; unchecked.

The capstone now restricts the stronger fixed log-log theorem in
`EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans.lean`.
