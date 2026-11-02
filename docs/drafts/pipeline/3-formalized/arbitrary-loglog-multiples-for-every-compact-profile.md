# Arbitrary log-log multiples for every compact profile

- **Stage:** 3-formalized
- **Wall:** Σ1d.
- **Statement:** Every nonzero real compact `C²` profile on `[0,1]` and every `K>0` admit `B,a>0` such that, for every `A>0`, eventually in `N`,
  `Wφ,c,N(x)≥a exp(-Bc)‖x‖²`
  on `V_floor((log N)^A)`, uniformly for `1≤c≤K log log N`.
  The prefactor is independent of `A`; the proof takes `B=1/(16K)`.

## Proof

Write `L=log N`, `t=log L`, and split at `Q=floor(L^(1/8))`.
The subexponential floor gives `E_m(c)≥a₀ exp(-Bc/m)` with the chosen
`B`. On the low block, the summed raw residual, multiplied by
`exp(2Bc)`, is bounded by `C[L^(-1/4)t^12+L^25/N²]`, which tends to zero.
The finite-frame compression retains half the common floor.
Orthogonality removes the prescribed conductor energies from the mixed
pairing, leaving only the same small raw residual.

On the complementary conductor band through
`R=floor(L^max(A,1/8))`, all nine high-band errors tend to zero.
The remaining logarithmic gap grows as `t/32−log(Kt)−Cφ`.
For large `N`, `c≤Kt≤t²`, so `log c≤2log t=o(t)`.
The orthogonal split retains one quarter of the common low-block floor.

## Lean

`CriticalArithmeticCorrelationTheory/EveryPolylogConductorSpanIsPositiveAtLogLogOverlap.lean`:
`exists_loglog_overlap_all_polylog_coercivity`.

Direct check passed. Its transitive axiom audit contains only
`propext`, `Classical.choice`, `Quot.sound`. The universal-small-multiple
capstone remains checked and available. Umbrella import is wired.
