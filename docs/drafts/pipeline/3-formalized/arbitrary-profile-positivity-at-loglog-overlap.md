# Arbitrary-profile positivity at log-log overlap

- **ID:** arbitrary-profile-positivity-at-loglog-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d; exponential conductor floors and relative quasimode budgets.
- **Statement:** There is a universal `B>0` such that every nonzero real `C²` profile supported on `[0,1]` admits `a>0` with the following property. For every `0<A<1/2` and `α>0` satisfying `2Bα<1`, eventually
  `Wφ,c,N(x)≥a exp(-Bc)‖x‖²`
  for all `1≤c≤α log log N` and all `x∈V_{⌊(log N)^A⌋}`.

## Proof

Take `B` at least the two universal rates in the formalized exponential
conductor floor and summed relative-residual budget. The conductor energies
satisfy `E_m(c)≥a₀ exp(-Bc)` for all `m≥1` and `c≥1`.

Write `L=log N`, `t=log L`, `Q=⌊L^A⌋` and
`θ=max(2Bα,2A)<1`. Choose an integer `k≥1` with `1/k<1−θ`.
For `1≤c≤αt`, the relative budget is bounded by
`C t⁹ L^(θ+1/k−1) + C' t¹⁴ L^(θ+2)/N²`.
Indeed, `(c+1)²≤4α²t²`, `exp(2Bc)≤L^(2Bα)`,
`Q²≤L^(2A)`, `1+log Q≤(1+A)t`, and `1+log c≤c`.
Both terms tend to zero: a power of `log L` is dominated by every positive
power of `L`, and `t¹⁴L^(θ+2)≤L¹⁷` eventually. The geometric width
condition also holds eventually.

The lower Riesz bound gives the dual frame estimate
`Σ_(m≤Q)|⟨v_m,x⟩|²≥‖x‖²/2` on `V_Q`; its horizon conditions
`Q²≤N` and `18(1+log Q)≤log N` hold eventually. Compress the actual
symmetric Weil operator orthogonally to `V_Q`. Projection preserves its
quadratic form there and contracts residuals.

For an eigenvector below `a₀ exp(-Bc)/2`, each frame coordinate squared
is at most four times its individual squared relative residual. Once their
sum is at most `1/16`, the unit eigenvector would have total coordinate
mass at most `1/4`, contradicting the lower frame bound `1/2`.
Every eigenvalue of the compression therefore exceeds this half-floor.
Set `a=a₀/2`. Its value is independent of `A` and `α`.

## Lean

`CriticalArithmeticCorrelationTheory/EveryProfileIsPositiveAtLogLogOverlap.lean`:
`exists_universal_loglog_overlap_coercivity` passed its direct Lean check
and transitive axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
The module is wired into the umbrella. The moving residual and frame
horizons are discharged in the theorem; no analytic input is assumed.
