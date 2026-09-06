# Decreasing-weight Möbius–divisor producer

- **Status:** active [BRIDGE] DW1, unproved.
- **Full chain:** actual arithmetic divisor source -> source diagonal dominance for decreasing
  kernels -> square-root Abel source estimate -> strict-right continuation -> RH.
- **Open cores:** the cone inequality itself; the explicit formal continuation bridge permitting
  the harmonic diagonal loss. No supporting diagonal bound is counted as the missing producer.

Let `D(q)=log(q!)-sum tau+2 gamma q`. For every finite nonnegative decreasing weight sequence,
put `C_d=mu(d) sum_(k>=d) w_k D(floor(k/d))`. DW1 asserts `(sum C_d)^2<=sum C_d^2`.
The square-root kernel is one member. This proposes monotone smoothing as an explanation for
SD1; it does not assume SD1 or infer it from finite computation.

[Protocol](../2-fully-proven/computations/mobius-divisor-decreasing-weights-2026-09-06/PROTOCOL.md).

The route survey distinguishes this source question from global Weil positivity, spectral
occurrence, singular landing, and theta compact-sign questions. The prime-side Weil lag uses
another arithmetic Abel readout; its existing truncation-horizon experiment already tests
omitted prime powers. Here the complete finite divisor source is retained and the entire
admissible time-weight cone is attacked, rather than repeating that omission experiment.
