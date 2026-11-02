# Compact-profile tail uncertainty at growing overlap

- **ID:** compact-profile-tail-uncertainty-at-growing-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d; quantitative continuation of the positive conductor floor.
- **Statement:** There is a universal `b>0` such that every nonzero real compact `C²` profile on `[0,1]` admits `a>0` with `∫_(t>c)|φ̂(2πt)|²dt ≥ a exp(-bc)` for every `c≥0`. Consequently its completed conductor energy is at least `a' exp(-bc/m)` for all `c>0`, `m≥1`.

The integrated tail gives a quantitative conductor floor without excluding
real Fourier zeros.

## Proof

For the entire Fourier transform `F`, put `H(z)=F(2πz)F(-2πz)`.
Real amplitude gives `H(t)=|F(2πt)|²≥0` on the real axis. Compact support
gives `|H(z)|≤M² exp(B|z|)`, with `B=4π` and `M>0` bounding `|φ|`.
The formalized qualitative theorem supplies `z₀>0` and `h=H(z₀)>0`.

Set `q=48 exp(1)`, `D=(4qB+1)/log 2` and
`C=max(1,|z₀|,log(8M²/h))`. For `c≥C`, take `N=⌈Dc⌉` and the real
Taylor polynomial `P_N` of `H`. On `|t|≤2c`, the Cauchy circle of radius
`4qc` gives error at most `2M² exp(4qBc)(2q)^(-N)`.
Since `2^N≥exp((4qB+1)c)` and `exp(c)≥8M²/h`, this is at most
`δ=h/(4q^N)`. In particular, `|P_N(z₀)|≥3h/4`.

Apply `PolynomialExtrapolationRemez.volume_sublevel_comp_le` in the identity
chart on `(c,2c)`, with anchor `z₀`, distance bound `3c` and
`ε=h/(2q^N)`. The sublevel measure is at most `12 exp(1)c/q=c/4`, since
`εq^N=h/2<|P_N(z₀)|`. On the complement, `H(t)≥|P_N(t)|−δ>δ`.
Therefore its integral is at least `hc/(16q^N)` (retaining only a quarter
of the interval). Since `N<Dc+1` and `c≥1`, this is at least
`a₀ exp(-bc)`, where `a₀=h/(16q)` and the universal `b=D log q>0`.
For `0≤c≤C`, tail monotonicity supplies `T(c)≥T(C)≥a₀ exp(-bC)>0`.
Thus `a=a₀ exp(-bC)>0` proves the assertion for every `c≥0`.

The first coprime repayment term starts at `c/m` and carries coefficient
`(2/∫φ²)(m/φ(m))≥2/∫φ²`. Therefore
`completedConductorEnergy(φ,c,m)≥(2a/∫φ²)exp(-bc/m)`.
This is stronger than the conductor-independent exponential floor.

The circle remainder and real Taylor polynomial are formalized in
`RiemannGaussian.FiniteToEntireExpandingTaylor`; their degree bound is in
`FiniteToEntireDegreeControl`. The profile assumptions discharge all
analytic inputs; no concentration-gap hypothesis is introduced.

## Lean

- `CompactEntireDensityRetainsExponentialTails.lean`:
  `exists_exponential_lower_tail_of_entire_nonnegative`.
- `EveryCompactProfileHasAnExponentialConductorFloor.lean`:
  `exists_universal_exponential_shell_tail`;
  `exists_universal_exponential_completedConductor_floor`.

Both modules are in `CriticalArithmeticCorrelationTheory` and wired into
its umbrella. Direct Lean checks passed; all three transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.

Growing-overlap whole-span positivity remains a separate conjecture:
`arbitrary-profile-spans-at-growing-overlap`.
