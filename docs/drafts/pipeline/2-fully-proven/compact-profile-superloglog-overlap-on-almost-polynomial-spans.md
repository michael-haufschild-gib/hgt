# Compact profiles beyond log-log overlap on almost-polynomial spans

- **Stage:** 2-fully-proven; Lean capstone written, checks pending.
- **Wall:** Σ1d.
- **Theorem:** For every nonzero compact real `C²` profile, one explicit clock `Cφ(N)` satisfies `Cφ(N)/log log N→∞`. For every `0<η<1/2` and `κ>2`, eventually `Wφ,c,N(x)≥(log N)^(-η)‖x‖²/4` on `V_floor(exp(log N/(log log N)^κ))`, uniformly for `1≤c≤Cφ(N)`.

## Spectral clock

Put `Hφ=shellSpectrum φ`, `L=log N`, `t=log L`, and
`Gφ(s)=∫_(u>s)|log Hφ(u)|/(1+u²)du`.
The nonzero compact Fourier transform is entire, so its real zero set is null.
Its Poisson-weighted logarithm is integrable. Comparing quadratic denominators
gives standard-weight integrability; hence `Gφ≥0` is decreasing and tends to zero.

For `s≥1`, write `E=∫_(u>s)Hφ(u)>0`. Integrating
`-log E+1≤Hφ(u)/E+|log Hφ(u)|` on `(s,2s]` gives
`s(-log E+1)≤1+5s²Gφ(s)`, hence `E≥exp(-5sGφ(s))`.

Define `gφ(t)=Gφ(t)+1/t` and `Cφ(N)=min(t log t,t²,t/sqrt(gφ(t)))`.
Then `Cφ(N)/t=min(log t,t,1/sqrt(gφ(t)))→∞`.
Eventually `Cφ(N)≥t`, so `Cφ(N)Gφ(Cφ(N))≤t sqrt(gφ(t))=o(t)`.
Tail monotonicity therefore gives every floor `exp(-εt)` throughout
`0≤c≤Cφ(N)`. The first coprime repayment gives
`E_m(c)≥(2/∫φ²)tail(c/m)≥(2/∫φ²)tail(c)`.
Absorbing this fixed positive factor with exponent `η/2` yields the common
conductor floor `L^(-η)`.

## Positivity mechanism

Choose `q=(1-2η)/4>0` and an integer `k≥1` with `2q+1/k+2η<1`.
On `Q=floor(L^q)`, the summed raw residual at `c≤t²` is bounded by
`Cφ,q[L^(2q+1/k−1)t^12+L^(2q+2)t^22/N²]=o(L^(-2η))`.
The lower frame and relative quasimode bound give low-block coercivity
`L^(-η)/2`; the summed raw budget `≤L^(-2η)/128` bounds the mixed pairing
by `L^(-η)‖p‖‖z‖/8`.

## Conductor cutoff

Take `Rκ(N)=floor(exp(L/t^κ))` for `κ>2`,
which exceeds every fixed power of `log N`. In the nine-term high-band
budget, the largest logarithmic error is
`c²(1+log Rκ)(1+log c)/L=O(t^(2−κ)(log t)^3)→0`.
The remaining horizon terms vanish since `Rκ≤N^θ` eventually for every
fixed `θ>0`. Since `log Q=qt+O(1)` and `log c≤2log t=o(t)`, the high-block
gap eventually exceeds one. Orthogonal splitting and
`2‖p‖‖z‖≤‖p‖²+‖z‖²` retain margin `L^(-η)/4`.

## Lean boundary

- `LogarithmicTailMassGivesAnExplicitSpectralFloor.lean`: checked, clean transitive axiom audits.
- `EveryCompactProfileHasAnExplicitTailClock.lean`: spectral and conductor floors checked with clean audits; sharper `t log t` cap awaiting check.
- `LogarithmicFloorsControlQuadraticOverlapResiduals.lean`: direct check passed; transitive audit contains only `propext`, `Classical.choice`, `Quot.sound`.
- `AlmostPolynomialConductorSpansRetainHighEnergyGaps.lean`: horizon written, unchecked.
- `EveryCompactProfileIsPositiveBeyondLogLogOverlap.lean`: capstone written, unchecked.
