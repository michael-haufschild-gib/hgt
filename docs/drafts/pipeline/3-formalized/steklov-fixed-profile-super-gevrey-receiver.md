# One fixed Steklov profile at super-Gevrey overlap

- **ID:** steklov-fixed-profile-super-gevrey-receiver
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `β>2`, eventual complete Weil positivity on the atomic families
  of the single profile `steklovDCProfile`, at overlap
  `c_N=loglog N (logloglog N)^β`, is equivalent to RH.
- **Module:** `TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean`.

## Mathematical content

Summable moving-average radii
`a_m=1/(4(m+3)(log(m+3))²)` produce a smooth profile supported in `[-1,1]`
with integral one. Its derivative integrals satisfy a fixed-constant bound of the form
`A·12^q·q!·(log(q+3))^(2q)`.

Euler–Maclaurin synthesis uses this logarithmic derivative weight. The mollification part
of `dcSynthErr` is `M·b·dcLogWeight 1·k⁻¹·A₀`, where
`dcLogWeight 1=(log 4)²`. Retaining this factor preserves all limiting estimates because
it is constant. Under the stated overlap schedule, synthesis converges in the topology
controlling the complete Weil form, including prime, Gamma, and polar terms.

Thus eventual positivity on these finite atomic families is equivalent to positivity on
all real compactly supported `C²` tests, and hence to RH. For every `ε>0`, the overlap
schedule is `o((loglog N)^(1+ε))`.

## Lean declarations

- `contDiff_steklovDCProfile`
- `steklovDCProfile_vanishesOff`
- `integral_steklovDCProfile`
- `integral_abs_iteratedDeriv_steklovDCProfile_le`
- `superGevreyRatio_isLittleO_loglog_rpow`
- `riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`

Direct `lake --old env lean` audit passed. All six transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The module is imported by its umbrella.
