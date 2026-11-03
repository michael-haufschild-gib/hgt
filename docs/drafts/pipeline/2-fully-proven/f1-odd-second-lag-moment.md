# The second odd lag moment is a position square

- **ID:** F1-M2
- **Stage:** 2-fully-proven; Lean formalization in progress
- **Type:** THEOREM (paper)
- **Source:** [Retained Gamma payment](../3-formalized/f1-gamma-lag-moment-payment.md)
- **Statement:** For a real continuous compact odd source supported in `[-a,a]`,
  `∫₀²ᵃ t²C(t)dt=−(∫xF(x)dx)²`, where `C(t)=∫F(x)F(x+t)dx`.
  Consequently `∫₀²ᵃt²(E−C(t))dt=(8a³/3)E+(∫xF)²`.

## Proof

Compact support makes `t²F(x)F(x+t)` integrable on the product. Fubini and `y=x+t`
give the full-line second correlation moment
`∫∫(y−x)²F(x)F(y)dxdy=2(∫F)(∫x²F)−2(∫xF)²`.
Oddness kills `∫F`. The correlation is even and vanishes outside `[-2a,2a]`, giving
the half-line identity. Integrating `t²E` gives the deficit identity.

For `a=1/2`, Cauchy–Schwarz gives `(∫xF)²≤E∫_{−1/2}^{1/2}x²=E/12`, hence
`M₂≤5E/12`. Combined with `M₁≤3E/4`, the retained Gamma payment improves the
uniform loss from `5/96` to `7/192`. The gain is `E/64` for every odd unit-window test.

**Lean:** pending `LatticeSectionTheory.WindowJumpCounts.OddAutocorrelationSecondMoment`
and its Gamma corollary.
