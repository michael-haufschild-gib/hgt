# The second odd lag moment is a position square

- **ID:** F1-M2
- **Stage:** 3-formalized
- **Type:** THEOREM; individually Lean-audited
- **Source:** [Retained Gamma payment](f1-gamma-lag-moment-payment.md)
- **Statement:** For a real continuous compact odd source supported in `[-a,a]`,
  `∫₀²ᵃ t²C(t)dt=−(∫xF(x)dx)²`, where `C(t)=∫F(x)F(x+t)dx`.
  On the unit window, `M₂=E/3+(∫xF)²≤5E/12`.

## Proof

Compact support makes `t²F(x)F(x+t)` integrable on the product. Fubini and `y=x+t`
give the full-line second correlation moment
`∫∫(y−x)²F(x)F(y)dxdy=2(∫F)(∫x²F)−2(∫xF)²`.
Oddness kills `∫F`. The correlation is even and vanishes outside `[-2a,2a]`, giving
the half-line identity. Integrating `t²E` gives the deficit identity.

For `a=1/2`, Cauchy–Schwarz gives `(∫xF)²≤E∫_{−1/2}^{1/2}x²=E/12`, hence
`M₂≤5E/12`. Combined with `M₁≤3E/4`, the retained Gamma payment improves the
uniform loss from `5/96` to `7/192`. The gain is `E/64` for every odd unit-window test.

**Lean:** `LatticeSectionTheory.WindowJumpCounts.OddAutocorrelationSecondMoment` proves
`odd_autocorr_second_moment`, `unit_odd_jump_second_moment`,
`unit_position_moment_square_le`, and `unit_odd_jump_second_moment_le`.
`WindowTowerOfSpecZ.TheGammaComparisonRetainsItsLagMoments` proves the exact position-square
substitution and the uniform `7/192` corollary. Both individual `lake --old env lean` source
audits pass; transitive axioms are `[propext, Classical.choice, Quot.sound]` only. Both modules
are wired into their umbrellas. The complete unit-window sign remains open.
