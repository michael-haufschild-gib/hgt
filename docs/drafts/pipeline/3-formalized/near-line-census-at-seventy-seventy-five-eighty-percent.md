# Near-line census at 70%, 75%, and 80%

Let `N(T,2T)` count all zeros, `N₀(T,2T)` those on the critical line,
and `S_A(T,2T)` the simple off-line zeros at distance at most `A/log T`
from that line. For every `A>0` and `ε>0`, eventually in `T`:

| Target `θ` | Alternative to `N₀ ≥ θN` |
|---|---|
| `7/10` | `S_A ≥ (HD(1) − 2/5 − 1/A − ε)N` |
| `3/4` | `S_A ≥ (HD(1) − 1/2 − 1/A − ε)N` |
| `4/5` | `S_A ≥ (HD(1) − 3/5 − 1/A − ε)N` |

These are the exact specializations of the proved coefficient
`1 + HD(1) − 2θ − 1/A − ε`. They are alternatives, not claims that
any of the three critical-line targets is attained.

## Lean

- Existing 70%: `RHTower.seventy_percent_or_simple_offLine_near_line`
  in `RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean`.
- Existing 75%: `RHTower.three_quarters_or_simple_offLine_near_line`
  in `RHTower/Zeta23SimpleOffLineNearLine.lean`.
- 80%: `GaloisForLFunctions.SquareRootThreshold.Census.four_fifths_or_simple_offLine_near_line`
  in `SquareRootThreshold/Census/NamedProportionAlternatives.lean`.

Direct `lake --old env lean` audit passed. All three transitive axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
