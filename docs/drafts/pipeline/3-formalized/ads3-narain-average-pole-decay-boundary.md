# One averaged Narain source detects every arithmetic decay obstruction

- **ID:** W11-NAB
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Actual target average](ads3-narain-target-average.md)
- **Statement:** For every fixed `Y,Z>0`, every resonance `p` with
  `ξ(1+2p)=0`, and every `α>1/2−Re p`, no constants `a,b` make
  `yA_YZ(y)−a log y−b = O(y^α)` at zero. Any positive-power expansion
  forces `a=−3/π`. Rates `y^(1−σ₀/2−ε)` for every positive `ε`
  imply `ξ(s)≠0` on `Re s>σ₀`; at `σ₀=1/2`, they imply RH.

## Proof

The filled mean numerator is

`T_Y(u)=(2u−1)Y^(1/2+u)ξ(1+2u)+(1+2u)ξ(2u)Y^(1/2−u)`.

It is entire, equals one at `u=1/2`, and vanishes at zero. At each arithmetic
resonance it is `(2p−1)C_Y(p)≠0`, by the proved nonvanishing constant term.
The actual average has Mellin continuation `F_YZ` satisfying

`u(1+2u)ξ(1+2u)(u−1/2)²F_YZ(u)=T_Y(u)T_Z(u)/2`

on its convergence half-plane.

Subtract the cutoff main term `(a log y+b)/y`. A claimed rate makes the
remainder `O(y^(α−1))` at zero. The proved continuity and exponential tail
supply the remaining Mellin hypotheses, giving holomorphy on
`Re u>1/2−α`. Subtract the exact main-term Mellin transform and clear both
denominators. Analytic uniqueness extends the cleared identity over this
connected half-plane. At `u=p`, its left side vanishes and its right side
is nonzero. At `u=1/2`, the identity instead gives `a=−3/π`.

The same averaged profile detects every resonance, including multiple zeros.
No selection of point targets depends on the zero. If rates
`y^(1−σ₀/2−ε)` held for every positive `ε`, a zero with
real part `β>σ₀` would contradict the obstruction at `ε=(β−σ₀)/4`.
The corpus's exact xi zero-free characterization then gives RH at
`σ₀=1/2`. No positive power rate is asserted.

## Lean

Namespace `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`:

- `NarainMeanNumerator`: entire filled mean numerator, universal main
  coefficient, nonvanishing at every resonance and the cleared identity.
- `narainScalarHeatAverage_no_faster_decay` in `NarainAverageDecay`: the fixed
  source has no power remainder beyond any arithmetic resonance.
- `narainAverageRate_log_coefficient`: any positive-power expansion forces
  logarithmic coefficient `−3/π`.
- `xi_ne_zero_of_narainAverageRate`: rates `y^(1−σ₀/2−ε)` for all positive
  `ε` exclude xi zeros in `Re s>σ₀`.
- `riemannHypothesis_of_narainAverageRate`: the three-quarter rate of one
  fixed averaged source implies mathlib's `RiemannHypothesis`.

Both modules pass direct Lean checks. Seven endpoint axiom audits use
only `propext`, `Classical.choice`, and `Quot.sound`; umbrella imports
are wired. The rate-to-RH implication is proved; its rate premise remains
open. The [exact constant term and weighted residue](ads3-narain-average-principal-part.md)
are also formalized. The [converse rate implication](../0-backlog/ads3-narain-average-sharp-rate.md)
remains open.

## Gates

- [x] 0 → 1: fixed source and noncancellation mechanism identified.
- [x] 1 → 2: all source inputs and analytic uniqueness discharged.
- [x] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
