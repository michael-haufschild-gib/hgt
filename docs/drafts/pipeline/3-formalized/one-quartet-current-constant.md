# The one-quartet current constant

- **ID:** A47
- **Stage:** 3-formalized
- **Lean:** `ExceptionalLayerTheory/ASingleTopQuartetCannotCancelItsCurrent.lean`

If the actual finite top layer `G` has only the ordinates `±γ`, conjugation
gives equal multiplicities. Its limiting normalized wave is

`(|G|/2)(W_γ+W_{−γ})`, with `|W_±γ|=exp(±πγ/4)`.

The reverse triangle inequality therefore gives the exact positive lower
bound `(|G|/2)(exp(πγ/4)−exp(−πγ/4))`. The proved current asymptotic gives
the eventual bound

`|normalizedExceptionalCurrent| ≥ (|G|/4)(exp(πγ/4)−exp(−πγ/4))`.

At every speed `a(β−σ)>π/2`, the pole norm tends to infinity, so the
corrected current does too. The quantitative dichotomy retains the other
possibility: two distinct positive top ordinates. No cancellation premise
is added. Direct Lean check passed.

Declaration: `not_asymptoticAbscissaLaw_has_quantitative_top_ordinate_dichotomy`.
