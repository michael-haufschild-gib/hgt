# Multiplicity consumes a hyperbolic annihilator budget

- **Stage:** 1-in-progress
- **Type:** CANDIDATE — paper proof complete; Lean verification pending.
- **Obstacles:** B13, B112.
- **Statement:** For normalized positive two-prime Dirichlet polynomial `P`, write `H(u)=H_P(u)`. For `x>σ`, the full sum over zeros `ρ` right of `σ`, with multiplicities `mρ`, converges and obeys
  `Σ mρ log(|ρ+x−2σ|/|ρ−x|) ≤ log(1+H(σ))−log(1+H(x))`.
  Every finite sub-divisor inherits this bound.
- **Multiplicity consequence:** If `ρ=σ+δ+iγ`, `δ>0`, `γ≠0`, has order at least `n`, put `R=sqrt(δ²+γ²)`. Then
  `((R+δ)/(R−δ))^n ≤ 1+H(σ)`.
  The base exceeds one; bounded left-line mass therefore bounds multiplicity at a fixed nonreal point.

## Proof

The finite exponential sum is entire. Nonnegative coefficients and nonnegative frequencies give `|P(s)|≤1+H(σ)` for `Re s≥σ`, while `P(x)=1+H(x)≥1` on the real axis. Translation places the boundary at `Re s=½`. These facts discharge the growth, nonvanishing and real-ray conditions of the corpus Poisson–Jensen identity. Its full Green sum converges. The normalized boundary Poisson integral is at most `log(1+H(σ))`; subtracting `log P(x)` gives the stated budget.

Real coefficients give conjugate zeros with equal multiplicity and equal Green cost. Write `t=x−σ`. Twice the cost of either conjugate is
`log(((t+δ)²+γ²)/((t−δ)²+γ²))`.
At `t=R`, its argument is `(R+δ)/(R−δ)>1`. The difference between this value and the argument at arbitrary `t` is
`2δ(t−R)² / ((R−δ)((t−δ)²+γ²)) ≥ 0`.
Thus the balanced point maximizes the real-axis test. The pair's contribution is at least `n log((R+δ)/(R−δ))`. Drop the nonnegative term `log(1+H(x))` and exponentiate.

Exponential growth is attainable: `P=(1+2^(β−s))^n` has exact order `n` at `β+iπ/log 2` and
`H_P(σ)=(1+exp((β−σ)log 2))^n−1`.
This establishes the growth scale, not equality of the upper and lower exponential bases.

## Novelty and limits

Corpus baseline: arbitrary multiplicity near unit mass on the zero's own line; Chebyshev bounds with a frequency cutoff; the generic Poisson–Jensen identity. New result couples left displacement, height, multiplicity and the complete annihilator divisor through a concrete positive mass budget, without a frequency cutoff. No assertion about actual zeta zeros; B13 and B112 remain open. All claims count together as one contribution after audit.

## Lean target

`ArithmeticPositiveDuality/TheZeroDivisorConsumesAnnihilatorMass.lean`: complete divisor budget, finite-divisor budget, conjugate-pair cost, optimized Green test, exponential multiplicity bound and binomial-power witnesses. Verification pending; uncounted.
