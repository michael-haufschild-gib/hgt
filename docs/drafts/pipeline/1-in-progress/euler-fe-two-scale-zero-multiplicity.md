# Two Gaussian scales read the actual zero multiplicity

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Euler–FE transport theory: two-scale coupling and conditional prime discrepancies.

## Target

For every actual Xi zero `ρ`, let `mρ` be its multiplicity and put

`Gρ(y)=ΣₙΛ(n)n^(−ρ)e^(−yn²)−∫₁∞u^(−ρ)e^(−yu²)du`,

`Bρ(y)=Σ_{q:ρq≠ρ} ½Γ((ρq−ρ)/2)y^(−(ρq−ρ)/2)`.

For every `c>1`, prove unconditionally

`Gρ(y)−Gρ(cy)+Bρ(y)−Bρ(cy) → −mρ log(c)/2`, as `y→0⁺`.

All zero sums retain multiplicity and the full infinite complement. No extremal
abscissa, simplicity, finite exceptional layer or zero-free hypothesis is allowed.
This reads existing divisor multiplicity from the exact two-scale prime current;
it does not assert replication at a new height.

## Analytic mechanism

For nonresonant `a=ρq−ρ`, Gamma subtraction leaves
`e^(−y)(½−ρ)/[(ρq−½)a]` with error at most
`(2y+2y²)/(|a||a+2|)`. The reciprocal families at every complex centre
are square summable, so Cauchy–Schwarz controls both complete products.
Dominated convergence recovers the entire nonresonant finite part.

The resonant fibre contributes
`mρ[e^(−y)/(ρ−½)+E(y,0)]`, with `E(y,0)=½∫_y∞e^(−v)dv/v`.
Its two-scale difference tends to `mρ log(c)/2`; the archimedean and
nonresonant finite-part constants cancel. The exact prime explicit formula
fixes the negative sign in the target.

In fact, if `Cq=(½−ρ)/[(ρq−½)(ρq−ρ)]` and `γE` is Euler's constant,

`Gρ(y)+Bρ(y)−(mρ/2)log y → A(ρ)−mρ/(ρ−½)−Σoff Cq+mργE/2`.

The two-scale law follows by subtracting this limit at `y` and `cy`; the
same proof permits every fixed `c>0`. Absolute admission of `Bρ(y)` follows
from two incomplete-Mellin recursions: the remaining integral has bounded
real exponent, and its coefficient is the same summable reciprocal product.

## Remaining proof obligations

1. Absolute admission and finite-part limit for the full complex nonresonant
   Gamma series; finite-fibre splitting of the actual explicit formula.
2. Exact two-scale formula for `E(y,0)−E(cy,0)` and its limit.
3. Assemble the prime-current law and audit transitive axioms.
