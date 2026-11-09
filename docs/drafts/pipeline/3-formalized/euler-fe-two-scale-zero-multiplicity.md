# Two Gaussian scales read the actual zero multiplicity

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport theory: two-scale coupling and conditional prime discrepancies.

## Theorem

For every actual Xi zero `ρ`, let `mρ` be its multiplicity and put

`Gρ(y)=ΣₙΛ(n)n^(−ρ)e^(−yn²)−∫₁∞u^(−ρ)e^(−yu²)du`,

`Bρ(y)=Σ_{q:ρq≠ρ} ½Γ((ρq−ρ)/2)y^(−(ρq−ρ)/2)`.

For every `c>0`, unconditionally

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

## Formalization

`EulerFETransportTheory/GaussianRenormalizationAtZeros.lean` proves absolute
admission, the finite-fibre split, the exponential-integral limit and the
assembled identity. Terminal declarations:

- `summable_norm_nonresonantGaussianModes`
- `tendsto_gaussianPrimeGap_resonantFinitePart`
- `tendsto_gaussianPrimeGap_logarithmicFinitePart`
- `two_gaussian_scales_read_zero_multiplicity`

Direct Lean checking succeeds. All four transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Dependency-closed paper argument

1. The existing Xi Cauchy-square theorem gives
   `Σq |ρq−s|⁻²<∞` at every complex centre `s`, with inverse zero assigned on
   its finite resonant fibre. Cauchy–Schwarz therefore makes both
   `Σoff |Cq|` and `Σoff (|ρq−ρ||ρq−ρ+2|)⁻¹` finite.
2. Two integrations by parts give, with `a=ρq−ρ`,
   `germ=e^(−y)Cq+[-2ye^(−y)+4y²E(y,a+4)]/[a(a+2)]`.
   All actual zeros lie in the open unit strip, so `Re(a+4)−1<4`.
   The incomplete-Mellin bound with exponent `4` supplies one finite bound
   for every numerator at fixed `y>0`. Thus the complete nonresonant germ
   series converges absolutely.
3. The Gamma-subtracted error bound above makes its remainder absolutely
   summable too. Subtracting the two admitted series proves absolute admission
   of the entire nonresonant Gamma field. For `0<y≤1`, the remainder is bounded
   by `|Cq|+4/(|a||a+2|)` and tends to `Cq`. Dominated convergence applies.
4. Split the exact Gaussian prime explicit formula into the complete finite
   resonant fibre and its infinite complement. The archimedean Mellin–Barnes
   current tends to `A(ρ)`. Hence
   `Gρ+Bρ+mρE(y,0) → A(ρ)−mρ/(ρ−½)−Σoff Cq`.
5. The upper incomplete Gamma representation gives
   `E(y,0)=½∫_y∞e^(−v)dv/v`. The proved exponential-integral limit
   `∫_y∞e^(−v)dv/v+log y→−γE` gives the stated logarithmic finite part.
6. Apply the same limit at `cy`, subtract, and use
   `log(cy)=log c+log y`. The constant cancels, leaving `−mρ log(c)/2`.

## Scope

The Gamma counterterms depend on the full divisor. This is a renormalization
law for the actual infinite prime current, not an independent prime-only
multiplicity selector. No new-height recurrence, same-depth replication,
`LinAt C`, or AAL follows from this identity alone.
