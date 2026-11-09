# Divisor recovery under arbitrary damping contraction

- **Obstacle:** B13, B134.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let every zero copy outside finite `F` have real part at most `θ<σ`,
with `½<σ<Re ρ<1`, `ξ(ρ)=0`, and `r=a(Re ρ−σ)/2−π/4>0`.
For the pole-and-divisor filter of degree `d`, every eventually positive
`h(t)→0` satisfies

`A_{P_h}(t)/(h(t)^d K(exp(−at),ρ−σ−it))`
`→ −mρ(ρ−1)Π_{q∈F,ρq≠ρ}(ρ−ρq) ≠ 0`.

Here `mρ` is the actual analytic multiplicity. No contraction-rate condition
such as `dκ<r` remains. Raw growth still depends on the attenuated Gamma mode.

## Proof

Choose `σ<c<Re ρ` outside the finitely many exceptional abscissae, with
`a(c−σ)/2<r`. Shift the complete filtered Euler integral from `Re z=2`
to `Re z=c`. Its Mellin argument has positive real part throughout, so no
Gamma pole is crossed. The weighted argument principle for the entire
residue unit `(z−1)ζ(z)` supplies exact zero multiplicities. The polynomial
kills the pole and every unwanted zero residue.

The actual logarithmic derivative is `O(1+|Im z|)` on the left line:
above the finite packet, real or imaginary separation bounds its distance
from every zero; continuity bounds the remaining compact segment. The
filter and Gamma strip envelope give vanishing horizontal edges and

`|A_{P_h}(t)+mρ P_h(exp(h(ρ−β))) K(exp(−at),ρ−σ−it)|`
`≤ C h^d(1+|t|)^(d+1) exp(at(c−σ)/2)`

uniformly in `0≤h≤1`. The entire error retains `h^d`. After division,
the remainder is bounded by a polynomial times
`exp(−(r−a(c−σ)/2)t)`, independently of `h`. The derivative of the
exponential at zero supplies the finite product limit.

At cancelled simple zeros, the literal product need not equal its removable
value; the rectangle argument uses boundary values and the exact finite
residue theorem, so no unproved removable-extension claim enters.

## Consequence for the arithmetic bound

For exponential contraction with `dκ≥a(1−σ)/2`, the independent arithmetic
bound forces the raw prime filter to zero. The same filter still recovers
the nonzero divisor constant after normalization. Thus contraction-induced
smallness alone cannot contradict an exceptional layer. The unresolved
exponential gap remains `a(1−Re ρ)/2+π/4`.

## Lean source

- `ExceptionalLayerTheory/ContourBoundsForFiniteDivisorFilters.lean`:
  exact contour identity and spacing-preserving complete error bound.
- `ExceptionalLayerTheory/ArbitraryDampingContractionReadsTheDivisor.lean`:
  arbitrary-contraction limit, simultaneous raw decay and normalized recovery,
  and actual-divisor consequence of failure of AAL.

The arbitrary-contraction module passes direct source audit without warnings.
Its five audited declarations are:

- `tendsto_divisorDampingFilter_scaled_value_of_tendsto`
- `arbitrary_contracting_prime_filter_reads_selected_zero`
- `prime_filter_decay_and_normalized_divisor_recovery`
- `divisorDampingFilter_limit_constant_ne_zero`
- `not_asymptoticAbscissaLaw_has_arbitrarily_contracting_prime_filters`

The contour module compiles without warnings; all six transitive audits contain
only `propext`, `Classical.choice`, and `Quot.sound`, as do all five limit-module
audits. The final direct contour source audit is pending.
