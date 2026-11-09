# Signed deletion on logarithmic-square windows

**Target.** Derive the two-sided local width criterion without positive
averaging or negative-excursion arguments. The existing one-sided theorem
does not provide this proof.

## Complex deletion kernel

For a deleted exponent `λ=a+iγ`, put `h=2π/(3γ)` and

`b = cosh(ha)/2 − i√3 sinh(ha)/2`,

`Qλ(w) = (cosh(hw)+b)/(1+b)`.

Then `Qλ(λ)=0`, `Qλ(0)=1`, and `Re b≥1/2`. Its three translation
coefficients are `1/(2(1+b)), b/(1+b), 1/(2(1+b))`; they need not be
real. Conjugate-pair multiplication must not replace this kernel by a
positive one.

Writing `x=ha`, the variation mass is
`m=(1+|b|)/|1+b|`. Since `|b|²=(Re b)²+(Im b)²`,

`m ≤ 1 + (Im b)²/(2 Re b (1+Re b))
   ≤ 1 + (3/2)tanh² x ≤ exp((3/2)x²)`.

The absolute exponential moment is at most
`m exp(min(|hs|,s²h²/2))`. Thus bounded real parts and square-summable
shifts give finite total variation; the existing ordinate head/tail
estimates yield logarithmic-square leakage. For retained `w`,
`|Qλ(w)−1| ≤ (2/3)h²|w|²` when `|hw|≤1`, so a sufficiently late
infinite product is nonzero at `w` and deletes a cofinite spectrum.

## Finite-spectrum endpoint

For a finite set `S` of distinct exponents choose `δ>0` with the values
`exp(δz)`, `z∈S`, distinct. The polynomial
`P(X)=∏_{z∈S\{z₀}}(X−exp(δz))` gives the exact translation identity

`Σ_j P_j F(T+jδ) = c(z₀)exp(z₀T)P(exp(δz₀))`.

Its triangle inequality forces a large absolute value within a fixed
distance of every `T` when `Re z₀>0`. No conjugation symmetry, absence
of real exponents, or sign of the trace is needed.

**Lean status:** `SignedDeletionFilters` and `SignedConvolutionBounds`
compile with only `propext`, `Classical.choice`, `Quot.sound`; final direct
audits remain. `SignedInfiniteDeletion`, `SignedZetaTailDeletion`,
`SignedFiniteSpectrum`, `SignedLogSquareWindows`,
`AbsolutePrimeWindowTransfer`, and `SignedPrimeLogSquareWindows` contain
the remaining proof and await successful audits. The infinite norm bound
uses total variation and dominated convergence, not order preservation.
