# Boundary damping recovers the exceptional divisor

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let every zero copy outside finite `F` have real part at most `θ<σ`, with
`½<σ<Re ρ<1` and `ξ(ρ)=0`. At angle `φ(t)=−π/2+1/t`, every `a>0` and
every eventually positive `h(t)→0` give

`A_h^rot(t)/(h(t)^d Kφ(exp(−at),ρ−σ−it))`
`→ −mρ(ρ−1)Π_{q∈F,ρq≠ρ}(ρ−ρq) ≠ 0`,

where `d=1+#{q∈F:ρq≠ρ}` and `mρ` is the actual analytic multiplicity.
There is no fixed positive speed threshold and no contraction-rate restriction.
Failure of AAL supplies the actual finite packet and all geometric inputs.

For `h(t)=exp(−κt)`, `κ>0`, the literal prime filter's norm tends to infinity
whenever `dκ<a(Re ρ−σ)/2`. This removes the earlier fixed `π/4` Gamma loss.
Independently, the literal prime filter tends to zero if `σ<1`, `a>0` and
`dκ>a(1−σ)/2`, without an exceptional-layer hypothesis.

## Proof

Choose `σ<c<Re ρ` avoiding the finite packet's real parts. The rotated
weight is an entire exponential multiplier of the positive-strip Mellin
weight. The weighted residue identity cancels the pole and every unwanted
zero exactly. No Gamma pole is crossed. For each interior angle, the sharp
Gamma strip bound leaves decay `exp(−(π/4−|φ|/2)|v|)`, so both horizontal
edges vanish.

The complete regular-line integral retains `h^d`. Its angular dependence
is a weighted kernel moment, bounded polynomially at `φ(t)`. Consequently

`|A_h^rot(t)+mρ P_h(exp(h(ρ−β)))Kφ(exp(−at),ρ−σ−it)|`
`≤ C h^d t^N exp(at(c−σ)/2)`.

The reciprocal selected mode is at most
`D t^M exp(−a(Re ρ−σ)t/2)`. Normalization cancels `h^d` exactly and leaves
`CD t^(N+M) exp(−a(Re ρ−c)t/2)→0`. The finite product of exponential
differences supplies the displayed nonzero limit. Applying the same mode
bound to exponential contraction proves raw growth. The independent Euler
bound proves decay above the arithmetic threshold.

## Lean proof

`ExceptionalLayerTheory/RotatedContoursForFiniteDivisorFilters.lean` proves
the exact rectangle and line-shift identities and the complete boundary
remainder, including
`exists_boundaryPrimeDampingFilter_spacing_preserving_error_bound`.

`ExceptionalLayerTheory/BoundaryDampingReadsTheDivisor.lean` proves
`boundary_contracting_prime_filter_reads_selected_zero`,
`not_asymptoticAbscissaLaw_has_boundary_contracting_prime_filters`,
`not_asymptoticAbscissaLaw_has_boundary_prime_growth`, and
`tendsto_boundary_prime_filter_zero_of_fast_contraction`.

Both direct source audits pass without warnings. All twelve printed
transitive dependency lists contain only `propext`, `Classical.choice`,
and `Quot.sound`. Both modules are imported by the exceptional-layer umbrella.

## Remaining gap

The independent decay and exceptional growth ranges remain separated by
`a(1−Re ρ)/2>0`. No B13 contradiction or zero exclusion follows.
