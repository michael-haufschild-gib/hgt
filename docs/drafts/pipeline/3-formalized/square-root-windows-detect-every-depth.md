# Square-root windows detect every zero depth

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/SquareRootWindowsDetectEveryDepth.lean`.

## Statement

Let `Z` be a tempered zero configuration without real zeros and
`f_Z(u)=2 Re lagStructure Z (boxSpline 1 3) u`.
Fix `α≥0`, `r>0`, and `K∈ℝ`. If arbitrarily late centers `T` satisfy

`f_Z(u)≥-K exp(αu)` for every `|u-T|≤r√T`,

then every `ρ∈Z` satisfies `Re ρ≤1/2+α`. Neither attainment of the
greatest depth nor a zero-count asymptotic is required.

## Proof

Suppose `ρ₀` is deeper than `α`. The spline coefficient at
`z₀=ρ₀-1/2` is nonzero. Write the normalized trace `exp(-αu)f_Z(u)`
as its absolutely convergent exponential series with exponents `z-α`.
Their real parts lie in `[-D,D]`, where `D=1/2+|α|`.

Temperedness gives inverse-square ordinate summability. Positive
three-point filters with shifts `π/Im ρ` therefore annihilate a cofinite
spectral tail while preserving `z₀-α`, with total square cost below
`V₀=r²/(16(D+1))`. The surviving coefficients form a finite,
conjugation-symmetric spectrum. Its greatest real part `β` exceeds `α`,
and no surviving mode has zero frequency.

Finite-spectrum oscillation supplies constants `B,η>0` and, for every
sufficiently late `T`, a point `t∈[T,T+B]` where the filtered normalized
trace is below `-η exp((β-α)t)`.

At an observed center, the radius-`r√T/2` window about this `t` lies inside
the observed window once `T` is large. Positive averaging of its lower
bound gives a filtered value at least

`-|K|-2A exp(DB+D²V₀-T)`, where `A=Σ_z |evenCoeff Z spline z|`.

The error tends to zero, contradicting the growing negative excursion.

## Certificates

- `exists_configuration_tail_deletion`
- `finite_spectrum_dense_negative`
- `infinite_tail_squareRoot_floor`
- `configuration_re_le_of_squareRoot_windows`
- `zeta_re_le_of_squareRoot_windows`

Lean checks pass; transitive axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. This detects depths from local
trace bounds; it does not produce the arithmetic bound in B130.
