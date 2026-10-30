# Weighted affine shell errors vanish in harmonic norm

- **ID:** weighted-affine-shell-errors-vanish-in-harmonic-norm
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Fix `c>0`, `m≥1`, a nonzero compact `C²` unit profile `φ`, and any fixed
shell shifts `b_h∈ℕ`. Let `A_b(X,n)` be the literal reciprocal-weighted
prime-power shell correction, with argument `kn+b_h`, and let
`κ_b=2/(Mϕ(m)) Σ_{1≤h<c} c_m(b_h)∫_{h/c}¹G(u)/u du`, where
`G=φ⋆φ` and `M=∫φ²`. Then

`Σ_{1≤n≤N} |A_b(N/n,n)−c_m(n)κ_b|²/n = o(log N)`.

The same holds for the explicit tilted spline. For negative offsets take
`b_h=mh−h`; then `c_m(b_h)=c_m(h)` and `κ_b=shellCorrection(φ,c,m)`.
This is a norm extension of the weighted source theorem, not an identification
of the literal logarithmic upward row or a separately counted contribution.

## Proof [PROVED HERE]

The uniform affine-shell theorem applies to every `n,b_h`; the finite shell
sum gives `R(X,n)=A_b(X,n)−c_m(n)κ_b→0` uniformly in `n`.
For bounded `X`, `|G|≤M`, `|c_m|≤ϕ(m)`, and nonnegativity of `Λ(k)/k`
bound the finite source by `2ϕ(m)·#{h}·Σ_{k≤X}Λ(k)/k`. Together with the
uniform limit this bounds `R` on all real `X` and all `n`.

Thus `F(Y)=sup_{X≥Y,n}|R(X,n)|` is finite and tends to zero. Since
`⌊N/n⌋≤N/n`, the row error is at most `F(⌊N/n⌋)/√n`.
`HTGeometry.tendsto_harmonicQuotient_square_error` makes its squared sum,
divided by `log N`, tend to zero. Taking square roots gives the normalized
Euclidean norm limit.

For every `d|m`, `d|(mh−h)` iff `d|h`; the divisor formula proves the
reflected coefficient identity. If `h≤T`, the same formula and congruence
modulo `m` give `c_m(T−h)=c_m(T+mh−h)`. All analytic inputs are already
proved for the weighted source; no prime-distribution premise is added.

## Lean

`CriticalArithmeticCorrelationTheory/TheWeightedAffineShellErrorsVanishInHarmonicNorm.lean`:

- `tendsto_shiftedReciprocalUpwardRowError_sq_div_log`;
- `tendsto_normalizedShiftedReciprocalUpwardResidual_norm`;
- `tendsto_tiltedUnitSpline_shiftedReciprocalResidual_norm`;
- `ramanujanLagCoefficient_sub_eq_reflected`;
- `shellCorrectionOfShift_reflected`.

Final direct no-olean check passed without warnings. Both norm theorems and
both reflection identities have only `propext`, `Classical.choice`, and
`Quot.sound`. CACT umbrella import added. No separate contribution count.
