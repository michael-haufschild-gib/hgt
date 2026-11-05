# Explicit Jensen real-rootedness horizons

- **ID:** explicit-jensen-real-rootedness-horizons
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** review-0511, A18.

## Target

Define a finite expression `N(d)` and prove that every actual ξ Jensen
polynomial of degree `d` and shift `n≥N(d)` splits over `ℝ`.
The bound may use the finite algebraic root set of the degree-`d` Hermite
polynomial; it must not choose a threshold from qualitative convergence.

## Explicit constants

Write `Q(s)=s(π exp(2s)−9/4)` and `Q(s_n)=n+1/2`. Let

`c₀=1`, `cₚ₊₁=6(2p+1)cₚ`,

`Dₚ=12e²(2p+1)cₚ+8e²(2p+1)cₚ₊₁+cₚ₊₂`,

`F_d=1+3Σ_{p<d}Dₚ`.

For `R≥1`, define the Hermite value bounds
`B₀=1`, `B₁=R`, `Bⱼ₊₂=R Bⱼ₊₁+(j+1)Bⱼ`, and error constants

`C₀=1`, `C₁=2R+1`,

`Cⱼ₊₂=(2R+2(j+1)+1)Cⱼ₊₁+(j+1)Cⱼ+2(j+1)Bⱼ₊₁+(j+1)Bⱼ₊₂`.

Let `Z` be the distinct roots of the degree-`d` probabilists' Hermite polynomial
`H_d`, and put

`ε=(1+Σ_{z∈Z}Σ_{w∈Z\{z}}4/|z−w|)⁻¹`,

`R=1+Σ_{z∈Z}(|z−ε|+|z+ε|)`,

`m=(1+Σ_{z∈Z}(|H_d(z−ε)|⁻¹+|H_d(z+ε)|⁻¹))⁻¹`,

`S=2+F_d+4F_d(C_d(R)+1)²/m²`,

`N(d)=max(ceil(Q(S)),4(d+1))`.

Only finite sums, recurrences, algebraic roots, exponentials and a ceiling enter.

## Proof

1. `exp(2s)≥(s+1)²` and `π>3` give `Q(s)≥s³` for `s≥2`.
   Thus `s_n²/(n+1/2)≤1/s_n`. The existing local Ward inequality and
   uniform centered-moment bounds imply `U(n,p+1)≤Dₚ/s_n` when
   `n≥4(p+2)`. The full-source comparison factor is at most
   `2(1+1/300)<3`. Cauchy–Schwarz therefore bounds each fluctuation
   moment error through degree `d` by `η=sqrt(F_d/s_n)`. Also
   `δ_n≤η`; if `s_n≥F_d`, then `η≤1`.
2. Induct on the exact mixed Laguerre recurrence. At degrees zero and one,
   the errors are at most `η` and `(2R+1)η`. At step `j+2`, multiply
   the error by `1+(j+1)δ_n²≥1`. The three previous error terms have
   coefficients bounded by `R+2(j+1)`, `R+1`, and `j+1`.
   The coefficient perturbation costs `2(j+1)Bⱼ₊₁η`; the denominator
   perturbation costs `(j+1)Bⱼ₊₂η`. The shifted target moment is zero.
   This is exactly the recurrence for `C`, giving error `≤C_d(R)η`.
3. Each pairwise reciprocal summand gives `2ε<|z−w|`. In the monic
   factorization of `H_d`, the target factor changes sign between `z−ε`
   and `z+ε`; every other factor has positive paired product. These are
   `d` disjoint sign intervals. All endpoint values are nonzero, so `m>0`
   and `m` is at most every endpoint absolute value.
4. `n≥N(d)` and monotonicity of the score give `s_n≥S`. Consequently
   `η≤m/(2(C_d(R)+1))`, so the actual normalized Jensen polynomial
   differs from `H_d` by less than `m/2` at every endpoint. It retains
   all `d` sign changes. The intermediate value theorem and degree bound
   give `d` real roots. Undoing the nonzero affine normalization proves
   that the actual ξ Jensen polynomial splits over `ℝ`.

## Lean status

Formalization in progress in `RHTower/Jensen/`: explicit concentration,
mixed-recurrence errors, finite Hermite sign margins and the actual horizon.
No qualitative convergence threshold is used in the proposed expression.
