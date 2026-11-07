# A parabolic core for the theta current

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization in progress)
- **Statement:** For `0<a≤1/2` and `|b|≤6`, `current(a,b) ≥ (a/300)(1-b²/36)²`.
- **Lean target:** `ThetaCuspSections/ParabolicCurrentCore.lean`, `current_ge_parabolic`.

## Proof [PROVED HERE]

The existing source second-moment bound and `poleSharpConstant≤0.0466` give
`∫₀∞ x²Φ(x) dx ≤ Ξ(0)/36`. Integrate `cos(bx)≥1-b²x²/2` against positive `Φ` to obtain
`Ξ(b)≥Ξ(0)(1-b²/36)`. On `|b|≤6`, the factor is nonnegative; `Ξ(0)≥49/100` gives the claimed parabolic minorant for Ξ.

For a zero with displacement δ and ordinate γ, compare its reflected logarithmic-derivative pair with `(a/3) Re[1/(ρ(1-ρ))]`. On-line zeros use `γ²>41/2`, `|b-γ|≤|γ|+6`, and `a≤1/2`. An off-line zero has `|γ|>67`; hence `|b-γ|>61`, and the exact paired rational expression gives the same lower bound. Summing and using `poleSharpConstant≥0.0456` yields `Re ξ'/ξ(1/2+a+ib)≥0.0076a`.

Verified height 67 makes the current nonnegative throughout the aperture segment at every `|b|≤6`. Thus `|Ξ(b-ia)|²≥Ξ(b)²`. The current identity gives
`current(a,b)≥2·0.0076·(49/100)²·a(1-b²/36)²`, whose coefficient exceeds `1/300`.

For degree-eleven `p`, the general Legendre kernel applied to `(1-b²/36)p(b)` retains this weighted energy. The resulting complete-source rank-twelve payment is formalized in `TheTwelfthSectionFromHeightSixtySeven`.
