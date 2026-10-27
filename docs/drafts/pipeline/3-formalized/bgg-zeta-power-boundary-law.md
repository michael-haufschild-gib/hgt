# The density form of the boundary law for powers of ζ

- **ID:** bgg-c12
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `(F, Λ) ∈ CompletedPositiveSystem κ d` with `−F'/F = Σ b(n)n^{−s}`, `b ≥ 0`, and let the
  deficit `D(s) = Σ (dΛ(n) − b(n))⁺ n^{−s}` have zero Abel density at `s = 1`: `(σ − 1) D(σ) → 0` as `σ ↓ 1`.
  Then `d ≤ κ` and `2 Σ_{t∈Z} ord_{1+it}Λ ≤ κ − d` for every finite set `Z` of positive heights; for
  `κ ≤ d + 1`, `Λ(1 + it) ≠ 0` for `t ≠ 0`. More generally the same holds for `−F'/F + dζ'/ζ = 𝓛ν + E`
  with `ν ≥ 0`, `E` holomorphic on `Re s > 1` and `(σ − 1)E(σ + it) → 0` for every `t`.

## Paper proof
Landau–Wronskian principle for `Λ(s(s−1))^{d−κ}` against `(s(s−1))^{κ−d}(2ξ)^d` with `σ_E = 1`: an abscissa
`c > 1` would be a real zero of the base beyond `1`, impossible, so `c ≤ 1`. The relation holds on
`Re s > 1` with integrable kernel; the perturbation is Abel-negligible on `Re s = 1` (`|D(σ + it)| ≤ D(σ)`).
The Abel–Gram law at `x₀ = 1` makes the jump `t ↦ ord_{1+it} base − ord_{1+it}Λ'` even positive definite:
its value at `0` is `≥ 0`, which for `κ < d` contradicts `ord_1 base = 0 < ord_1 Λ'`; and the line
capacity, with the base nonvanishing on `Re s = 1` off `1` (`ζ(1 + it) ≠ 0`), gives
`2Σ ord ≤ ord_1 base − ord_1 Λ' ≤ κ − d`.

## Lean
`TheBoundaryCapacityOfDeformationsOfPowersOfZeta.lean`: `zetaPowDeformation_boundary_law`,
`abscissaOfAbsConv_relDeficit_vonMangoldt_le_one`, `latticeMember_boundary_law`,
`latticeMember_ne_zero_on_boundary`; `zetaPowDeformation_boundary_capacity`,
`latticeMember_boundary_capacity` are corollaries. Generalized Abel lemmas in
`StrongMultiplicityOneBelowTheSquareRootDeficit.lean` (`tendsto_sub_mul_LSeries_of_residue_zero`,
`tendsto_residue_zero_of_abscissa_lt` at any `x₀`). Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
