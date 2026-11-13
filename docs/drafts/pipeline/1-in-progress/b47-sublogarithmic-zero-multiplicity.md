# Sublogarithmic multiplicity of zeta zeros

- **ID:** b47-sublogarithmic-zero-multiplicity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1311/route-obstacles.md`, S4, B47; exact target in `docs/reports/review-0611/obstacles-summary.md`, B47.
- **Statement:** For every `ε > 0`, eventually every critical zeta zero `ρ = 1/2 + iγ` satisfies `m(ρ) ≤ ε log |γ|`, unconditionally, from an input not reducible to size bounds. The same assertion for all nontrivial zeros is a stronger target.

## Proven inputs and open step

- `SquareRootThreshold.mult_le_log_zeta` gives `m(ρ) ≤ 40 log(180 |Im ρ|)`.
- `NodalGeometryOfTheDeBruijnFlow.exists_mult_le_log` gives critical multiplicity `≤ (3300/9991 + ε) log X`. Its frequency estimate comes from energy doubling and size bounds at a fixed positive horizon; it does not make the coefficient tend to zero.
- `ConjugateDiagonalGeometry.exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect` gives `H(γ) ≤ C log|γ|/loglog|γ| + 4 Eγ((1/4)loglog|γ|)`, where `H` counts the entire horizontal fibre. The all-height estimate `Eγ((1/4)loglog|γ|) = o(log|γ|)` is not supplied.
- `PrimeTorusTheory.NonAlignmentAtEveryLargeHeight` controls finite-word multiplicity and prime phases. No implication from large zeta multiplicity to the forbidden alignment has been identified.

## Gates

- [x] Exact target and existing bounds identified.
- [ ] Independent all-height arithmetic or geometric input proved.
- [ ] Dependency-closed proof of the displayed zeta statement.
- [ ] Lean formalization, module check, transitive axiom audit.
