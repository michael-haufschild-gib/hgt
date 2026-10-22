# CCM unit-Riesz Markov density

- **ID:** `ccm-unit-riesz-markov-density`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM, finite positivity core
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/ccm-unit-riesz-markov-virial-landau-law.md`

## Formal theorem surface

Module:

`GaloisForLFunctions/RHTower/CCM/CCMUnitRieszMarkovDensity.lean`

It proves unconditionally:

1. the prefix inequality
   `2m sqrt(m+1) <= 3 sum_(r=1)^m sqrt(r)`;
2. the exact derivative of each logarithmic unit-Riesz cell profile;
3. nonnegativity of that derivative on its physical cell;
4. exact gluing of adjacent cells and the base value `W(1)=0`;
5. global floor-assembled logarithmic profile and its exact reduction on every physical cell.

Principal declarations:

- `unitRieszSqrtPrefixMass_lower`;
- `hasDerivAt_unitRieszCellProfile`;
- `unitRieszCellMarkovDensity_nonneg`.
- `unitRieszCellProfile_succ_eq_at_boundary`;
- `unitRieszCellProfile_one_zero`.
- `unitRieszLogProfile_eq_cell`;
- `unitRieszLogProfile_zero`.

These theorems certify the arithmetic positivity engine behind the paper-level conclusion that
`d(v)=d/dv W(exp(v))` is a probability density.  Global absolute continuity, its zeta Laplace
transform, Markov--virial convolution, and one-sided Landau connector are not claimed formalized.

## Gates

- [x] square-root prefix law
- [x] cell derivative formula
- [x] physical-cell positivity
- [x] adjacent-cell gluing
- [x] base endpoint
- [x] global floor-assembled profile
- [ ] formalize global piecewise profile and probability mass one
- [ ] formalize zeta Laplace transform
- [ ] formalize one-sided Laplace Landau connector
- [ ] prove source-specific virial lower bound
- [ ] RH
