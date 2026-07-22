# CCM unit-Riesz Markov density

- **ID:** `ccm-unit-riesz-markov-density`
- **Stage:** 3-formalized/new_scientific_knowledge
- **Type:** THEOREM, finite positivity core
- **Scientific status:** `[FORMALIZED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Paper parent:**
  `../../2-fully-proven/new_scientific_knowledge/ccm-unit-riesz-markov-virial-landau-law.md`

## Formal theorem surface

Module:

`GaloisForLFunctions/RHTower/CCMUnitRieszMarkovDensity.lean`

It proves unconditionally:

1. the prefix inequality
   `2m sqrt(m+1) <= 3 sum_(r=1)^m sqrt(r)`;
2. the exact derivative of each logarithmic unit-Riesz cell profile;
3. nonnegativity of that derivative on its physical cell.

Principal declarations:

- `unitRieszSqrtPrefixMass_lower`;
- `hasDerivAt_unitRieszCellProfile`;
- `unitRieszCellMarkovDensity_nonneg`.

These theorems certify the arithmetic positivity engine behind the paper-level conclusion that
`d(v)=d/dv W(exp(v))` is a probability density.  Global absolute continuity, its zeta Laplace
transform, Markov--virial convolution, and one-sided Landau connector are not claimed formalized.

## Gates

- [x] square-root prefix law
- [x] cell derivative formula
- [x] physical-cell positivity
- [ ] formalize global piecewise profile and probability mass one
- [ ] formalize zeta Laplace transform
- [ ] formalize one-sided Laplace Landau connector
- [ ] prove source-specific virial lower bound
- [ ] RH

