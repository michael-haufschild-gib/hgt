# Coalitional attainment, universal escape, and reciprocal pricing law — Lean record

- **ID:** ULF-CAM-1
- **Stage:** 3-formalized
- **Status:** [LEAN-CERTIFIED] [ROUTE-INDEPENDENT MECHANISM] [NOT RH]
- **Paper card:**
  `2-fully-proven/universal-law-field/coalitional-attainment-mechanics/coalitional-attainment-universal-escape-and-reciprocal-pricing-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCoalitionalAttainment`

## Certified mechanism

Lean certifies a countable Banach-valued law of formation versus escape:

1. an actual positive carrier exists exactly when finite positive coalitions approach zero defect
   without losing tightness;
2. tightness is equivalent to bounded expectation of some proper source price;
3. every exact carrier has a tight normalized finite-prefix approximation;
4. without an actual carrier, every zero-residual history diverges under every proper source price;
5. a reciprocal separator gives the quantitative residual-times-resource lower bound;
6. the scalar family `a i = 1/(i+1)` with Dirac coalitions realizes sharp escape.

This is a mechanism theorem. It neither supplies source-specific law atoms nor selects an RH route.

## Significant declarations

- `CoalitionalProbabilityVector`
- `CoalitionalUniformlyTight`
- `CoalitionalProperPrice`
- `coalitional_tight_attainment`
- `coalitional_price_bounded_attainment`
- `coalitional_no_carrier_universal_escape`
- `coalitional_tightness_constructs_proper_price`
- `coalitional_exact_carrier_has_tight_finite_approximation`
- `coalitional_attainment_iff_tight_finite_approximation`
- `coalitional_attainment_iff_proper_priced_finite_approximation`
- `coalitional_reciprocal_pricing`
- `coalitional_banach_reciprocal_pricing_div`
- `coalitional_escapeRule_has_no_carrier`
- `coalitional_sharp_escape_countermodel`

## Verification

Direct foreground elaboration:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCoalitionalAttainment.lean
```

The module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`. Axiom prints on the
two equivalence theorems, Banach universal escape, reciprocal pricing, and sharp countermodel
report only standard Mathlib foundations. Formal lint reports no forbidden declaration in the
module. Final umbrella build is recorded after certification audit.
