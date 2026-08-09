# Minimal exchange strictification and universal commuting observer -- Lean certification

- **ID:** ULF-OPM-2
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/minimal-exchange-strictification-and-universal-commuting-observer-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveExchangeStrictification`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [MECHANISM THEOREM] [NOT RH]

## Certified declarations

- `ExchangeSeed`, `exchangeLawFamily`, `ExchangeCongruence`;
- `exchangeCongruence_equivalence`;
- `exchangeCongruence_contains`;
- `exchangeCongruence_preserves_left`, `exchangeCongruence_preserves_right`;
- `exchangeCongruence_least`;
- `exchangeSetoid`, `ExchangeQuotient`, `exchangeQuotientMap`;
- `exchangeQuotientLeft`, `exchangeQuotientRight` and their quotient-map equations;
- `exchangeQuotient_commute`;
- `exchangeCongruence_subset_observerKernel_of_commuting_descents`;
- `exchangeObserverFactor`, its quotient equation, uniqueness, and both intertwining laws;
- `no_strictly_smaller_exchange_strictification`;
- `constitutiveExchangeStrictificationMechanism_closed`.

## Exact content

For two arbitrary unary laws, Lean constructs the least equivalence containing every critical pair
`f (g x) ~ g (f x)` and preserved by both laws. The induced quotient laws commute. Every observer
carrying commuting descents annihilates the full generated congruence and factors uniquely through
the quotient. Any strictly smaller equivalence fails at least one of preservation, executability, or
commutation.

This certifies an obstruction-promotion mechanism, not a route endpoint: failed exchange generates
the universal least strict repair.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveExchangeStrictification.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveExchangeStrictification
```

Both pass. A `/tmp` axiom audit prints:

```text
exchangeCongruence_least: [propext]
exchangeQuotient_commute: [propext, Quot.sound]
exchangeCongruence_subset_observerKernel_of_commuting_descents: [propext]
exchangeObserverFactor_unique: [propext, Quot.sound]
no_strictly_smaller_exchange_strictification: [propext]
constitutiveExchangeStrictificationMechanism_closed: [propext, Quot.sound]
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computational certificate is used.
