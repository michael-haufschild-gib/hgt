# Exchange residual, strict quotient, central promotion, nonsplit history -- Lean certification

- **ID:** ULF-OPM-3
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/exchange-residual-strict-quotient-central-promotion-and-nonsplit-history-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveExchangeCentralPromotion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [CROSS-PROMOTION MECHANISM] [NOT RH]

## Certified declarations

- `ExchangeAbelian`, `exchangeCarry`, `exchangeCarry_cocycle`;
- `heisExchangeProjection`, surjectivity, kernel criterion, central image, and exact-fibre theorem;
- `exchangeGenF`, `exchangeGenG`, strict basis shadows;
- `exchangeGenerators_central_residual` and `exchangeGenerators_strict_shadow_commute`;
- `heis_commutator_formula`, `every_heis_commutator_is_central`;
- `every_center_is_exchange_commutator`, `heis_center_characterization`;
- `lifts_of_exchange_basis_have_fixed_commutator`;
- `lifts_of_exchange_basis_do_not_commute`;
- `no_heisExchangeProjection_group_section`;
- `constitutiveExchangeCentralPromotionMechanism_closed`.

## Exact content

The strict observer `H -> Multiplicative (Z x Z)` erases the central coordinate. The same exchange
failure is retained in `H` by

```text
F * G = center 1 * (G * F).
```

The cross term is an exact normalized two-cocycle, and its cocycle identity is the associativity
law. Every commutator is central; every central integer occurs as an exchange commutator. Every pair
of lifts of the strict basis has commutator `center 1`, so no group-homomorphic section exists.

Thus Lean distinguishes two promotion mechanisms for one residual: strict quotient and nonsplit
central-history retention.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveExchangeCentralPromotion.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveExchangeCentralPromotion
```

Both pass. `/tmp` axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` on the
printed significant declarations. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or
computational certificate is used.
