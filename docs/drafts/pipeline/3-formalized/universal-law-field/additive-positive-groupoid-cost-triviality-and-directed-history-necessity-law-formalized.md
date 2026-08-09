# Reversible-phase / irreversible-cost polarization — Lean certification

- **ID:** ULF-HISTORY-1
- **Paper card:**
  `additive-positive-groupoid-cost-triviality-and-directed-history-necessity-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveHistoryPolarization`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### `constitutiveGroupoid_nonnegativeAdditiveCost_eq_zero`

Every nonnegative additive real cost on every reversible history groupoid vanishes identically.

### `constitutiveGroupoid_complexWeight_nonnegativeRealPart_eq_zero`

The nonnegative real part of an additive complex groupoid weight vanishes identically.

### `constitutiveDirectedHistory_nontrivialAdditiveCost_exists`

The directed natural-number history monoid carries a nonzero nonnegative additive cost, closing the
positive survivor rather than stopping at a no-go.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveHistoryPolarization.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveHistoryPolarization
```

Targeted build completed successfully. `#print axioms` reports only standard logical quotient/choice
principles for groupoid results and only `propext` for directed survivor. Module is imported by
dedicated universal-law-field umbrella. No project postulate or computation proof is used.

## Exact field consequence

Any universal history field must polarize reversible memory from irreversible cost. One additive
complex weight on a groupoid cannot unify both; nontrivial positive action requires directed,
subadditive, or otherwise noninvertible history structure.
