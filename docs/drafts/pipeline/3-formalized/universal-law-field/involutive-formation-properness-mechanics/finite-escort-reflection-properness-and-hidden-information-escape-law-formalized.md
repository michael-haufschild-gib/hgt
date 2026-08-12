# Finite escort reflection properness and hidden-information escape — Lean certificate

- **Paper theorem:** ULF-IFPM-1
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFiniteEscortFormationProperness`
- **Status:** `[LEAN-PROVED] [NO SORRY] [NO ADDED AXIOMS] [UMBRELLA-WIRED]`

## Formal theorem surface

- `hasDerivAt_finiteTiltMean`
- `finiteTiltVariance_nonneg`
- `finiteTiltVariance_pos`
- `finiteTiltMean_monotone`
- `finiteTiltMean_strictMono`
- `finiteTiltKLReal_eq`
- `finiteTiltJeffreysReal_eq`
- `finiteTiltJeffreysReal_reflection_eq`
- `finiteTiltJeffreysReflection_bounded_iff_score_constant`
- `finiteTiltJeffreysReflection_linear_lower`
- `finiteEscortHiddenLoss_linear_lower`
- `finiteEscortHiddenLoss_unbounded_of_nonconstant`

The capstones prove two global formation laws.  Complete reflected amplification has uniformly
bounded Jeffreys work exactly when the score is constant.  For a nonconstant score, every observer
with uniformly bounded reported work forces an unbounded complementary hidden-information loss.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFiniteEscortFormationProperness.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFiniteEscortFormationProperness
lake env lean /tmp/finite_escort_axioms.lean
```

Axiom audit reports only mathlib foundations:

```text
propext
Classical.choice
Quot.sound
```

Scoped scan contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
