# Complete scalar persistent gauge reduction — formalization certificate

- **ID:** `complete-scalar-persistent-gauge-reduction`
- **Stage:** 3-formalized
- **Paper proof:**
  `../../../2-fully-proven/new_scientific_knowledge/other/complete-scalar-persistent-gauge-reduction.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/CompleteScalarPersistentGaugeReduction.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`

## Closed formal theorem

For every derivation-compatible endomorphism of the canonical scalar free differential rational
field over an algebraically closed characteristic-zero constant field, Lean proves an exact XOR:

1. the stable range core is the base field; or
2. the core is nontrivial and its induced differential automorphism has one complete gauge branch.

The four branches are exhaustive and pairwise mutually exclusive:

- identity, fixed field equal to the full core, trivial differential Galois group;
- finite multiplicative order `N ≥ 2`, fixed field `C⟨q^N⟩`, radical reconstruction and exact
  `μ_N` differential Galois group;
- infinite multiplicative order, fixed field `C⟨q′/q⟩`, equation `q′=(q′/q)q`, reconstruction and
  exact `G_m` differential Galois group;
- additive translation, fixed field `C⟨q′⟩`, equation `q′=P`, reconstruction and exact `G_a`
  differential Galois group.

Each displayed fixed-field generator is hypertranscendental. The finite branch also records its
explicit rank-one radical differential coefficient and equation. Cross-coordinate multiplicative
versus additive overlap is ruled out by a formal Möbius determinant argument, not by treating the
branches as mere tagged alternatives.

Capstones:

```text
GaloisForLFunctions.HTGeometry.persistentGaugeBranches_mutuallyExclusive
GaloisForLFunctions.HTGeometry.differentialAlgEquiv_completePersistentGaugeClassification
GaloisForLFunctions.HTGeometry.universalProjectiveBoundary_le_fixedField
GaloisForLFunctions.HTGeometry.freeScalar_completePersistentGaugeReduction
```

The universal Schwarzian boundary claim is formalized by
`universalProjectiveBoundary_le_fixedField`: `C⟨S(q)⟩` is hypertranscendental and lies in the exact
cyclic fixed field. Charged clock compatibility is supplied by the existing closed stable-core
theorem `persistent_core_clock_character_dichotomy`, which forces positive-charge action to be
multiplicative.

## Infrastructure added

- `ScalarPersistentGaugeBranchInvariants.lean`: generator rigidity, exact automorphism orders, and
  multiplicative/additive cross-generator disjointness.
- `ScalarRadicalDifferentialEquation.lean`: finite radical coefficient and rank-one equation.
- `JetFieldConstantKernel.lean`: exact constant kernel of finite-rank free jet fields.
- `ScalarDifferentialInversiveCoreProjectiveLaw.lean`: unrestricted Lüroth/stable-core projective
  reduction used by the capstone.

## Verification

- Direct `lake env lean` checks pass for all new leaves and the capstone.
- Targeted final build passes:
  `lake build GaloisForLFunctions.HTGeometry.CompleteScalarPersistentGaugeReduction`.
- Scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for every
  listed capstone.
- Targeted scans find no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Capstone is imported by the `HTGeometry` umbrella; infrastructure is reachable transitively.
- Repository-wide lint reaches unrelated concurrent umbrella gaps; none names this card or its
  modules.
