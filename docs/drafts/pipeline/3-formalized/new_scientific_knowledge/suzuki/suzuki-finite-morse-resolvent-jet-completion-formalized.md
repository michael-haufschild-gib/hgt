# Suzuki finite-Morse resolvent-jet completion — Lean certificate

- **ID:** `suzuki-finite-morse-resolvent-jet-completion-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-finite-morse-resolvent-jet-completion.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CfcEigenvector.lean`
- `formal/GaloisForLFunctions/HTGeometry/CompactOperatorDiscreteSpectrum.lean`
- `formal/GaloisForLFunctions/HTGeometry/ResolventFamilyJet.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteMorseEigenspaceBlock.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteMorseInterpolantUniqueness.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteMorseResolventJetCompletion.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteMorseResolventOperatorLift.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiNegativeProjectorCoherentCompletion.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.CfcEigenvector`:

```text
GaloisForLFunctions.HTGeometry.cfc_apply_eigenvector
```

`GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum`:

```text
GaloisForLFunctions.HTGeometry.countable_setOf_hasEigenvalue
GaloisForLFunctions.HTGeometry.countable_spectrum_of_isCompactOperator
GaloisForLFunctions.HTGeometry.finite_setOf_hasEigenvalue_norm_ge
GaloisForLFunctions.HTGeometry.finite_setOf_mem_spectrum_norm_ge
GaloisForLFunctions.HTGeometry.inner_eq_zero_of_hasEigenvector_of_ne
```

`GaloisForLFunctions.HTGeometry.ResolventFamilyJet`:

```text
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.continuousAt
GaloisForLFunctions.HTGeometry.IsResolventFamilyOn.hasDerivAt
GaloisForLFunctions.HTGeometry.aeval_eq_resolventShiftJet_sum
GaloisForLFunctions.HTGeometry.hasDerivAt_resolventShiftJet
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMorseEigenspaceBlock`:

```text
RHTower.negPart_cfc_apply_of_eigenvector
RHTower.suzukiFiniteMorse_completion_apply_negativeEigenvector_eq_zero
RHTower.suzukiFiniteMorse_jetSquare_eq_negPart_on_negativeEigenvector
RHTower.suzukiFiniteMorse_jetSquare_eq_neg_kreinDefect_on_negativeEigenvector
RHTower.suzukiFiniteMorse_kreinDefect_apply_positiveEigenvector
RHTower.suzukiResolventJetSquare_gram_nonneg
RHTower.suzukiResolventJetSquare_inner_eq
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMorseInterpolantUniqueness`:

```text
RHTower.suzukiFiniteMorseInterpolant_natDegree_le
RHTower.suzukiFiniteMorseInterpolant_unique
RHTower.suzukiFiniteMorseKreinInterpolant_unique
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMorseResolventJetCompletion`:

```text
RHTower.suzukiFiniteMorseInterpolant_eval
RHTower.suzukiFiniteMorseKreinDiagonalForm_nonneg
RHTower.suzukiFiniteMorseKreinInterpolant_exact_negativeDebt
RHTower.suzukiFiniteResolventPolynomial_exactProjector_impossible
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMorseResolventOperatorLift`:

```text
RHTower.aeval_apply_of_eigenvector
RHTower.exists_eigenvector_of_mem_spectrum_real
RHTower.finite_setOf_mem_real_spectrum_abs_ge
RHTower.finite_setOf_negativeLevel_of_isCompactOperator
RHTower.isCompactOperator_suzukiFiniteMorseInterpolant
RHTower.isCompactOperator_suzukiResolventJet
RHTower.pow_apply_of_eigenvector
RHTower.suzukiFiniteMorseInterpolant_eq_resolventShiftJetSum
RHTower.suzukiFiniteMorse_completedWeight_eq_zero
RHTower.suzukiFiniteMorse_kreinResolventWeight_pos
RHTower.suzukiFiniteMorse_operatorCompletion_nonneg
RHTower.suzukiFiniteMorse_operatorCompletion_nonneg_of_eigenvectors
RHTower.suzukiFiniteMorse_operatorCompletion_re_inner_nonneg
RHTower.suzukiKreinResolventWeight_resolventNode
RHTower.suzukiKreinResolventWeight_zero
RHTower.suzukiOperatorCompletion_nonneg_iff
RHTower.suzukiOperatorResolventJetSquare_exactProjector_impossible
RHTower.suzukiResolventJetSquare_apply_of_eigenvector
RHTower.suzukiResolventJetSquare_nonneg
RHTower.suzukiResolventJet_isSelfAdjoint
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiNegativeProjectorCoherentCompletion`:

```text
RHTower.gram_re_nonneg_of_nonneg
RHTower.negPart_cfc
RHTower.negPart_operatorKreinDefect_le_jetSquare
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 47 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 → 4 publication-ready: standalone paper + external priority audit

These are research frontier items, not formalization debt.
