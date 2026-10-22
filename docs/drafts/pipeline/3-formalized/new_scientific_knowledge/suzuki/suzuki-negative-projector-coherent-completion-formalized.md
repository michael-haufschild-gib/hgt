# Suzuki coherent completion is the weighted negative spectral projector — Lean certificate

- **ID:** `suzuki-negative-projector-coherent-completion-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-negative-projector-coherent-completion.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiNegativeProjectorCoherentCompletion.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiNegativeProjectorCoherentCompletion`:

```text
RHTower.abs_suzukiInverseDefect_eq_weight
RHTower.eq_negPart_of_minimal_commutingCompletion
RHTower.gram_add_negPart_eq_posPart
RHTower.gram_defect_add_negPart_nonneg
RHTower.gram_negPart_nonneg
RHTower.gram_re_nonneg_of_nonneg
RHTower.inner_eq_inner_sqrt
RHTower.inner_negPart_eq_inner_sqrt
RHTower.isLeast_commutingCompletion_unique
RHTower.negPart_cfc
RHTower.negPart_isLeast_commutingCompletions
RHTower.negPart_le_of_add_nonneg
RHTower.negPart_le_of_cfc_add_nonneg
RHTower.negPart_mem_commutingCompletions
RHTower.negPart_suzukiInverseDefect
RHTower.posPart_cfc
RHTower.posPart_suzukiInverseDefect
RHTower.suzukiCommutingCompletions
RHTower.suzukiInverseDefectOperator_eq_product
RHTower.suzukiInverseDefect_add_negPart
RHTower.suzukiInverseDefect_add_negPart_nonneg
RHTower.suzukiInverseDefect_add_nonneg_iff
RHTower.suzukiInverseDefect_add_two_negPart
RHTower.suzukiInverseDefect_negPart_nonneg
RHTower.suzukiInverseDefect_posPart_nonneg
RHTower.suzukiInverseDefect_posPart_sub_negPart
RHTower.suzukiInverseKreinDefect_eq_product
RHTower.suzukiInverseKreinDefect_inv
RHTower.suzukiInverseKreinWeight_eq_abs
RHTower.suzukiInverseShiftFactor
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 30 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
