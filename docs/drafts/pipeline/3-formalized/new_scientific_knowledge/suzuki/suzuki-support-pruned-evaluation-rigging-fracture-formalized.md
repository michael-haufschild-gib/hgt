# The Suzuki seam Hilbert carrier cannot have bounded physical evaluation — Lean certificate

- **ID:** `suzuki-support-pruned-evaluation-rigging-fracture-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-support-pruned-evaluation-rigging-fracture.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SuzukiSupportPrunedEvaluationRiggingFracture.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.SuzukiSupportPrunedEvaluationRiggingFracture`:

```text
GaloisForLFunctions.RHTower.no_bounded_suzukiSeamHilbert_phaseEvaluation
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 1 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- construct completed-domain `ell1` carrier state
- prove exact scalar evaluation/intertwining through the rigging
- apply Gamma wall and weighted-tail coercivity in the middle `ell2` space
- prove raw Evans injectivity
- RH

These are research frontier items, not formalization debt.
