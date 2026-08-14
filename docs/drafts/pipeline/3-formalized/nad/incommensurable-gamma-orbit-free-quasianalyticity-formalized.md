# Incommensurable Gamma orbit-free quasianalyticity — formalized

- **ID:** `incommensurable-gamma-orbit-free-quasianalyticity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `incommensurable-gamma-orbit-free-quasianalyticity.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/FiniteCommutingShiftPeeling.lean` | **`shiftWord_dichotomy`** — the many-shift rational-or-hypertranscendental dichotomy, peeled from the one-shift input by commuting-shift induction |
| `HTGeometry/GammaPhaseCompletion.lean` | **`alienCharge_shiftWord_classification`** — the scaled alien-character branch classification, the card's exact DA/HT dichotomy |

Both resolve; `#print axioms` reports no axioms at all for the two capstones (the surrounding
supporting lemmas report only `propext`, `Classical.choice`, `Quot.sound`).

## Audited declarations

- `HTGeometry.shiftWord_dichotomy` — *no axioms*;
- `HTGeometry.alienCharge_shiftWord_classification` — *no axioms*.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

## Boundary

The Adamczewski--Dreyfus--Hardouin one-shift theorem (JAMS 2021) and the scaled-Borel residue
computation enter as **explicit named theorem inputs**, exactly as the card's gate line records
("named ADH and scaled-Borel parents are explicit theorem inputs").  They are not postulated as
axioms and no `sorry`, `admit`, `opaque` or `unsafe` declaration is used.  The card's only remaining
gate is the external parent-literature and priority audit.
