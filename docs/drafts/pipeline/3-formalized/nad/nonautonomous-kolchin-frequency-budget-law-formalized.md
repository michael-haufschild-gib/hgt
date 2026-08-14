# Nonautonomous Kolchin frequency-budget law — formalized

- **ID:** `nonautonomous-kolchin-frequency-budget-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `nonautonomous-kolchin-frequency-budget-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/ArithmeticComplementRank.lean` | `finrank_le_arithmeticComplement_add` — the exact coefficient/state rank conservation `(20)` from a short exact sequence of rational vector spaces |
| `HTGeometry/KolchinFrequencyBudgetPhase.lean` | the coefficient/state split, the relative-capacity bound, the prime-complement budget, the Gamma-coefficient half-rank floor, and `primeApertureCharacterModule_finrank` discharging the abstract prime premise at `V = ⊤` |
| **`HTGeometry/PrimePhaseBudgetRank.lean`** | `primeLog_primesBelow_linearIndependent_rat` (`rank_ℚ Λ_N = π′(N)`), `primeCounting_le_finrank_of_primeLog_mem`, `primeCounting_le_rank_of_primeLog_mem`, and **`primeCounting_le_of_realAutonomousAnnihilator_of_primeLog_mem`** — the genuine prime-complement budget: prime logs below `N` in the Bohr frequency module plus an order-`n` autonomous ADE force `π′(N) ≤ n`; contrapositive `not_realAutonomousAnnihilator_of_primeLog_mem` |
| `HTGeometry/BohrFrequencyRankLaw.lean` | the frequency-rank law consumed above |
| `HTGeometry/BohrHullDual.lean`, `BohrHullDimension.lean`, `BohrModuleTheorem.lean`, `CoveringDimension.lean` | hull duality, hull covering dimension, the module theorem, inverse-limit covering dimension |

## What closed last

The card's audit had recorded that its `SingularKolchinFrequencyInput` is a numerical structure
carrying no analysis, and that the Bohr-hull / Pontryagin / inverse-limit substrate was absent.  The
second claim was wrong: the corpus carries seventy-plus Bohr modules, including hull duality
(`exists_frequency_of_hull_character`), the module theorem (`rank_closure_bohrSpectrum_eq`), the
hull covering dimension (`hasCoverDimLE_bohrHull_of_injection`) and the frequency-rank law
(`rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator`), all unconditional and
axiom-clean.  With the prime side upgraded from `ℤ`- to `ℚ`-independence, the budget inequality is
now a genuine analytic theorem rather than an arithmetic restatement.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

Every declaration resolves and `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`.

## Boundary

The card's remaining gate is the external cross-literature priority audit.  The Ritt--Kolchin
analytic parents beyond the frequency-rank law remain cited classical inputs, exposed explicitly and
never as axioms.
