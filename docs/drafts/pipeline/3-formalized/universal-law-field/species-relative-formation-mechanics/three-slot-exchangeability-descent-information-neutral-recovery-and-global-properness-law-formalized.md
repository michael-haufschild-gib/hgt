# ULF-SRFM-6 — Lean formalization record

**Card:** `three-slot-exchangeability-descent-information-neutral-recovery-and-global-properness-law.md`

**Modules** (namespace `GaloisForLFunctions.HTGeometry`), both imported by
`GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.HTGeometry.UniversalLawField`:

| Module | Content |
|---|---|
| `ConstitutiveExchangeableFormationSelection.lean` | the reporter/tensor layer: §3 and the reporter form of §5 |
| `ThreeSlotExchangeabilityInformation.lean` | the measure/information layer: §2, §4, §5, §6 |
| `PoissonIntensityMarkingIsometry.lean` | supplies `klDiv_prod`, `klDiv_pi` |

## Card result → Lean declaration

| Card result | Lean declaration |
|---|---|
| `α`, `β`, (EFD.2) | `slotAlpha`, `slotBeta` |
| **Theorem 2.1**, (EFD.4) | `klDiv_slotAlpha_slotBeta` |
| (EFD.4) reflection invariance | `klDiv_slot_reflection` |
| **Corollary 2.2**, (EFD.5) | `klDiv_slot_eq_zero_iff` |
| (EFD.7) two-slot blindness | `twoSlotOrbitSymmetrization_swap` |
| (EFD.9) cylinder masses | `symAlternatingCylinder112`, `symAlternatingCylinder121` |
| **Theorem 3.1**, (EFD.10) | `symAlternatingCylinder_gap`, `symAlternatingCylinder_eq_iff` |
| **Theorem 3.2**, (EFD.10a)–(EFD.10c) | `phaseAveragedAdjacentCoincidence`, `phaseAveragedSkippedCoincidence`, `phaseAveragedSkipped_sub_adjacent`, `phaseAveragedThinningConsistent_iff`, `phaseAveragedThinningConsistent_iff_laws_eq` |
| **Theorem 3.3**, (EFD.10d)–(EFD.10e) | `formationThinningTensorFactorization` |
| (EFD.10f) | `formationThinningReporterDefect_eq_sq` |
| **Corollary 3.4**, (EFD.10g)–(EFD.10h) | `formationThinningReporterDefect_nonneg`, `formationThinningReporterDefect_eq_zero_iff` |
| **Theorem 4.1**, (EFD.11) | `klDiv_slot_recovery` |
| `𝒲_m`, (EFD.13) | `slotWork` |
| **Theorem 5.1**, (EFD.14) | `slotWork_eq`, `slotWork_add` |
| **(EFD.15)** | `slotWork_bddAbove_iff` |
| **§6**, (EFD.17) | `slotWork_bddAbove_iff_neutral` |
| **(EFD.18)** logistic example | `logisticPhase`, `logisticPhase_eq_iff` |
| finite-reporter global properness | `finiteExchangeWork_bounded_iff`, `exchangeableFormationSelection_capstone` |

## Method notes

* `(EFD.4)` is two applications of `klDiv_prod` (additivity of relative entropy over independent
  products) together with `klDiv_self`; it needs **no** finiteness, positivity, or full-support
  hypothesis and holds for arbitrary probability measures on an arbitrary measurable space.
* `(EFD.11)` is exactly mathlib's `klDiv_compProd_left`: the common recovery kernel is the same on
  both sides, so the conditional term of the chain rule vanishes identically.
* `(EFD.14)` is `klDiv_pi` (relative entropy is additive over finite independent packets, proved
  here by `Fin`-induction through `measurePreserving_piFinSuccAbove` and `klDiv_prod`).
* `(EFD.15)` is proved in `ℝ≥0∞` without any auxiliary hypothesis: a bound `C ≠ ⊤` on every depth
  forces `J.toReal = 0` by Archimedes, hence `klDiv P Q = 0`, hence `P = Q`.

## Verification

* `lake env lean` on both modules: 0 errors, 0 warnings.
* Axiom audit: `ThreeSlotExchangeabilityInformation` (10) and
  `ConstitutiveExchangeableFormationSelection` (22) public declarations — only `propext`,
  `Classical.choice`, `Quot.sound`.
