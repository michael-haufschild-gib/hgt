# Suzuki screw compact-hull and parity law — Lean certificate

- **ID:** `suzuki-screw-compact-hull-parity-law-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-screw-compact-hull-parity-law.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewDistribution.lean`
- `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewHilbert.lean`
- `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewHull.lean`
- `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewRecurrence.lean`
- `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewValue.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCompactHullParityLaw.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.SummableSpectrumScrewDistribution`:

```text
GaloisForLFunctions.HTGeometry.screwHaar_pos_of_isOpen
GaloisForLFunctions.HTGeometry.screwHaar_support
GaloisForLFunctions.HTGeometry.screwHaar_unique
GaloisForLFunctions.HTGeometry.screwValueLaw
GaloisForLFunctions.HTGeometry.screwValueLaw_support
GaloisForLFunctions.HTGeometry.tendsto_timeAverage_screwSeries
```

`GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHilbert`:

```text
GaloisForLFunctions.HTGeometry.screwEmbed
GaloisForLFunctions.HTGeometry.screwEmbed_injective
GaloisForLFunctions.HTGeometry.sq_norm_screwEmbed_screwPhase_sub
GaloisForLFunctions.HTGeometry.sq_norm_screwEmbed_sub
```

`GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHull`:

```text
GaloisForLFunctions.HTGeometry.add_mem_screwHull
GaloisForLFunctions.HTGeometry.existsUnique_screwHaar
GaloisForLFunctions.HTGeometry.isCompact_screwHull
GaloisForLFunctions.HTGeometry.isConnected_screwHull
GaloisForLFunctions.HTGeometry.neg_mem_screwHull
GaloisForLFunctions.HTGeometry.screwHaar
GaloisForLFunctions.HTGeometry.screwHaar_fourier
GaloisForLFunctions.HTGeometry.screwHaar_map_add_self
GaloisForLFunctions.HTGeometry.screwHullSubgroup
GaloisForLFunctions.HTGeometry.screwHull_eq_screwAnnihilator
GaloisForLFunctions.HTGeometry.sub_mem_screwHull
```

`GaloisForLFunctions.HTGeometry.SummableSpectrumScrewRecurrence`:

```text
GaloisForLFunctions.HTGeometry.closure_screwPhase_image_Ici
GaloisForLFunctions.HTGeometry.closure_screwSeries_image_Ici
GaloisForLFunctions.HTGeometry.exists_window_screwPhase_mem_of_isOpen
GaloisForLFunctions.HTGeometry.exists_window_screwSeries_eq
GaloisForLFunctions.HTGeometry.exists_window_screwSeries_near
GaloisForLFunctions.HTGeometry.neg_mem_screwForwardHull
GaloisForLFunctions.HTGeometry.screwSeries_liminf_eq_zero
GaloisForLFunctions.HTGeometry.screwSeries_limsup_eq_screwHullMax
```

`GaloisForLFunctions.HTGeometry.SummableSpectrumScrewValue`:

```text
GaloisForLFunctions.HTGeometry.infiniteTorusFourier_screwAntipode
GaloisForLFunctions.HTGeometry.parity_of_screwRelationLattice_trivial
GaloisForLFunctions.HTGeometry.screwAntipode_mem_screwAnnihilator_iff
GaloisForLFunctions.HTGeometry.screwHullMax_eq_two_mul_tsum_iff
GaloisForLFunctions.HTGeometry.screwValue_image_screwHull
```

`GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCompactHullParityLaw`:

```text
RHTower.closure_suzukiScrewFunction_image_Ici
RHTower.exists_window_suzukiScrewFunction_eq
RHTower.exists_window_suzukiScrewFunction_near
RHTower.sq_norm_suzukiScrewEmbed_sub
RHTower.suzukiScrewFunction_law_support
RHTower.suzukiScrewFunction_liminf_eq_zero
RHTower.suzukiScrewFunction_limsup_eq
RHTower.suzukiScrewFunction_limsup_eq_absolute_bound_iff
RHTower.tendsto_timeAverage_suzukiScrewFunction
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 43 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- manuscript completed
- independent specialist novelty review

These are research frontier items, not formalization debt.
