# Large-parameter exterior geometry: Green sublevels and the filled Julia set avoid the unit disk

- **ID:** green-sublevel-exterior-geometry
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** GBExt-clause probe of the tower certificate (library-backlog ticket
  `2026-07-02-towerdata-u0-gb-clause.md`, Updates 4–5).
- **Statement:** For `‖b‖ ≥ 4`: (i) `filledJulia b ⊆ {|z| > 1}`; (ii) if
  `exp(4t) + 4 ≤ (‖b‖−1)² − ‖b‖` then the Green sublevel `{G_b < t} ⊆ {|z| > 1}`; (iii) every
  `TowerSection b rlo rhi` with `1 < rlo`, `rhi⁴ + 4 ≤ (‖b‖−1)² − ‖b‖` maps into `{|z| > 1}`.

## Goal

Places the ENTIRE tower geometry of a large parameter inside `u₀`'s domain (natural boundary
`|z| = 1`): the geometric obstruction to the `u₀`-extension (`GBExt`) clause of the tower
certificate is empty at large `‖b‖`, so `u₀` restricts to section images and Green-band extension
domains directly.  Consumed by the Green-band tower consumer (`U0GreenBandBridge`).

## Lean surface

- `U0PhiLargeCarrier.filledJulia_exterior`; `U0SectionExterior.green_sublevel_exterior`,
  `tower_section_image_exterior`, `tower_section_image_subset_Ext`.
- Card: `FullyProvenNewTargets.green_sublevel_exterior_card`.
- Files: `formal/GaloisForLFunctions/U0/U0PhiLargeCarrier.lean`, `U0SectionExterior.lean`.

## Proof shape

A point of the closed unit disk reaches modulus `≥ (‖b‖−1)² − ‖b‖` in two quadratic steps.
There `‖φ_b‖ = exp(G_b)` (`norm_bottcherCoord_eq_exp_green_escape`) with
`‖φ_b − id‖ ≤ 4‖b‖/‖·‖` (`norm_bottcherCoord_sub_id_le`) forces
`G_b ≥ ¼ log((‖b‖−1)² − ‖b‖ − 4)` at the point itself (Green doubling
`greenFunctionDyn_iterate`).  Small Green level therefore implies modulus `> 1`; the filled
Julia set is the `G = 0` case, and section images sit at levels `< log rhi` (`TowerSection.level`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (proof carried directly in Lean)
- [x] 2 → 3  formalized: axiom set `[propext, Classical.choice, Quot.sound]`; build + lint green
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — proven as the pullAn/GBExt probe outcome; consumer theorems banked same day.
